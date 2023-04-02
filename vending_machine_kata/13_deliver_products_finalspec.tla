------------------- MODULE 13_deliver_products_finalspec -------------------

EXTENDS Naturals, TLC

CONSTANT customer_names, vending_machine_names, min_coin_stock, max_coin_stock, min_product_stock, max_product_stock, products, cointypes, customer_cash

VARIABLE
    customers,
    vending_machines,
    state,
    selected_product
    
vars == <<customers, vending_machines, state>>


CoinValue (f, coin) ==
                                f[coin] * coin

ProductValue (p, prd) ==
                                p [prd] * products [prd]


RECURSIVE SumWallet(_, _)
SumWallet(w, cs) ==             IF cs = {} THEN 0
                                ELSE CoinValue (w, CHOOSE coin \in cs :TRUE) + SumWallet (w, cs \ {CHOOSE coin \in cs :TRUE})

RECURSIVE SumProduct(_, _)
SumProduct(w, prd) ==           IF prd = {} THEN 0
                                ELSE ProductValue (w, CHOOSE p \in prd :TRUE) + SumProduct (w, prd \ {CHOOSE p \in prd :TRUE})

AssetValue (asset_collection, actor) ==
                                SumWallet (asset_collection[actor].assets.credit, cointypes) +
                                SumWallet (asset_collection[actor].assets.bank, cointypes) +
                                    SumProduct (asset_collection[actor].assets.product, DOMAIN products)

RECURSIVE TotalAssetValue(_, _)
TotalAssetValue (asset_collection, actors) ==
                                IF actors = {} THEN 0
                                ELSE AssetValue (asset_collection, CHOOSE actor \in actors : TRUE) + 
                                        TotalAssetValue (asset_collection, actors \ {CHOOSE actor \in actors : TRUE})

CountCoins (asset_collection, actor, coin) ==
                                asset_collection[actor].assets.credit[coin] +
                                asset_collection[actor].assets.bank[coin]

RECURSIVE TotalCoins(_, _, _)
TotalCoins (asset_collection, actors, coin) ==
                                IF actors = {} THEN 0
                                ELSE CountCoins (asset_collection, CHOOSE actor \in actors : TRUE, coin) + 
                                        TotalCoins (asset_collection, actors \ {CHOOSE actor \in actors : TRUE}, coin)

InsertCoin (vending_machine_name, coin) == 
                                vending_machines' = [vending_machines EXCEPT ![vending_machine_name].assets.credit[coin] = @ + 1]

ExchangeCoin (source_collection, target_collection, source, target, coin) ==
                                /\ source_collection[source].assets.credit [coin] > 0
                                /\ target_collection[target].assets.credit [coin] < max_coin_stock
                                /\ source_collection' = [source_collection EXCEPT ![source].assets.credit[coin] = @ - 1]
                                /\ target_collection' = [target_collection EXCEPT ![target].assets.credit[coin] = @ + 1]
                            

InsertCredit (customer_name, vending_machine_name) ==
                                /\ state =  "operational"
                                /\ \E coin \in cointypes : ExchangeCoin (customers, vending_machines, customer_name, vending_machine_name, coin)
                                /\ UNCHANGED <<state, selected_product>>


ReturnCredit (customer_name, vending_machine_name) ==
                                \/
                                    /\ SumWallet (vending_machines[vending_machine_name].assets.credit, cointypes) > 0
                                    /\ \E coin \in cointypes : ExchangeCoin (vending_machines, customers, vending_machine_name, customer_name, coin)
                                    /\ state' =  "returning_credit"
                                    /\ UNCHANGED <<selected_product>>
                                \/
                                    /\ SumWallet (vending_machines[vending_machine_name].assets.credit, cointypes) = 0
                                    /\ state = "returning_credit"
                                    /\ state' =  "operational"
                                    /\ UNCHANGED <<customers, vending_machines, selected_product>>

Init == 
                                /\  customers = 
                                        [c \in customer_names |->
                                            [
                                                assets |->
                                                    [
                                                        credit |-> CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] : \A coin \in cointypes : SumWallet (f, cointypes) = customer_cash /\ f[50] >= 2 /\ f[25] >= 2,
                                                        bank |-> CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] : \A coin \in cointypes : f[coin] = 0,
                                                        product |-> CHOOSE p \in [DOMAIN products -> {d: d \in 0..max_product_stock}] : \A product_name \in DOMAIN products : p[product_name] = 0
                                                    ]
                                            ]
                                        ]
                                /\  vending_machines = 
                                        [v \in vending_machine_names |->
                                            [
                                                assets |->
                                                    [
                                                        credit |-> CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] : \A coin \in cointypes : f[coin] = 0,
                                                        bank |-> CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] : \A coin \in cointypes : f[coin] = 0,
                                                        product |-> CHOOSE p \in [DOMAIN products -> {d: d \in 0..max_product_stock}] : \A pr \in DOMAIN products : p[pr] = 2
                                                    ]
                                            ]
                                        ]
                                /\ state = "operational"
                                /\ selected_product = ""

SelectProduct (customer_name, vending_machine_name, product) ==
                                    selected_product' = product
                                    /\ UNCHANGED <<customers, vending_machines, state>>

ProductAvailable (vending_machine_name, product) ==
                                /\ vending_machines[vending_machine_name].assets.product[product] > 0


CustomerCanPay (customer_name, vending_machine_name, product) ==
                                /\ SumWallet (vending_machines[vending_machine_name].assets.credit, cointypes) >= products[product]

CanReturnExchange (customer_name, vending_machine_name, product) ==
                                /\ \E f \in [cointypes -> {d: d \in 0..max_coin_stock}] : 
                                    /\ SumWallet (f, cointypes) = products[product]                        
                                     /\ \A coin \in cointypes : f[coin] <= vending_machines[vending_machine_name].assets.credit[coin]

SubstractWallet (wallet1, wallet2) ==
                                CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] :
                                    \A coin \in cointypes : f[coin] = wallet2[coin] - wallet1[coin]

AddWallet (wallet1, wallet2) ==
                                CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] :
                                    \A coin \in cointypes : f[coin] = wallet2[coin] + wallet1[coin]

PickCoinSet (wallet, price) ==
                                CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] :
                                    /\ SumWallet (f, cointypes) = price
                                    /\ \A coin \in cointypes : f[coin] <= wallet[coin]


DeliverProduct (customer_name, vending_machine_name, product) ==
                                /\ product # ""
\*                                /\ ProductAvailable (vending_machine_name, product)
                                /\ CustomerCanPay (customer_name, vending_machine_name, product)
                                /\ CanReturnExchange (customer_name, vending_machine_name, product)
                                /\ vending_machines' =  [[[   vending_machines
                                                                EXCEPT ![vending_machine_name].assets.credit = 
                                                                        SubstractWallet (PickCoinSet (vending_machines[vending_machine_name].assets.credit, products[product]), vending_machines[vending_machine_name].assets.credit)
                                                        ]
                                                                EXCEPT ![vending_machine_name].assets.bank = 
                                                                        AddWallet (PickCoinSet (vending_machines[vending_machine_name].assets.credit, products[product]), vending_machines[vending_machine_name].assets.bank)
                                                        ]
                                                                EXCEPT ![vending_machine_name].assets.product[product] = @ - 1
                                                        ]
                                /\ customers' =     [   customers
                                                            EXCEPT ![customer_name].assets.product[product] = @ + 1
                                                    ]
                                /\ product' = ""
                                /\ UNCHANGED <<state>>
                                

Transaction (customer_name, vending_machine_name, product) ==
                                \/ InsertCredit (customer_name, vending_machine_name)
                                \/ ReturnCredit (customer_name, vending_machine_name)
                                \/ SelectProduct (customer_name, vending_machine_name, product)
                                \/ DeliverProduct (customer_name, vending_machine_name, selected_product)


Next ==
                                \/ \E customer_name \in customer_names, vending_machine_name \in vending_machine_names, coin \in cointypes, product \in DOMAIN products : Transaction (customer_name, vending_machine_name, product)

                                   
                                    
NoNegativeStock ==              
                                \A p \in DOMAIN products, v \in vending_machine_names : vending_machines [v].assets.product[p] >= 0
 
AssetValueIsConstant ==         []  [   TotalAssetValue (customers, customer_names) + 
                                            TotalAssetValue (vending_machines, vending_machine_names) = 
                                        TotalAssetValue (customers', customer_names) + 
                                            TotalAssetValue (vending_machines', vending_machine_names)]_<<customers, vending_machines>>

TotalCoinsIsConstant ==         []  [   \A coin \in cointypes :
                                                        TotalCoins (customers, customer_names, coin) +  
                                                            TotalCoins (vending_machines, vending_machine_names, coin) =
                                                        TotalCoins (customers', customer_names, coin) +  
                                                            TotalCoins (vending_machines', vending_machine_names, coin) 
                                    ]_<<customers, vending_machines>>
                                        

=============================================================================
\* Modification History
\* Last modified Tue May 17 16:01:56 CEST 2022 by dirk-janswagerman
\* Created Tue May 17 08:06:17 CEST 2022 by dirk-janswagerman


=============================================================================
\* Modification History
\* Created Tue May 17 08:15:45 CEST 2022 by dirk-janswagerman
