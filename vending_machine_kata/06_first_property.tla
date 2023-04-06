-------------------------- MODULE 06_first_property --------------------------
EXTENDS Naturals, TLC

CONSTANT customer_names, vending_machine_names, min_coin_stock, max_coin_stock, min_product_stock, max_product_stock, products, cointypes

VARIABLE
    customers,
    vending_machines
    
vars == <<customers, vending_machines>>


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

Init == 
                                /\  customers = 
                                        [c \in customer_names |->
                                            [
                                                assets |->
                                                    [
                                                        credit |-> CHOOSE f \in [cointypes -> {d: d \in 0..max_coin_stock}] : \A coin \in cointypes : f[coin] = 0,
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

Next ==
                               /\ PrintT (customers)
                               /\ UNCHANGED <<vars>>
\*                               /\ customers' = [customers EXCEPT !["c1"].assets.credit[50] = 2]
\*                               /\ UNCHANGED <<vending_machines>>
                                        
AssetValueIsConstant ==         []  [   TotalAssetValue (customers, customer_names) + 
                                            TotalAssetValue (vending_machines, vending_machine_names) = 
                                        TotalAssetValue (customers', customer_names) + 
                                            TotalAssetValue (vending_machines', vending_machine_names)]_<<customers, vending_machines>>


=============================================================================
\* Modification History
\* Last modified Tue May 17 08:25:37 CEST 2022 by dirk-janswagerman
\* Created Tue May 17 08:06:17 CEST 2022 by dirk-janswagerman


=============================================================================
\* Modification History
\* Created Tue May 17 08:15:45 CEST 2022 by dirk-janswagerman
