----------------- MODULE 05_vending_machine_datastructure_2 -----------------
EXTENDS Naturals, TLC

CONSTANT customer_names, vending_machine_names, min_coin_stock, max_coin_stock, min_product_stock, max_product_stock, products, cointypes

VARIABLE
    customers,
    vending_machines
    
vars == <<customers, vending_machines>>

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
                                        
=============================================================================
\* Modification History
\* Last modified Tue May 17 08:09:36 CEST 2022 by dirk-janswagerman
\* Created Tue May 17 07:57:40 CEST 2022 by dirk-janswagerman


=============================================================================
\* Modification History
\* Created Tue May 17 08:06:17 CEST 2022 by dirk-janswagerman
