------------------ MODULE 5_vending_machine_datastructure ------------------
EXTENDS Naturals, TLC


VARIABLE
    products,
    cointypes,
    wallet

Init ==
            /\ products = [saffron_sky |-> 150, desert_white |-> 175, ocean_blue |-> 100]
            /\ cointypes = {25,50,100}
            /\ wallet = CHOOSE f \in [cointypes -> 0..4] : \A coin \in cointypes : f[coin] = 1

Next ==
            /\ PrintT (products)
            /\ PrintT (cointypes)
            /\ PrintT (wallet)
                                        
=============================================================================
\* Modification History
\* Last modified Tue May 17 08:13:54 CEST 2022 by dirk-janswagerman
\* Created Tue May 17 07:57:40 CEST 2022 by dirk-janswagerman
