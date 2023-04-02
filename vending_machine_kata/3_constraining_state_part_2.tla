-------------------- MODULE 3_constraining_state_part_2 --------------------

EXTENDS Naturals
CONSTANTS
    min_value,
    max_value

VARIABLE
    x
    
Init ==
    /\ x = 0

Next ==
   \/
        /\ x < max_value
        /\ x' = x + 1
   \/
        /\ x > min_value
        /\ x' = x - 1

Spec ==
    Init /\ [][Next]_<<x>>

=============================================================================
\* Modification History
\* Last modified Mon May 16 17:02:39 CEST 2022 by dirk-janswagerman
\* Created Mon May 16 16:52:56 CEST 2022 by dirk-janswagerman
