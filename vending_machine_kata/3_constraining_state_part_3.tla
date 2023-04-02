-------------------- MODULE 3_constraining_state_part_3 --------------------
EXTENDS Naturals
CONSTANTS
    min_value,
    max_value

VARIABLE
    x
    
Increment (v) ==
    /\ v < max_value
    /\ v' = v + 1

Decrement (v) ==
    /\ v > min_value
    /\ v' = v - 1
    
Init ==
    /\ x = 0

Next ==
   \/ Increment (x)
   \/ Decrement (x)

Spec ==
    Init /\ [][Next]_<<x>>

=============================================================================
\* Modification History
\* Last modified Mon May 16 17:01:23 CEST 2022 by dirk-janswagerman
\* Created Mon May 16 17:00:43 CEST 2022 by dirk-janswagerman
