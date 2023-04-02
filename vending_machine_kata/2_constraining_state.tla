------------------------ MODULE 2_constraining_state ------------------------
EXTENDS Naturals

VARIABLE
    x
    
    
Init ==
    /\ x = 0

Next ==
    /\ x' = x + 1

\* This spec does not terminate.
Spec ==
    Init /\ [][Next]_<<x>>

=============================================================================
\* Modification History
\* Last modified Mon May 16 20:55:36 CEST 2022 by dirk-janswagerman
\* Created Mon May 16 16:49:49 CEST 2022 by dirk-janswagerman
