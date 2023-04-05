----------------- MODULE 999_playground -----------------

EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT ComponentType, RecordType, ComplexRecordType

VARIABLE 
    queue, count_x, count_y

TypeInvariant ==
    /\ queue \in Seq (ComplexRecordType)

Init ==
/\    queue = <<>>
/\    count_x = 0
/\    count_y = 0
     

Add (q) ==
    /\ Len (q) < 5
    /\ q' = Append (queue, [component |-> "resistor", position |-> [x |-> count_x, y |-> count_y]])
    /\ UNCHANGED (<<count_x, count_y>>)

Next ==
    \/ Add (queue)
    \/
        /\ count_x' = count_x + 1
        /\ UNCHANGED (<<queue, count_y>>)
    \/
        /\ count_y' = count_x + 1
        /\ UNCHANGED (<<queue, count_y>>)

====