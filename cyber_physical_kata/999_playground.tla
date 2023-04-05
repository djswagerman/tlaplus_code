----------------- MODULE 999_playground -----------------

EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT ComponentType

VARIABLE 
    recipe1,
    recipe2

Positions == positions = {  
                [x |-> 0, y |-> 0],
                [x |-> 0, y |-> 1]
             }

TypeInvariant ==
    \A r \in recipe1 :
        /\ r.position \in Positions
        /\ r.component \in ComponentType

Init ==
/\    recipe1 = 
        {
            [
                position |-> [x |-> 0, y |-> 0],
                component |-> "resistor"
            ],
            [
                position |-> [x |-> 0, y |-> 1],
                component |-> "IC"
            ]
        }
/\    recipe2 = {}

MoveElement(src, dest, idx) ==
        /\ src' = [i \in DOMAIN src |-> IF i = idx THEN "REMOVED" ELSE src[i]]
        /\ dest' = Append(dest, src[idx])

Next ==
\/ \E r \in recipe1 : MoveElement (recipe1, recipe2, r)

====