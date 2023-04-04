----------------- MODULE 01_datastructure -----------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ComponentTypes, BoardIds, BoardPositions, RobotIds, ComponentIds

VARIABLES environment

Null == 0  \* Null is defined as a value not in ComponentIds

Board == [
  id: Nat,
  positions: SUBSET [x: Nat, y: Nat, type: ComponentTypes]
]

TypeInvariant ==
    /\ environment \in [BoardIds -> [positions: [BoardPositions -> ComponentIds \cup {Null}]]]

Init ==
    environment = [b \in BoardIds |-> [positions |-> [p \in BoardPositions |-> Null]]]

(* Action to place a component at a specific position on a board *)
PlaceComponent(boardId, componentId, position) ==
    /\ boardId \in BoardIds
    /\ componentId \in ComponentIds
    /\ position \in BoardPositions
    /\ environment[boardId].positions[position] = Null
    /\ environment' = [environment EXCEPT ![boardId].positions[position] = componentId]

Next ==
    \E boardId \in BoardIds, componentId \in ComponentIds, position \in BoardPositions:
        PlaceComponent(boardId, componentId, position)

(* Recursive function to compute the sum of elements in a sequence *)
RECURSIVE SumSeq(_)
SumSeq(seq) ==
    IF Len(seq) = 0 THEN 0
    ELSE IF Len(seq) = 1 THEN Head(seq)
    ELSE Head(seq) + SumSeq(Tail(seq))

(* Helper operator to convert a set to a sequence *)
RECURSIVE SetToSeq(_, _)
SetToSeq(S, seq) ==
    IF S = {} THEN seq
    ELSE LET elem == CHOOSE x \in S: TRUE
         IN SetToSeq(S \ {elem}, Append(seq, elem))

(* Function to count non-empty positions for all boards *)
NonEmptyPositions(env) ==
    LET CountNonEmpty(boardId) ==
            Cardinality({position \in BoardPositions: env[boardId].positions[position] /= Null})
        nonEmptyCounts == {CountNonEmpty(boardId) : boardId \in BoardIds}
    IN
    SumSeq(SetToSeq(nonEmptyCounts, <<>>))

=====