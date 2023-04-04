---- MODULE 02_datastructure --------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ComponentTypes, BoardIds, BoardPositions, RobotIds, ComponentIds

VARIABLES environment, system

Null == [c0 |-> ""]

TypeInvariant ==
    /\ environment \in [boards: SUBSET [id: BoardIds, positions: [BoardPositions -> ComponentIds \cup {Null}]]]


Init ==
    /\ system =
        [
            boards |-> {}
        ]
    /\ environment =
        [
            boards |-> {[id |-> b, positions |-> [p \in BoardPositions |-> Null]] : b \in BoardIds}
        ]

MoveBoard(boardId) ==
    /\ \E board \in environment.boards : board.id = boardId
    /\ LET movedBoard == CHOOSE board \in environment.boards : board.id = boardId
         updatedEnvironment == [environment EXCEPT !.boards = @ \ {movedBoard}]
         updatedSystem == [system EXCEPT !.boards = @ \cup {movedBoard}]
     IN
     /\ environment' = updatedEnvironment
     /\ system' = updatedSystem


(* Action to place a component at a specific position on a board *)
PlaceComponent(boardId, componentId, position) ==
    /\ boardId \in BoardIds
    /\ componentId \in ComponentIds
    /\ position \in BoardPositions
    /\ environment.boards[boardId].positions[position] = Null
    /\ environment' = [environment EXCEPT !.boards[boardId].positions[position] = componentId]

Next ==
    \E boardId \in BoardIds: MoveBoard(boardId)

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
    LET CountNonEmpty(board) ==
            Cardinality({position \in BoardPositions: board.positions[position] /= Null})
        nonEmptyCounts == {CountNonEmpty(board) : board \in env.boards}
    IN
    SumSeq(SetToSeq(nonEmptyCounts, <<>>))
    
CountBoards(x) ==
    IF x \in [boards: SUBSET [id: BoardIds, positions: [BoardPositions -> ComponentIds \cup {Null}]]]
    THEN Cardinality(x.boards)
    ELSE 0

=====
