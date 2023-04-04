---- MODULE 99_pickplace --------

EXTENDS Integers, Sequences, FiniteSets, TLC, 99_utils

CONSTANT ComponentTypes, BoardIds, BoardPositions, RobotIds, ComponentIds, BoardState

VARIABLES environment, system

Null == [c0 |-> ""]

TypeInvariant ==
    /\ environment \in [boards: SUBSET [id: BoardIds, state: BoardState, positions: [BoardPositions -> ComponentIds \cup {Null}]]]


Init ==
    /\ system =
        [
            boards |-> {}
        ]
    /\ environment =
        [
            boards |->  {
                            [   id |-> b,
                                state |-> "Unprocessed",
                                positions |-> [p \in BoardPositions |-> Null]
                            ] : b \in BoardIds
                        }
        ]

MoveBoard(boardId) ==
    /\ \E board \in environment.boards : board.id = boardId
    /\ LET movedBoard == CHOOSE board \in environment.boards : board.id = boardId
         updatedEnvironment == [environment EXCEPT !.boards = @ \ {movedBoard}]
         updatedSystem == [system EXCEPT !.boards = @ \cup {movedBoard}]
     IN
     /\ environment' = updatedEnvironment
     /\ system' = updatedSystem

Next ==
    \E boardId \in BoardIds: MoveBoard(boardId)

=====
