----------------- MODULE 99_robot -----------------
(* Recursive function to compute the sum of elements in a sequence *)

EXTENDS Integers, Sequences, FiniteSets, TLC


(* Action to place a component at a specific position on a board *)
PlaceComponent(boardId, componentId, position) ==
    /\ boardId \in BoardIds
    /\ componentId \in ComponentIds
    /\ position \in BoardPositions
    /\ environment.boards[boardId].positions[position] = Null
    /\ environment' = [environment EXCEPT !.boards[boardId].positions[position] = componentId]

====
