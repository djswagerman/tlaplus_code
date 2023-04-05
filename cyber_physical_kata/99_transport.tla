----------------- MODULE 99_transport -----------------
(* Recursive function to compute the sum of elements in a sequence *)

EXTENDS Integers, Sequences, FiniteSets, TLC
MoveBoard(boardId, env, sys) ==
    /\ \E board \in env.boards : board.id = boardId
    /\ LET movedBoard == CHOOSE board \in env.boards : board.id = boardId
         updatedEnvironment == [env EXCEPT !.boards = @ \ {movedBoard}]
         updatedSystem == [sys EXCEPT !.boards = @ \cup {movedBoard}]
     IN
     /\ env' = updatedEnvironment
     /\ sys' = updatedSystem

=====