----------------- MODULE 99_utils -----------------
(* Recursive function to compute the sum of elements in a sequence *)

EXTENDS Integers, Sequences, FiniteSets, TLC

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

====
