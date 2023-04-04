----------------- MODULE 99_mc_pickplace -----------------

EXTENDS 99_pickplace, TLC

ConstComponentTypes == {"Resistor", "Conductor", "IC"}
ConstBoardIds == {"b1", "b2","b3", "b4"}
ConstRobotIds== {"r1", "r2","r3", "r4"}
ConstBoardPositions ==  {
                            [x |-> 0, y |-> 0],
                            [x |-> 0, y |-> 1],
                            [x |-> 1, y |-> 0],
                            [x |-> 1, y |-> 1]
                        }
ConstComponentIds ==    {
                        [c1 |-> "Resistor"], 
                        [c2 |-> "IC"]
                        }

ConstBoardState ==  {"Unprocessed", "Processing", "Processed"}

ConstMaxX == 2
ConstMaxY == 2

(* Function to count non-empty positions for all boards *)
NonEmptyPositions(x) ==
    LET CountNonEmpty(board) ==
            Cardinality({position \in BoardPositions: board.positions[position] /= Null})
        nonEmptyCounts == {CountNonEmpty(board) : board \in x.boards}
    IN
    SumSeq(SetToSeq(nonEmptyCounts, <<>>))
    
CountBoards(x) ==
    IF x \in
        [
            boards: SUBSET  [
                                id: BoardIds,
                                state: BoardState,
                                positions: [BoardPositions -> ComponentIds \cup {Null}]
                            ],
            boardrecipe:    [
                                BoardIds -> STRING
                            ] \cup { [b \in BoardIds |-> ""] }
        ]
        THEN 
            Cardinality(x.boards)
    ELSE 0


InvariantNonEmpty ==
    NonEmptyPositions (environment) < 5

InvariantConstantNumberOfBoards ==
    CountBoards (environment) + CountBoards (system) =  Cardinality (ConstBoardIds) 

====
