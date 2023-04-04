----------------- MODULE 99_mc_pickplace -----------------

EXTENDS 99_pickplace, TLC

ConstComponentTypes == {"Resistor", "Conductor", "IC"}
ConstBoardIds == {"b1", "b2","b3", "b4"}
ConstRobotIds== {"r1", "r2","r3", "r4"}
ConstRecipeIds == {"recipe1", "recipe2"}
ConstBoardPositions ==  {
                            [x |-> 0, y |-> 0],
                            [x |-> 0, y |-> 1],
                            [x |-> 1, y |-> 0],
                            [x |-> 1, y |-> 1]
                        }

ConstRecipes ==     {
                        [
                            id |-> "Recipe1",
                            positions |-> {
                                [position |-> [x |-> 0, y |-> 0], component |-> "Resistor"],
                                [position |-> [x |-> 0, y |-> 1], component |-> "Conductor"],
                                [position |-> [x |-> 1, y |-> 0], component |-> "IC"],
                                [position |-> [x |-> 1, y |-> 1], component |-> ""]
                            }
                        ],
                        [
                            id |-> "Recipe2",
                            positions |-> {
                                [position |-> [x |-> 0, y |-> 0], component |-> "IC"],
                                [position |-> [x |-> 0, y |-> 1], component |-> ""],
                                [position |-> [x |-> 1, y |-> 0], component |-> "Resistor"],
                                [position |-> [x |-> 1, y |-> 1], component |-> "Conductor"]
                            }
                        ],
                        [
                            id |-> "Recipe3",
                            positions |-> {
                                [position |-> [x |-> 0, y |-> 0], component |-> Null],
                                [position |-> [x |-> 0, y |-> 1], component |-> "IC"],
                                [position |-> [x |-> 1, y |-> 0], component |-> "Conductor"],
                                [position |-> [x |-> 1, y |-> 1], component |-> "Resistor"]
                            }
                        ]
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
    IF x.boards \in SUBSET  [
                                id: BoardIds,
                                state: BoardState,
                                positions: [BoardPositions -> ComponentTypes \cup {Null}]
                            ]
        THEN 
            Cardinality(x.boards)
    ELSE 0


InvariantNonEmpty ==
    NonEmptyPositions (environment) < 5

InvariantConstantNumberOfBoards ==
    CountBoards (environment) + CountBoards (system) =  Cardinality (ConstBoardIds) 

====
