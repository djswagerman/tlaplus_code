----------------- MODULE 99_mc_pickplace -----------------

EXTENDS 99_pickplace, TLC

ConstComponentTypes == {"Resistor", "Capacitor", "Inductor", "Diode", "IC"}
ConstBoardIds == {"b1", "b2","b3", "b4"}
ConstRobotIds== {"r1", "r2","r3", "r4"}
ConstRecipeIds == {"Recipe1", "Recipe2", "Recipe3"}
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
                                [position |-> [x |-> 0, y |-> 1], component |-> "Capacitor"],
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
                                [position |-> [x |-> 1, y |-> 1], component |-> "Capacitor"]
                            }
                        ],
                        [
                            id |-> "Recipe3",
                            positions |-> {
                                [position |-> [x |-> 0, y |-> 0], component |-> ""],
                                [position |-> [x |-> 0, y |-> 1], component |-> "IC"],
                                [position |-> [x |-> 1, y |-> 0], component |-> "Capacitor"],
                                [position |-> [x |-> 1, y |-> 1], component |-> "Resistor"]
                            }
                        ]
                    }

ConstBoardRecipe ==     [
                            x \in {"b1", "b2", "b3"} |-> IF x = "b1" THEN "Recipe3"
                                ELSE IF x = "b2" THEN "Recipe1"
                                ELSE IF x = "b3" THEN "Recipe2"
                                ELSE ""
                        ]

ConstProductionLocations == 
                        {
                            [
                                id |-> 1,
                                feeders |->
                                    {
                                        [
                                            id |-> 1,
                                            reels |->
                                            {
                                                [
                                                    id |-> 1,
                                                    componentType |-> "Resistor",
                                                    remainingComponents |-> 5
                                                ],
                                                [
                                                    id |-> 2,
                                                    componentType |-> "Capacitor",
                                                    remainingComponents |-> 5
                                                ]
                                            }
                                        ],
                                        [
                                            id |-> 2,
                                            reels |->
                                            {
                                                [
                                                    id |-> 1,
                                                    componentType |-> "Inductor",
                                                    remainingComponents |-> 5
                                                ],
                                                [
                                                    id |-> 2,
                                                    componentType |-> "Diode",
                                                    remainingComponents |-> 5
                                                ]
                                            }
                                        ]
                                    }
                            ]
                        }




ConstBoardState ==  {"Unprocessed", "Processing", "Processed"}

ConstLocationIds == {"production location 1", "production_location 2"}

ConstFeederIds == {"f1", "f2"}

ConstReelIds== {"r1", "r2"}


ConstMaxX == 2
ConstMaxY == 2
ConstMaxComponents == 3

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
