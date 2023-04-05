----------------- MODULE 99_mc_pickplace -----------------

EXTENDS 99_pickplace, TLC

ConstComponentTypes == {"Resistor", "Capacitor", "Transistor", "Diode", "IC"}
ConstBoardIds == {"b1", "b2","b3"}
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


ConstProductionLocationQueueType    ==
                            {
                                [
                                    boardId |-> id,
                                    component |-> c,
                                    position |-> p
                                ] : id \in BoardIds, c \in ConstComponentTypes, p \in  {[x |-> a, y |-> b] : a, b \in 0..3}
                            }


ConstProductionLocations == 
                        {
                            [
                                id |-> "pl1",
                                queue |->   <<
                                                [
                                                    boardId |-> "b3",
                                                    component |-> "Resistor",
                                                    position |-> [x |-> 0, y |-> 0]
                                                ]
                                            >>,
                                boardId |-> "",
                                feeders |->
                                    {
                                        [
                                            id |-> "f1",
                                            reels |-> {}
                                        ]
                                    }
                            ],
                            [
                                id |-> "pl2",
                                queue |-> <<>>,
                                boardId |-> "",
                                feeders |->
                                    {
                                        [
                                            id |-> "f2",
                                            reels |-> {}
                                        ]
                                    }
                            ]
                        }




ConstBoardState ==  {"Unprocessed", "Processing", "Processed"}

ConstLocationIds == {"pl1", "pl2"}

ConstFeederIds == {"f1", "f2", "f3"}

ConstReelIds== {"r1", "r2", "r3", "r4"}

ConstReels == 
                        {
                            [
                                id |-> "r1",
                                componentType |-> "Resistor",
                                remainingComponents |-> 5
                            ],
                            [
                                id |-> "r2",
                                componentType |-> "Capacitor",
                                remainingComponents |-> 5
                            ],
                            [
                                id |-> "r3",
                                componentType |-> "Transistor",
                                remainingComponents |-> 5
                            ],
                            [
                                id |-> "r4",
                                componentType |-> "Diode",
                                remainingComponents |-> 5
                            ]
                        }

ConstMaxX == 2
ConstMaxY == 2
ConstMaxComponents == 5
ConstMaxReels == 2

CountBoards(x) ==
    Cardinality(x.boards)

RECURSIVE IterateFeeders(_, _)
IterateFeeders(reelCount, feeders) ==
    IF feeders = {}
    THEN reelCount
    ELSE LET feeder == CHOOSE f \in feeders: TRUE
         IN IterateFeeders(reelCount + Cardinality(feeder.reels), feeders \ {feeder})

RECURSIVE IterateProductionLocations(_, _)
IterateProductionLocations(totalReelCount, pls) ==
    IF pls = {}
    THEN totalReelCount
    ELSE LET pl == CHOOSE p \in pls: TRUE
         IN IterateProductionLocations(totalReelCount + IterateFeeders(0, pl.feeders), pls \ {pl})

TotalReelCount(pls) ==
    IterateProductionLocations(0, pls)

InvariantConstantNumberOfBoards ==
    CountBoards (environment) + CountBoards (system) =  Cardinality (ConstBoardIds) 

InvariantReels == 
    Cardinality (environment.reels) + TotalReelCount (system.production_locations) = Cardinality (ConstReels)


====
