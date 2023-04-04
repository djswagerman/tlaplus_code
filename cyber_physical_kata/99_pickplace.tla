---- MODULE 99_pickplace --------

EXTENDS Integers, Sequences, FiniteSets, TLC, 99_utils

CONSTANT
    ComponentTypes,
    BoardIds,
    BoardPositions,
    RobotIds,
    BoardState,
    RecipeIds,
    Recipes,
    BoardRecipe,
    LocationIds,
    FeederIds,
    ReelIds,
    MaxComponents,
    ProductionLocations

VARIABLES environment, system

Null == ""

ValidBoards (boards) ==
    boards \in SUBSET       [
                                id: BoardIds,
                                state: BoardState,
                                positions: [BoardPositions -> ComponentTypes \cup {Null}]
                            ]

ValidRecipes (recipes) ==
    recipes \in SUBSET      [
                                id: RecipeIds,
                                positions:
                                        [
                                            SUBSET
                                            {
                                                [   position |-> p,
                                                    component |-> c
                                                ] : p \in BoardPositions, c \in ComponentTypes \cup {Null}
                                            } -> ComponentTypes \cup {Null}
                                        ]
                            ]

ValidBoardRecipe (boardrecipe) ==
     boardrecipe \in        [
                                BoardIds -> STRING
                            ] \cup { [b \in BoardIds |-> ""] }

ValidProductionLocations (production_locations) ==
    production_locations \in SUBSET
                            [
                                id: LocationIds,
                                feeders:
                                [
                                    id : FeederIds,
                                    reels:
                                        SUBSET
                                        {
                                            [
                                                id : ReelIds,
                                                componentType : ComponentTypes,
                                                remainingComponents : MaxComponents
                                            ]
                                        }
                                ]
                            ]

TypeInvariantSystem (sys) ==
    /\ ValidBoards (sys.boards)
    /\ ValidRecipes (sys.recipes)
    /\ ValidProductionLocations (sys.production_locations)

TypeInvariantEnvironment (env) ==
    /\ ValidBoards (env.boards)
    /\ ValidRecipes (env.recipes)

TypeInvariant ==
    /\ TypeInvariantEnvironment (environment)
    /\ TypeInvariantSystem (system)

Init ==
    /\ system =
        [
            boards |-> {},
            boardrecipe |-> [b \in BoardIds |-> ""],
            recipes |-> {},
            production_locations |-> ProductionLocations
        ]
    /\ environment =
        [
            boards |->  {
                            [   id |-> b,
                                state |-> "Unprocessed",
                                positions |-> [p \in BoardPositions |-> Null]
                            ] : b \in BoardIds
                        },
            boardrecipe |-> BoardRecipe,
            recipes |-> Recipes
        ]

GetPositionsForRecipe(x, rid) ==
    LET selectedRecipe == CHOOSE r \in x.recipes : r.id = rid
    IN selectedRecipe.positions
    
MoveBoard(boardId) ==
    /\ \E board \in environment.boards : board.id = boardId
    /\ LET movedBoard == CHOOSE board \in environment.boards : board.id = boardId
         updatedEnvironment == [environment EXCEPT !.boards = @ \ {movedBoard}]
         updatedSystem == [system EXCEPT !.boards = @ \cup {movedBoard}]
     IN
     /\ environment' = updatedEnvironment
     /\ system' = updatedSystem

Next ==
    \/ \E boardId \in BoardIds: MoveBoard(boardId)

=====
