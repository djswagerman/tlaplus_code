---- MODULE 99_pickplace --------

EXTENDS Integers, Sequences, FiniteSets, TLC, 99_utils, 99_scheduler, 99_feeder, 99_transport

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
    ProductionLocations,
    ProductionLocationQueueType,
    Reels,
    MaxReels

VARIABLES environment, system

Null == ""

ValidBoards (boards) ==
    boards \in SUBSET       [
                                id: BoardIds,
                                state: BoardState,
                                positions: [BoardPositions -> ComponentTypes \cup {Null}]
                            ]

ValidPositions (positions) ==
    \A p \in positions : 
        /\ p.component \in ComponentTypes \cup {Null}

ValidRecipes (recipes) ==
    \A r \in recipes : 
        /\ r.id \in RecipeIds
        /\ ValidPositions (r.positions)


ValidBoardRecipe (boardrecipe) ==
     boardrecipe \in        [
                                BoardIds -> STRING
                            ] \cup { [b \in BoardIds |-> ""] }

ValidReel (reel) ==
    /\ reel.id \in ReelIds
    /\ reel.componentType \in ComponentTypes \cup {Null}
    /\ reel.remainingComponents <= MaxComponents

ValidReels (reels) == 
    \A r \in reels :
        /\ ValidReel (r)

ValidFeeder (feeder) == 
    /\ feeder.id \in FeederIds
    /\ ValidReels (feeder.reels)

ValidFeeders (feeders) == 
    \A f \in feeders : ValidFeeder (f)

ValidQueue (queue) ==
    queue \in Seq (ProductionLocationQueueType)

ValidProductionLocations (production_locations) ==
    \A pl \in production_locations:
        /\ pl.id \in LocationIds
        /\ ValidQueue (pl.queue) 
        /\ ValidFeeders (pl.feeders) 

TypeInvariantSystem (sys) ==
    /\ ValidBoards (sys.boards)
    /\ ValidRecipes (sys.recipes)
    /\ ValidProductionLocations (sys.production_locations)

TypeInvariantEnvironment (env) ==
    /\ ValidBoards (env.boards)
    /\ ValidRecipes (env.recipes)
    /\ ValidReels (env.reels)

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
            recipes |-> Recipes,
            reels |-> Reels
        ]

Next ==
    \* Scheduling
    \/ \E boardId \in BoardIds: SetRecipeForBoard (boardId, environment, system)
    \/ DownloadRecipes (environment, system)

    \* Operator actions
    \/ PlaceReels(environment, system)

    \* Transport
    \/ \E boardId \in BoardIds: MoveBoard(boardId, environment, system)

=====
