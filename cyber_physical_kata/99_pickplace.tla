---- MODULE 99_pickplace --------

EXTENDS Integers, Sequences, FiniteSets, TLC, 99_utils

CONSTANT ComponentTypes, BoardIds, BoardPositions, RobotIds, BoardState, RecipeIds, Recipes, BoardRecipe, LocationIds, FeederIds, ReelIds

VARIABLES environment, system

Null == ""

TypeInvariant ==
    /\ environment \in
        [
            boards: SUBSET  [
                                id: BoardIds,
                                state: BoardState,
                                positions: [BoardPositions -> ComponentTypes \cup {Null}]
                            ],
            boardrecipe:    [
                                BoardIds -> STRING
                            ] \cup { [b \in BoardIds |-> ""] },
            recipes: SUBSET [
                                id: RecipeIds,
                                positions: [SUBSET {[position |-> p, component |-> c] : p \in BoardPositions, c \in ComponentTypes \cup {Null}} -> ComponentTypes \cup {Null}]
                            ],
            production_locations: SUBSET
                            [
                                id: LocationIds,
                                feeders:
                                [
                                    SUBSET
                                    [
                                        id: FeederIds,
                                        reels: STRING
                                    ] -> FeederIds
                                ]
                            ]
        ]


Init ==
    /\ system =
        [
            boards |-> {},
            boardrecipe |-> [b \in BoardIds |-> ""],
            recipes |-> {}
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
