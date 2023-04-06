----------------- MODULE 99_scheduler -----------------

EXTENDS Integers, Sequences, FiniteSets, TLC, 99_utils


SetRecipeNameForBoard(boardId, env, sys) ==
    /\ sys.boardrecipe_name[boardId] = ""
    /\ sys' = [sys EXCEPT !.boardrecipe_name[boardId] = env.boardrecipe_name[boardId]]
    /\ UNCHANGED (env)


DownloadRecipe (recipe, env, sys) ==
    /\ sys' =   [
                        sys EXCEPT !.recipes = @ \union {recipe}
                ]
    /\ env' =  [
            env EXCEPT !.recipes = @ \ {recipe}
        ]

DownloadRecipes (env, sys) ==
        \E recipe \in { SetToSeq(env.recipes, <<>>)[i] : i \in 1..Cardinality(env.recipes) }:
            DownloadRecipe(recipe, env, sys)

PrepareBoardRecipe (board, env, sys) ==
    /\ board.state = "Unscheduled"
    /\ LET br == sys.boardrecipe_name[board.id]
        IN  /\  br # ""
            /\  \E recipe \in sys.recipes :
                /\ recipe.id = br
                /\ LET updatedBoard == [board EXCEPT !.state = "Scheduled"]
                       updatedBoards == (sys.boards \ {board}) \union {updatedBoard}
                       scheduledBoard == [
                                                id |-> board.id,
                                                state |-> "Scheduled",
                                                positions |-> recipe.positions
                                            ]
                    IN  /\ sys' = [sys EXCEPT
                                     !.boardrecipes = @ \union {scheduledBoard},
                                     !.boards = updatedBoards]
                        /\ UNCHANGED (env)


PrepareBoardPositionForProductionLocation (brd, pos, pl, env, sys) ==
    /\ pos.state = "Unscheduled"
    /\ \E feeder \in pl.feeders :
        \E reel \in feeder.reels :
            /\ pos.component = reel.componentType
            /\  LET updatePosition == [pos EXCEPT !.state = "Scheduled"]
                    updatedBoard == [brd EXCEPT !.positions = (brd.positions \ {pos}) \union {updatePosition}]
                    updatedBoards == (sys.boardrecipes \ {brd}) \union {updatedBoard}
                    scheduledPosition == [
                                                boardId |-> brd.id,
                                                component |-> pos.component,
                                                position |-> pos.position
                                             ]
                    updatedProductionLocation == [pl EXCEPT !.queue = Append(pl.queue, scheduledPosition)]
                    updatedProductionLocations == (sys.production_locations \ {pl}) \union {updatedProductionLocation}
                IN sys' = [sys EXCEPT
                                !.production_locations = updatedProductionLocations,
                                !.boardrecipes = updatedBoards]
                        /\ UNCHANGED (env)

    
PrepareBoardForProductionLocation (board, pl, env, sys) ==
    /\ board.state = "Scheduled"
    /\ \E position \in board.positions : PrepareBoardPositionForProductionLocation (board, position, pl, env, sys) 
  
Schedule (env, sys) ==
    \/ \E board \in sys.boards : PrepareBoardRecipe (board, env, sys)
    \/ \E board \in sys.boardrecipes, pl \in sys.production_locations: PrepareBoardForProductionLocation (board, pl, env, sys)

====
