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

ScheduleBoardPosition (board_position, env, sys) == 
    /\ board_position.state = "Unscheduled"
    /\ env' = board_position


ScheduleBoard (board, env, sys) ==
    /\ board.state = "Unscheduled"
    /\ LET br == sys.boardrecipe_name[board.id]
        IN  /\  br # ""
            /\  \E recipe \in sys.recipes :
                /\ LET updatedBoard == [board EXCEPT !.state = "Scheduled"]
                       updatedBoards == (sys.boards \ {board}) \union {updatedBoard}
                       scheduledBoard ==    [
                                                id |-> board.id,
                                                state |-> "Scheduled",
                                                positions |-> recipe.positions
                                            ]
                    IN  /\ sys' = [[sys EXCEPT !.boardrecipes = @ \union {scheduledBoard}]
                                    EXCEPT !.boards = updatedBoards]
                        /\ UNCHANGED (env)

\* /\  LET updatedFeeder ==
\*                         [feeder EXCEPT !.reels = feeder.reels \union {reel}]
\*                     IN LET updatedFeeders ==
\*                         (pl.feeders \ {feeder}) \union {updatedFeeder}
\*                     IN LET updatedProductionLocation ==
\*                         [pl EXCEPT !.feeders = updatedFeeders]
\*                     IN sys' = [
\*                         sys EXCEPT
\*                         !.production_locations = (sys.production_locations
\*                             \ {pl}) \union {updatedProductionLocation}
\*    /\ \E board_position \in board.positions : ScheduleBoardPosition (board_position, env, sys)

Schedule (env, sys) ==
    /\ \E board \in sys.boards : ScheduleBoard (board, env, sys)
    

        \* /\  \E recipe \in sys.recipes :
        \*         \E pl \in sys.production_locations :
        \*             \E feeder \in pl.feeders :
        \*                 \E reel \in feeder.reels :
        \*                     \E recipe_position \in recipe.positions :
        \*                         \E board_position \in board.positions :
        \*                             /\ recipe_position.component = reel.componentType
        \*                             /\ recipe_position.position = board_position.position
        \*                             /\ LET br == sys.boardrecipe[board.id]
        \*                                 IN   
        \*                                     /\ br # ""
        \*                                     /\ recipe.id = br
        \*                                     /\ env' = <<board, recipe, pl, feeder, reel, recipe_position.position, board_position.position, br>>

====
