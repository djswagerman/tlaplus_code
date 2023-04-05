----------------- MODULE 99_scheduler -----------------

EXTENDS Integers, Sequences, FiniteSets, TLC, 99_utils


SetRecipeForBoard(boardId, env, sys) ==
    /\ sys.boardrecipe[boardId] = ""
    /\ sys' = [sys EXCEPT !.boardrecipe[boardId] = env.boardrecipe[boardId]]
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

Schedule (env, sys) ==
    \E board \in sys.boards :
        /\  \E recipe \in sys.recipes :
                \E pl \in sys.production_locations :
                    \E feeder \in pl.feeders :
                        \E reel \in feeder.reels :
                            \E recipe_position \in recipe.positions :
                                \E board_position \in board.positions :
                                    /\ recipe_position.component = reel.componentType
\*                                    /\ recipe_position = board_position
                                    /\ LET br == sys.boardrecipe[board.id]
                                        IN   
                                            /\ br # ""
                                            /\ recipe.id = br
                                            /\ env' = <<board, recipe, pl, feeder, reel, recipe_position, board_position, br>>

\* PlaceReels (env, sys) ==
\*     \E reel \in env.reels:
\*         \E pl \in sys.production_locations:
\*             \E feeder \in pl.feeders:
\*                 /\ Cardinality(feeder.reels) < 2
\*                 /\  LET updatedFeeder ==
\*                         [feeder EXCEPT !.reels = feeder.reels \union {reel}]
\*                     IN LET updatedFeeders ==
\*                         (pl.feeders \ {feeder}) \union {updatedFeeder}
\*                     IN LET updatedProductionLocation ==
\*                         [pl EXCEPT !.feeders = updatedFeeders]
\*                     IN sys' = [
\*                         sys EXCEPT
\*                         !.production_locations = (sys.production_locations
\*                             \ {pl}) \union {updatedProductionLocation}
\*                     ]
\*                 /\ env' =   [
\*                                 env EXCEPT
\*                                 !.reels = @ \ {reel}
\*                             ]



====
 
\* The function definition 
\* PrepareQueueForProductionLocation (boardId, locationId, env, sys) ==

====
