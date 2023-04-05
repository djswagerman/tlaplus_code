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


 
\* The function definition 
\* PrepareQueueForProductionLocation (boardId, locationId, env, sys) ==

====
