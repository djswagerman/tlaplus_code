----------------- MODULE 99_scheduler -----------------

EXTENDS Integers, Sequences, FiniteSets, TLC


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
 
\* The function definition 
\* PrepareQueueForProductionLocation (boardId, locationId, env, sys) ==

====
