----------------- MODULE 99_feeder -----------------

EXTENDS Integers, Sequences, FiniteSets, TLC

PlaceReels (env, sys) ==
    \E reel \in env.reels:
        \E pl \in sys.production_locations:
            \E feeder \in pl.feeders:
                /\ Cardinality(feeder.reels) < 2
                /\  LET updatedFeeder ==
                        [feeder EXCEPT !.reels = feeder.reels \union {reel}]
                    IN LET updatedFeeders ==
                        (pl.feeders \ {feeder}) \union {updatedFeeder}
                    IN LET updatedProductionLocation ==
                        [pl EXCEPT !.feeders = updatedFeeders]
                    IN sys' = [
                        sys EXCEPT
                        !.production_locations = (sys.production_locations
                            \ {pl}) \union {updatedProductionLocation}
                    ]
                /\ env' =   [
                                env EXCEPT
                                !.reels = @ \ {reel}
                            ]

====