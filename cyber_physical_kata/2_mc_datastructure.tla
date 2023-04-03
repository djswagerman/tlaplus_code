----------------- MODULE 2_mc_datastructure -----------------

EXTENDS 2_datastructure

ConstComponentTypes == {"Resistor", "Conductor", "IC"}
ConstBoardIds == {"b1", "b2","b3", "b4"}
ConstRobotIds== {"r1", "r2","r3", "r4"}
ConstBoardPositions ==  {
                            [x |-> 0, y |-> 0],
                            [x |-> 0, y |-> 1],
                            [x |-> 1, y |-> 0],
                            [x |-> 1, y |-> 1]
                        }
ConstComponentIds ==    {
                        [c1 |-> "Resistor"], 
                        [c2 |-> "IC"]
                        }
ConstMaxX == 2
ConstMaxY == 2
InvariantNonEmpty ==
    NonEmptyPositions (environment) < 5

====
