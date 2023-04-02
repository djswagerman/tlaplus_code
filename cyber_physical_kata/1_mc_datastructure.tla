----------------- MODULE 1_mc_datastructure -----------------

EXTENDS 1_datastructure

ConstComponentTypes == {"Resistor", "Conductor", "IC"}
ConstBoardIds == {"b1", "b2","b3", "b4"}
ConstRobotIds== {"r1", "r2","r3", "r4"}
ConstBoardPositions == {1,2,3}
ConstComponentIds == {1,2,3}
InvariantNonEmpty ==
    NonEmptyPositions (environment) < 5

====
