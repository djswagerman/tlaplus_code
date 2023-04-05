----------------- MODULE 999_mc_playground -----------------

EXTENDS 999_playground 


ConstComponentType ==    {"resistor", "IC"}
ConstRecordType    ==    {
                            [x |-> a, y |-> b] : a, b \in 0..3
                         }


ConstComplexRecordType    ==
                            {
                                [
                                    component |-> c,
                                    position |-> p
                                ] : c \in ConstComponentType, p \in  {
                                            [x |-> a, y |-> b] : a, b \in 0..3
                                        }

                            }

=====