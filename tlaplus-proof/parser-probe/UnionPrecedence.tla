------------------------- MODULE UnionPrecedence -----------------------------
EXTENDS Naturals
VARIABLE value
Init == value = (UNION {{}} \cup {{}})
Next == UNCHANGED value
Spec == Init /\ [][Next]_value
SanyMeaning == value = {{}}
ExplicitMeaning == value = ((UNION {{}}) \cup {{}})
=============================================================================
