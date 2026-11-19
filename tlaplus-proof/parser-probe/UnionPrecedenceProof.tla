----------------------- MODULE UnionPrecedenceProof --------------------------
EXTENDS UnionPrecedence, TLAPS
\* Tool-version diagnostic: TLAPM 1.5 groups the ambiguous operand widely.
\* The TLC/SANY probe deliberately checks the other, standard grouping.
THEOREM AmbiguousTLAPMGrouping == (UNION {{}} \cup {{}}) = {}
BY SMT
THEOREM ExplicitSyntax == ((UNION {{}}) \cup {{}}) = {{}}
BY SMT
=============================================================================
