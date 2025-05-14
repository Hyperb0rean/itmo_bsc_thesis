---- MODULE GraphUtil ----
EXTENDS TLC, FiniteSets

CONSTANT nodes

VARIABLES edges

ExistEdge(a, b) ==
     a \in edges[b] /\ b \in edges[a]

Connected ==
    LET C[N \in SUBSET nodes] ==
    IF N = {}
    THEN [m,n \in nodes |-> m = n \/ ExistEdge(m, n)]
    ELSE LET u == CHOOSE u \in N : TRUE
            Cu == C[N \ {u}]
        IN  [m,n \in nodes |-> \/ Cu[m,n]
                               \/ (Cu[m,u] /\ Cu[u,n])]
    IN  C[nodes]


====