---- MODULE StaticMeshNetwork ----
EXTENDS TLC, Sequences

\*********************************************************************************
\*   Current module specifies the staticly configured mesh-network abstraction layer. 
\*   All links and visibility should be declared in Init action and will not change.
\*   Made for faster model checking of specific scenarios.
\*********************************************************************************


CONSTANT nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions \*  specifies which nodes could send messages

-----------------------------------------------------------------------------

TypeOK == 
    /\ \A n \in nodes: discovery[n] \subseteq nodes \ {n} \* Nodes should not discover themselves
    /\ \A n \in nodes: sessions[n] \subseteq nodes \ {n} \*  Nodes should not connect to themselves
    \* Not just subset of discovery 
    \* because it is possible to have session but not to have discovery 

-----------------------------------------------------------------------------

Init == 
    /\ discovery = [n \in nodes |-> nodes \ {n}] \* Full mesh discovery
    /\ sessions = [n \in nodes |-> nodes \ {n}] \* Full mesh sessions

\*Discovery changing is omitted
NewPeer(src, new) == UNCHANGED <<discovery, sessions>>

LostPeer(src, lost) == UNCHANGED <<discovery, sessions>>

\*Connection changing is omitted
OpenSession(src, dst) == UNCHANGED <<discovery, sessions>>

CloseSession(src, dst) == UNCHANGED <<discovery, sessions>>
====