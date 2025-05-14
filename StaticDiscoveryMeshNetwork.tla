---- MODULE StaticDiscoveryMeshNetwork ----
EXTENDS TLC, Sequences

CONSTANT nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions \*  specifies which nodes could send messages

-----------------------------------------------------------------------------

TypeOK == 
    /\ \A n \in nodes: discovery[n] \subseteq nodes \ {n} \* Nodes should not discover themselves
    /\ \A n \in nodes: sessions[n] \subseteq nodes \ {n} \*  Nodes should not connect to themselves
    (* Not just subset of discovery 
     because it is possible to have session but not to have discovery *)

-----------------------------------------------------------------------------

Init == 
    /\ discovery = [n \in nodes |-> nodes \ {n}] \* Full mesh discovery
    /\ sessions = [n \in nodes |-> {}]


(*Discovery changing is not supported*)
NewPeer(src, new) == UNCHANGED <<discovery, sessions>>

LostPeer(src, lost) == UNCHANGED <<discovery, sessions>>

OpenSession(src, dst) ==
    /\ src # dst
    /\ ~(dst \in sessions[src])
    /\ ~(src \in sessions[dst])
    /\ dst \in discovery[src] \* other may not be true
    /\ sessions' = [sessions EXCEPT ![src] = @ \cup {dst},
                                    ![dst] = @ \cup {src}] 
    /\ UNCHANGED discovery

CloseSession(src, dst) ==
    /\ src # dst
    /\ dst \in sessions[src]
    /\ src \in sessions[dst]
    /\ sessions' = [sessions EXCEPT ![src] = @ \ {dst},
                                    ![dst] = @ \ {src}] 
    /\ UNCHANGED discovery

====