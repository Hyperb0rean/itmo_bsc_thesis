---- MODULE MeshNetwork ----

(*
    Current module specifies the mesh-network abstraction layer. 
    Basic implementation assumes dynamic changes in both discovery and sessions sets.
                                                                                        *)

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
    /\ discovery = [n \in nodes |-> {}]
    /\ sessions = [n \in nodes |-> {}]

-----------------------------------------------------------------------------

(*
Actions to model node discovery behaviour.
*)


NewPeer(src, new) == 
    /\ src # new
    /\ ~(new \in discovery[src])
    /\ discovery' = [discovery EXCEPT ![src] = @ \cup {new}]
    /\ UNCHANGED sessions

LostPeer(src, lost) == 
    /\ discovery[src] # {}
    /\ discovery' = [discovery EXCEPT ![src] = @ \ {lost}]
    /\ UNCHANGED sessions

-----------------------------------------------------------------------------

(*
Actions to model node connection behaviour.
In this model assumed, that all links are kind of graph edges, 
other properties (e.g. link initiator, RTT, bandwidth) are omitted.
*)

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