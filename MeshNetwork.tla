---- MODULE MeshNetwork ----
EXTENDS TLC, Sequences

CONSTANT nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions \*  specifies which nodes could send messages

MNTypeOK == 
    /\ \A n \in nodes: discovery[n] \subseteq nodes \ {n} \* Nodes should not discover themselves
    /\ \A n \in nodes: sessions[n] \subseteq nodes \ {n} \*  Nodes should not connect to themselves
    (* Not just subset of discovery 
     because it is possible to have session but not have discovery *)


MNInit == 
    /\ discovery = [n \in nodes |-> {}]
    /\ sessions = [n \in nodes |-> {}]


NewPeer(src, new) == 
    /\ src # new
    /\ ~(new \in discovery[src])
    /\ discovery' = [discovery EXCEPT ![src] = @ \cup {new}]
    /\ UNCHANGED sessions

LostPeer(src, lost) == 
    /\ discovery[src] # {}
    /\ discovery' = [discovery EXCEPT ![src] = @ \ {lost}]
    /\ UNCHANGED sessions

OpenSession(src, dst) ==
    /\ src # dst
    /\ ~(dst \in sessions[src])
    /\ ~(src \in sessions[dst])
    /\ dst \in discovery[src] \* other may not be true
    /\ sessions' = [[sessions EXCEPT ![src] = @ \cup {dst}] EXCEPT ![dst] = @ \cup {src}] 
    /\ UNCHANGED discovery

CloseSession(src, dst) ==
    /\ src # dst
    /\ dst \in sessions[src]
    /\ src \in sessions[dst]
    /\ sessions' = [[sessions EXCEPT ![src] = @ \ {dst}] EXCEPT ![dst] = @ \ {src}] 
    /\ UNCHANGED discovery

====