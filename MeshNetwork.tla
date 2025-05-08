---- MODULE MeshNetwork ----
EXTENDS TLC, Sequences

CONSTANT nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions, \*  specifies which nodes could send messages
          msgs \* specifies messages in flight

vars == << discovery, sessions, msgs >>

TypeOK == 
    /\ \A n \in nodes: discovery[n] \subseteq nodes \ {n} \* Nodes should not discover themselves
    /\ \A n \in nodes: sessions[n] \subseteq nodes \*  Nodes should not connect to themselves
    (* Not just subset of discovery 
     because it is possible to have session but not have discovery *)


Init == 
    /\ discovery = [n \in nodes |-> {}]
    /\ sessions = [n \in nodes |-> {}]
    /\ msgs = [from \in nodes |-> [to \in nodes |-> <<>>]]


NewPeer == 
    \/ \E n \in nodes: 
       \E k \in nodes: 
       /\ k # n
       /\ ~(k \in discovery[n])
       /\ discovery' = [discovery EXCEPT ![n] = @ \cup {k}]
       /\ UNCHANGED <<sessions, msgs>>

LostPeer == 
    \/ \E n \in nodes: 
        /\ discovery[n] # {}
        /\ \E k \in discovery[n]: discovery' = [discovery EXCEPT ![n] = @ \ {k}]
        /\ UNCHANGED <<sessions, msgs>>

Next == 
    \/ NewPeer
    \/ LostPeer
    \/ UNCHANGED vars

Spec == Init /\ [] [Next]_vars

====