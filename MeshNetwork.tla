---- MODULE MeshNetwork ----
EXTENDS TLC, Sequences

CONSTANT nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions, \*  specifies which nodes could send messages
          msgs \* specifies messages in flight

vars == << discovery, sessions, msgs >>

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