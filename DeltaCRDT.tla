---- MODULE DeltaCRDT ----
EXTENDS TLC

CONSTANTS nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  
          sessions, \*  
          msgs, \*
          chanState \* from ReliableBroadcast


vars == <<discovery, sessions, msgs, chanState>>

Network == INSTANCE ReliableBroadcast

TypeOK == Network!TypeOK

Init == Network!Init

Next == Network!Next

Spec == Init /\ [] [Next]_vars

Symmetry == Network!Symmetry

====