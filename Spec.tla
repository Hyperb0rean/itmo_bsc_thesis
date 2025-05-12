---- MODULE Spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          values, \* Set of all valid values
          maxSeq, \* maximum sequence number of node
          linkTag, \* linkState tag
          discTag \* discState tag

VARIABLES discovery,\*  
          sessions, \*  from Connector
          msgs,     \*
          lmsg,     \* 
          linkState,
          discState     


vars == <<discovery, sessions, msgs, lmsg, linkState, discState>>

LinkTable == INSTANCE DeltaCRDT WITH tag <- linkTag, state <- linkState

DiscTable == INSTANCE DeltaCRDT WITH tag <- discTag, state <- discState

Connector == INSTANCE FullConnector

Network == INSTANCE ALOMeshNetwork

Init == 
    /\ Network!ALOInit
    /\ LinkTable!Init
    /\ DiscTable!Init
    /\ Connector!Init


Next == 
    \E n, k \in nodes: 
    \/  Network!Deliver(n,k)
    \/  /\ Network!NewPeer(n, k)
        /\ DiscTable!Update(n, discState[n][n].value \cup {k})
        /\ UNCHANGED <<linkState>>
    \/  /\ Connector!Connect(n, k)
        /\ Network!OpenSession(n, k)
        /\ LinkTable!Update(n, linkState[n][n].value \cup {k})
        /\ UNCHANGED <<discState>>
    \/  /\ LinkTable!Recieve(n, k)
    \/  /\ DiscTable!Recieve(n, k)



Spec == Init /\ [] [Next]_vars

\* Symmetry == Permutations(nodes)
====