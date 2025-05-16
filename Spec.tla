---- MODULE Spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          maxSeq


VARIABLES discovery,\*  
          sessions, \* from MeshNetwork
          msgs,     \*
          state,    \*
          sync      \* from DeltaCRDT

nodeVars == <<sync, state>>
vars == <<discovery, sessions, msgs, nodeVars>>
subsets == SUBSET nodes

-----------------------------------------------------------------------------

Synchronizator == INSTANCE AbstractDeltaCRDT WITH values <- subsets

Connector == INSTANCE FullConnector

Network == INSTANCE MeshNetwork

Graph == INSTANCE GraphUtil WITH nodes <- nodes, edges <- sessions 

-----------------------------------------------------------------------------

TypeOK ==
    /\ Network!TypeOK
    /\ Synchronizator!TypeOK
    
-----------------------------------------------------------------------------

Init == 
    /\ Network!Init
    /\ sync = [local \in nodes |-> FALSE]
    /\ Synchronizator!Init
    /\ Connector!Init


NewPeer(local, new) ==
    /\ Network!NewPeer(local, new)
    /\ UNCHANGED <<msgs, nodeVars>>

OpenSession(src, dst) == 
    /\ Connector!CouldConnect(src, dst)
    /\ Network!OpenSession(src, dst)
    /\ sync' = [sync EXCEPT ![src] = TRUE,
                            ![dst] = TRUE]
    /\ state' = [state EXCEPT   ![src][src].seq = @ + 1, 
                                ![src][src].value = @ \cup {dst},
                                ![dst][dst].seq = @ + 1,
                                ![dst][dst].value = @ \cup {src}]
    /\ UNCHANGED msgs

    
Recieve(dst, src) == 
    Synchronizator!Recieve(dst, src)


SendAdvertisement(src) ==
    Synchronizator!SendAdvertisement(src)

Terminated == 
    /\ \A n \in nodes: sync[n] = FALSE
    /\ UNCHANGED vars

Next == 
    \/ Terminated
    \/ \E n, k \in nodes: 
        \/  Recieve(n, k)
        \/  NewPeer(n, k)
        \/  OpenSession(n, k)
        \/  SendAdvertisement(n)

-----------------------------------------------------------------------------

Fairness == \A n, k \in nodes: 
            /\ ENABLED NewPeer(n, k) ~> ENABLED NewPeer(k, n) \* <>eventually other node should discover if first discovered 
            /\ WF_vars(OpenSession(n, k)) \* If <>eventually []always node discovered other and it can connect it should []always <>eventually connect
            /\ WF_vars(SendAdvertisement(n)) \* If node <>eventually []always should sync its state it should <>eventually do it
            /\ SF_vars(Recieve(n, k))  \* If []always <>eventually could recieve it []always <>eventually will do it

-----------------------------------------------------------------------------

EventualConsistency == 
    LET connected == Graph!Connected IN
    <> \A n,k \in nodes: connected[n, k] => state[n] = state[k]

ConnectionCompletness ==
    \A n,k \in nodes:  <>[](Connector!CouldConnect(n, k) /\ k \in discovery[n])
                         =>  <>[]Graph!ExistEdge(n, k) 

SequenceMonotonicity ==
    [][\A n \in nodes:
       \A k \in DOMAIN state[n]:
        state'[n][k].seq >= state[n][k].seq]_vars

SequenceInvariant ==
    \A n \in nodes:
       \A k \in DOMAIN state[n]:
        state[n][k].seq <= maxSeq

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ Fairness

Symmetry == Permutations(nodes)
====