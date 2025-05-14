---- MODULE Spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nodes \* Set of all nodes participating in communication

VARIABLES discovery,\*  
          sessions, \*  
          msgs,     \*
          state,
          sync
        \*   updated,
        \*   delivered

nodeVars == <<sync, state>>
vars == <<discovery, sessions, msgs, nodeVars>>

subsets == SUBSET nodes

Synchronizator == INSTANCE DeltaCRDT WITH values <- subsets

Connector == INSTANCE NeverConnector

Network == INSTANCE ALOMeshNetwork

Graph == INSTANCE GraphUtil WITH nodes <- nodes, edges <- sessions 

TypeOK ==
    /\ Network!ALOTypeOK
    /\ Synchronizator!TypeOK
    
Init == 
    /\ Network!ALOInit
    /\ Synchronizator!Init
    /\ Connector!Init


NewPeer(local, new) ==
    /\ Network!NewPeer(local, new)
    /\ UNCHANGED <<msgs, nodeVars>>

OpenSession(n, k) == 
    /\ Connector!Connect(n, k)
    /\ Network!OpenSession(n, k)
    /\ sync' = [sync EXCEPT ![n] = TRUE,
                            ![k] = TRUE]
    /\ state' = [state EXCEPT   ![n][n].seq = @ + 1, 
                                ![n][n].value = @ \cup {k},
                                ![k][k].seq = @ + 1,
                                ![k][k].value = @ \cup {n}]
    /\ UNCHANGED <<msgs>>

    
Recieve(n, k) == 
    Synchronizator!Recieve(n, k)


SendAdvertisement(n) ==
    Synchronizator!SendAdvertisement(n)

Terminated == 
    /\ \A n \in DOMAIN sync: sync[n] = FALSE
    /\ UNCHANGED vars

Next == 
    \/ Terminated
    \/ \E n, k \in nodes: 
        \/  Recieve(n, k)
        \/  NewPeer(n, k)
        \/  OpenSession(n, k)
        \/  SendAdvertisement(n)


Fairness == \A n, k \in nodes: 
            \* /\ WF_vars(OpenSession(n, k)) \* If <>eventually []always node discovered other and it can connect it should []always <>eventually connect
            /\ WF_vars(SendAdvertisement(n)) \* If node <>eventually []always should sync its state it should <>eventually do it
            /\ SF_vars(Recieve(n, k))  \* If []always <>eventually could recieve it []always <>eventually will do it


Convergence == 
    LET matrix == Graph!Connected IN
    <> \A n,k \in nodes: matrix[n, k] => state[n] = state[k]

Spec == Init /\ [][Next]_vars /\ Fairness 

Symmetry == Permutations(nodes)
====