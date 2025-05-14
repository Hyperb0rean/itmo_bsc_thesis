---- MODULE Spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nodes \* Set of all nodes participating in communication

VARIABLES discovery,\*  
          sessions, \*  
          msgs,     \*
          state,
          sync

nodeVars == <<sync, state>>
vars == <<discovery, sessions, msgs, nodeVars>>

subsets == SUBSET nodes

Synchronizator == INSTANCE DeltaCRDT WITH values <- subsets

Connector == INSTANCE FullConnector

Network == INSTANCE ALOMeshNetwork

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
    /\ state' = [state EXCEPT     ![n][n].seq = @ + 1, 
                                  ![n][n].value = @ \cup {k},
                                  ![k][k].seq = @ + 1,
                                  ![k][k].value = @ \cup {n}]
    /\ UNCHANGED <<msgs>>

    
Recieve(n, k) == 
    Synchronizator!Recieve(n, k)


SendAdvertisement(n) ==
    Synchronizator!SendAdvertisement(n)

Next == 
    \E n, k \in nodes: 
    \/  Recieve(n, k)
    \/  NewPeer(n, k)
    \/  OpenSession(n, k)
    \/  SendAdvertisement(n)


Fairness == \A n, k \in nodes: 
            \* /\ WF_vars(OpenSession(n, k))
            \* /\ WF_vars(NewPeer(n, k))
            /\ WF_vars(SendAdvertisement(n))
            /\ SF_vars(Recieve(n, k))  


Convergence == <>\A n,k \in nodes: 
                           /\ state[n] = state[k]


Spec == Init /\ [][Next]_vars /\ Fairness 

\* Symmetry == Permutations(nodes)
====