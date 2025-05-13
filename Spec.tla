---- MODULE Spec ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          values, \* Set of all valid values
          linkTag, \* linkState tag
          discTag \* discState tag

VARIABLES discovery,\*  
          sessions, \*  
          msgs,     \*
          lmsg,     \* 
          linkState,
          discState,
          linkSync,
          discSync     

discVars == <<discSync, discState>>
linkVars == <<linkSync, linkState>>
vars == <<discovery, sessions, msgs, lmsg, linkVars, discVars>>

subsets == SUBSET nodes

LinkTable == INSTANCE DeltaCRDT WITH values <- subsets, ctag <- linkTag, sync <- linkSync, state <- linkState

DiscTable == INSTANCE DeltaCRDT WITH values <- subsets, ctag <- discTag, sync <- discSync, state <- discState

Connector == INSTANCE FullConnector

Network == INSTANCE ALOMeshNetwork

TypeOK ==
    /\ Network!ALOTypeOK
    /\ LinkTable!TypeOK
    /\ DiscTable!TypeOK
    
Init == 
    /\ Network!ALOInit
    /\ LinkTable!Init
    /\ DiscTable!Init
    /\ Connector!Init


NewPeer(local, new) ==
    /\ discSync' = [discSync EXCEPT ![local] = TRUE]
    /\ discState' = [[discState EXCEPT ![local][local].seq = @ + 1] 
                                EXCEPT ![local][local].value = @ \cup {new}]
    /\ Network!NewPeer(local, new)
    /\ UNCHANGED <<lmsg, msgs, linkVars>>

OpenSession(n, k) == 
    /\ Connector!Connect(n, k)
    /\ Network!OpenSession(n, k)
    /\ linkSync' = [[linkSync EXCEPT ![n] = TRUE] EXCEPT ![k] = TRUE]
    /\ discSync' = [discSync EXCEPT ![n] = TRUE] \* Should sync all if we have new session
    /\ linkState' = [[[[linkState EXCEPT ![n][n].seq = @ + 1] 
                                    EXCEPT ![n][n].value = @ \cup {k}]
                                    EXCEPT ![k][k].seq = @ + 1]
                                    EXCEPT ![k][k].value = @ \cup {n}]
    /\ UNCHANGED <<lmsg, msgs, discState>>


Deliver(n,k) == 
    /\ Network!Deliver(n,k) 
    /\ UNCHANGED <<linkVars, discVars>>

    
Recieve(n, k) == 
    \/  /\ DiscTable!Recieve(n, k)
        /\ UNCHANGED <<linkVars>>
    \/  /\ LinkTable!Recieve(n, k)
        /\ UNCHANGED <<discVars>>

SendAdvertisement(n) ==
    \/ DiscTable!SendAdvertisement(n) /\ UNCHANGED linkVars
    \/  LinkTable!SendAdvertisement(n) /\ UNCHANGED discVars

Next == 
    \E n, k \in nodes: 
    \/  Deliver(n, k)
    \/  Recieve(n, k)
    \/  NewPeer(n, k)
    \/  OpenSession(n, k)
    \/  SendAdvertisement(n)


Fairness == \A n, k \in nodes: 
            /\ WF_vars(OpenSession(n, k))
            /\ WF_vars(NewPeer(n, k))
            /\ WF_vars(SendAdvertisement(n))
            /\ SF_vars(Deliver(n, k))
            /\ SF_vars(Recieve(n, k))  


Convergence == <>\A n,k \in nodes: 
                           /\ linkState[n] = linkState[k]
                           /\ discState[n] = discState[k]


Spec == Init /\ [][Next]_vars /\ Fairness 

Symmetry == Permutations(nodes)
====