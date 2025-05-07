---- MODULE ReliableBroadcast ----
EXTENDS TLC, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          data \* data to send

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions, \*  specifies which nodes could send messages
          msgs, \* specifies messages in flight
          nodesState

nvars == << discovery, sessions, msgs >>
vars == << discovery, sessions, msgs, nodesState >>

Network == INSTANCE MeshNetwork

TypeOK == Network!TypeOK

Init == 
    /\ Network!Init
    /\ nodesState = [n \in nodes \X nodes  |-> "closed"]

OpenSession(n, k) ==
    /\ n # k
    /\ ~(k \in sessions[n])
    /\ ~(n \in sessions[k])
    /\ k \in discovery[n] \* other could not be true
    /\ sessions' = [[sessions EXCEPT ![n] = @ \cup {k}] EXCEPT ![k] = @ \cup {n}] 
    /\ nodesState' = [[nodesState EXCEPT ![<<n, k>>] = "opened"] EXCEPT ![<<k, n>>] = "opened"]
    /\ UNCHANGED <<discovery, msgs>>

CloseSession(n, k) ==
    /\ n # k
    /\ k \in sessions[n]
    /\ n \in sessions[k]
    /\ sessions' = [[sessions EXCEPT ![n] = @ \ {k}] EXCEPT ![k] = @ \ {n}] 
    /\ nodesState' = [[nodesState EXCEPT ![<<n, k>>] = "closed"] EXCEPT ![<<k, n>>] = "closed"]
    /\ UNCHANGED <<discovery, msgs>>

Send(n, k, msg) ==
    /\ nodesState[<<n, k>>] = "opened"
    /\ msgs' = [msgs EXCEPT ![<<n, k>>] = Append(@, msg)]
    /\ nodesState' = [nodesState EXCEPT ![<<n, k>>] = "sent"]
    /\ UNCHANGED <<discovery, sessions>>

Next == 
    \/ Network!Next /\ UNCHANGED nodesState
    \/ \E n, k \in nodes: OpenSession(n, k)
    \/ \E n, k \in nodes: CloseSession(n, k)
    \/ \E n, k \in nodes: \E msg \in data: Send(n, k, msg)
    \/ UNCHANGED vars


Spec == Init /\ [] [Next]_vars

====