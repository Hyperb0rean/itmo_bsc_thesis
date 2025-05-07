---- MODULE ReliableBroadcast ----
EXTENDS TLC, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          data \* data to send

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions, \*  specifies which nodes could send messages
          msgs, \* specifies messages in flight
          chanState

nvars == << chanState >>
vars == << discovery, sessions, msgs, chanState >>

Network == INSTANCE MeshNetwork

TypeOK ==
    /\ Network!TypeOK
    \* /\ \A seq \in msgs:  Check all msgs
    /\ \A s \in DOMAIN chanState: LET st == chanState[s] IN
        /\ st.state \in {"closed", "opened", "sent"}
        /\ st.lmsg \subseteq data
        

Init == 
    /\ Network!Init
    /\ chanState = [n \in (nodes \X nodes)  |-> [state |-> "closed",
                                                lmsg |-> {}]]

OpenSession(n, k) ==
    /\ n # k
    /\ ~(k \in sessions[n])
    /\ ~(n \in sessions[k])
    /\ k \in discovery[n] \* other could not be true
    /\ sessions' = [[sessions EXCEPT ![n] = @ \cup {k}] EXCEPT ![k] = @ \cup {n}] 
    /\ chanState' = [[chanState EXCEPT ![<<n, k>>].state = "opened"] EXCEPT ![<<k, n>>].state = "opened"]
    /\ UNCHANGED <<discovery, msgs>>

CloseSession(n, k) ==
    /\ n # k
    /\ k \in sessions[n]
    /\ n \in sessions[k]
    /\ sessions' = [[sessions EXCEPT ![n] = @ \ {k}] EXCEPT ![k] = @ \ {n}] 
    /\ chanState' = [[chanState EXCEPT ![<<n, k>>].state = "closed"] EXCEPT ![<<k, n>>].state = "closed"]
    /\ UNCHANGED <<discovery, msgs>>

Send(n, k, msg) ==
    /\ chanState[<<n, k>>].state = "opened"
    /\ msgs' = [msgs EXCEPT ![<<n, k>>] = Append(@, msg)]
    /\ chanState' = [chanState EXCEPT ![<<n, k>>].state = "sent"]
    /\ UNCHANGED <<discovery, sessions>>

Deliver(n, k) ==
    /\ chanState[<<k, n>>].state = "sent"
    /\ chanState' = [[chanState EXCEPT ![<<k, n>>].state = "opened"] EXCEPT ![<<n, k>>].lmsg = {Head(msgs[<<k, n>>])}] 
    /\ msgs' = [msgs EXCEPT ![<<k, n>>] = Tail(@)]
    /\ UNCHANGED <<discovery, sessions>>

Next == 
    \/ Network!Next /\ UNCHANGED nvars
    \/ \E n, k \in nodes: OpenSession(n, k)
    \* \/ \E n, k \in nodes: CloseSession(n, k)
    \/ \E n, k \in nodes: \E msg \in data: Send(n, k, msg)
    \/ \E n, k \in nodes: \E msg \in data: Deliver(n, k)
    \/ UNCHANGED vars


Spec == Init /\ [] [Next]_vars

====