---- MODULE ATOMeshNetwork ----
(*
At-Least-Once Mesh Network 

We assume reliable channel that could not loose messages
But due to cycles in network only "at-least-once" guarantee is possible 
*)


EXTENDS TLC, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          states \* possible state of channel

VARIABLES discovery, \*
          sessions, \*  from MeshNetwork
          msgs, \* specifies messages in flight
          chanState

nvars == << chanState, msgs >>
vars == << discovery, sessions, msgs, chanState >>

Network == INSTANCE MeshNetwork

TypeOK ==
    /\ Network!TypeOK
    /\ {"closed", "opened", "sent"} \subseteq states
    /\ \A src, dst \in nodes: LET chan == chanState[src][dst] IN
        /\ chan.state \in states

Init == 
    /\ Network!Init
    /\ msgs = [src \in nodes |-> [dst \in nodes |-> <<>>]]
    /\ chanState = [src \in nodes |-> [dst \in nodes |-> 
                                        [state |-> "closed",
                                          lmsg |-> {}] ]]

OpenSession(src, dst) == 
    /\ Network!OpenSession(src, dst)
    /\ chanState' = [[chanState EXCEPT ![src][dst].state = "opened"] EXCEPT ![dst][src].state = "opened"]
    /\ UNCHANGED msgs

CloseSession(src, dst) == 
    /\ Network!CloseSession(src, dst)
    /\ chanState' = [[chanState EXCEPT ![src][dst].state = "closed"] EXCEPT ![dst][src].state = "closed"]
    /\ UNCHANGED msgs

Send(src, dst, msg) ==
    /\ chanState[src][dst].state = "opened"
    /\ msgs' = [msgs EXCEPT ![src][dst] = Append(@, msg)]
    /\ chanState' = [chanState EXCEPT ![src][dst].state = "sent"]
    /\ UNCHANGED <<discovery, sessions>>

Deliver(dst, src) ==
    /\ chanState[src][dst].state = "sent"
    /\ chanState' = [[chanState EXCEPT ![src][dst].state = "opened"] EXCEPT ![dst][src].lmsg = {Head(msgs[src][dst])}] 
    /\ msgs' = [msgs EXCEPT ![src][dst] = Tail(@)]
    /\ UNCHANGED <<discovery, sessions>>

Broadcast(src, msg) ==
    /\ sessions[src] # {}
    /\ \A dst \in sessions[src]: chanState[src][dst].state = "opened"
    /\ msgs' = [msgs EXCEPT ![src] = [dst \in nodes |-> IF dst \in sessions[src] 
                                                    THEN Append(msgs[src][dst], msg)
                                                    ELSE msgs[src][dst]]]
    /\ chanState' = [chanState EXCEPT ![src] = [dst \in nodes |-> 
                                                    IF dst \in sessions[src] 
                                                    THEN [chanState[src][dst] EXCEPT !.state = "sent"]
                                                    ELSE chanState[src][dst]]]
    /\ UNCHANGED <<discovery, sessions>>


Next == 
    \/ Network!Next /\ UNCHANGED nvars
    \* \/ \E n,k \in nodes: OpenSession(n,k)
    \* \/ \E n,k \in nodes: Deliver(n,k)
    \* \/ \E n \in nodes: Broadcast(n, {"Hello"})
    \/ UNCHANGED vars

Spec == Init /\ [] [Next]_vars

Symmetry == Network!Symmetry

====