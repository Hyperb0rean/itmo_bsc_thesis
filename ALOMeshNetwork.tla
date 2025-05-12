---- MODULE ALOMeshNetwork ----
(*
At-Least-Once Mesh Network 

We assume reliable channel that could not loose messages
But due to cycles in network only "at-least-once" guarantee is possible 
*)


EXTENDS TLC, MeshNetwork, Sequences, Naturals

VARIABLES msgs, \* msg[src][dst] -- FIFO channel between src and dst
          lmsg

vars == << discovery, sessions, msgs, lmsg >>

ALOTypeOK == MNTypeOK

ALOInit == 
    /\ MNInit
    /\ msgs = [src \in nodes |-> [dst \in nodes |-> <<>>]]
    /\ lmsg = [dst \in nodes |-> [src \in nodes |-> {}]]


LOCAL Contains(s, e) ==
    /\ s # <<>>
    /\ \E i \in 1..Len(s) : s[i] = e

Send(src, dst, msg) ==
    /\ dst \in sessions[src]
    /\ ~Contains(msgs[src][dst],msg) \* Deduplication for stuttering steps elimination
    /\ msgs' = [msgs EXCEPT ![src][dst] = Append(@, msg)]
    /\ UNCHANGED <<discovery, sessions>>

Deliver(dst, src) ==
    /\ dst \in sessions[src]
    /\ Len(msgs[src][dst]) > 0
    /\ lmsg' = [lmsg EXCEPT ![dst][src] = @ \cup {Head(msgs[src][dst])}]  
    /\ msgs' = [msgs EXCEPT ![src][dst] = Tail(@)]
    /\ UNCHANGED <<discovery, sessions>>

Broadcast(src, msg) ==
    \/  sessions[src] = {} /\ UNCHANGED msgs
    \/  /\ msgs' = [msgs EXCEPT ![src] = 
            [dst \in nodes |-> 
                IF (dst \in sessions[src] /\ ~Contains(msgs[src][dst], msg))
                THEN Append(msgs[src][dst], msg)
                ELSE msgs[src][dst]]]
        /\ UNCHANGED <<discovery, sessions>>

====