---- MODULE ALOMeshNetwork ----
(*
At-Least-Once Mesh Network 

We assume reliable channel that could not loose messages
But due to cycles in network only "at-least-once" guarantee is possible 
*)


EXTENDS TLC, MeshNetwork, Sequences, Naturals

VARIABLES msgs \* msg[src][dst] -- FIFO channel between src and dst

vars == << discovery, sessions, msgs >>

ALOTypeOK == MNTypeOK

ALOInit == 
    /\ MNInit
    /\ msgs = [src \in nodes |-> [dst \in (nodes \ {src}) |-> <<>>]]


LOCAL Contains(s, e) ==
    /\ s # <<>>
    /\ \E i \in 1..Len(s) : s[i] = e

Broadcast(src, msg) ==
    \/  sessions[src] = {} /\ UNCHANGED msgs
    \/  /\ msgs' = [msgs EXCEPT ![src] = 
            [dst \in (nodes \ {src}) |-> 
                IF (dst \in sessions[src] /\ ~Contains(msgs[src][dst], msg))
                THEN Append(msgs[src][dst], msg)
                ELSE msgs[src][dst]]]
        /\ UNCHANGED <<discovery, sessions>>

====