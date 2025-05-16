---- MODULE DeltaCRDT ----

(*
    This module describes developed \delta-CRDT protocol and uses
    MeshNetwork abstractions discussed previously
    Using CvRDT (state CRDT) because network has only "at-least-once" guarantee
                                                                                *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS nodes, \* Set of all nodes participating in communication
          values \* Set of all valid values


VARIABLES discovery,\*  
          sessions, \*  from MeshNetwork
          msgs,     \* msg[src][dst] -- FIFO channel between src and dst
          sync,     \* sync[local]L local \in nodes flag to synchronize state[local]
          state     (* 
                        state[local][n]: local, n \in nodes -- local CvRDT object 
                        .seq -- value of Vector Clock
                        .value -- any CvRDT value 
                                                                                *)

vars == <<discovery, sessions, msgs, sync, state>>

-----------------------------------------------------------------------------

Network == INSTANCE MeshNetwork

-----------------------------------------------------------------------------

MessageTypes == {"ADV", "REQ", "RESP"}

Advertisement(msg) == 
    /\ msg.type = "ADV"
    /\ DOMAIN msg.body \subseteq nodes
    /\ \A i \in DOMAIN msg.body: msg.body[i] \in Nat

Request(msg) == 
    /\ msg.type = "REQ"
    /\ msg.body \subseteq nodes

Response(msg) == 
    /\ msg.type = "RESP"
    /\ DOMAIN msg.body \subseteq nodes
    /\ \A i \in DOMAIN msg.body: 
        /\ msg.body[i].seq \in Nat
        /\ msg.body[i].value \in values


Message(msg) == 
    \/ Advertisement(msg)
    \/ Request(msg)
    \/ Response(msg)

TypeOK == 
    /\ sync \in [nodes -> BOOLEAN]
    /\ \A n \in nodes: \E subset \in SUBSET nodes: 
                        state[n] \in [subset -> [seq: Nat, value: values]]
    /\ \A src, dst \in nodes: 
        \/ src = dst
        \/ \A i \in 1..Len(msgs[src][dst]): Message(msgs[src][dst][i])

-----------------------------------------------------------------------------

Init == 
    /\ msgs = [src \in nodes |-> [dst \in (nodes \ {src}) |-> <<>>]]
    /\ state = [local \in nodes |-> [l \in {local} |->  [seq |-> 0, value |-> {}]]]

-----------------------------------------------------------------------------

LOCAL Contains(s, e) ==
    /\ s # <<>>
    /\ \E i \in 1..Len(s) : s[i] = e

LOCAL Broadcast(src, msg) ==
    \/  sessions[src] = {} /\ UNCHANGED msgs
    \/  /\ msgs' = [msgs EXCEPT ![src] = 
            [dst \in (nodes \ {src}) |-> 
                IF (dst \in sessions[src] /\ ~Contains(msgs[src][dst], msg))
                THEN Append(msgs[src][dst], msg)
                ELSE msgs[src][dst]]]
        /\ UNCHANGED <<discovery, sessions>>

-----------------------------------------------------------------------------

\* Extracts vector clock from node state
LOCAL Get(data) == [n \in DOMAIN data |-> data[n].seq]

\* Used for \delta-mutator generation
LOCAL Prepare(local, incoming) == 
    LET new == (DOMAIN incoming) \ (DOMAIN local)
        intersection == (DOMAIN incoming \cap DOMAIN local)
        updated == {k \in intersection: local[k] < incoming[k]} IN
    new \cup updated

\* Semi-lattice join on node state
LOCAL Merge(local, incoming) == Prepare(Get(local), Get(incoming))

-----------------------------------------------------------------------------

SendAdvertisement(local) ==
    /\ sync[local] = TRUE
    /\ Broadcast(local, [type |-> "ADV", body |-> Get(state[local])])
    /\ sync' = [sync EXCEPT ![local] = FALSE] 
    /\ UNCHANGED <<discovery, sessions, state>>

LOCAL RecieveAdvertisement(dst, src, msg, newMsgs) ==
    LET req == Prepare(Get(state[dst]), msg.body) IN
    /\  IF req # {}
        THEN msgs' = [newMsgs EXCEPT ![dst][src] 
                            = Append(@, [type |-> "REQ", body |-> req])]
        ELSE msgs' = newMsgs 
    /\ UNCHANGED <<discovery, sessions, state, sync>>

LOCAL RecieveRequest(dst, src, msg, newMsgs) ==
    LET resp == [n \in msg.body |-> state[dst][n]] IN
    /\ msgs' = [newMsgs EXCEPT ![dst][src] 
                        = Append(@, [type |-> "RESP", body |-> resp])]
    /\ UNCHANGED <<discovery, sessions, state, sync>>


LOCAL RecieveResponse(dst, src, msg, newMsgs) ==
    LET affected == Merge(state[dst], msg.body) IN
    /\  IF affected # {}
        THEN    /\ state' = [state EXCEPT ![dst] = 
                        [n \in (affected \cup DOMAIN state[dst]) |-> 
                                IF n \in affected
                                THEN msg.body[n]
                                ELSE state[dst][n]
                        ]]
                /\ sync' = [sync EXCEPT ![dst] = TRUE]
                /\ UNCHANGED <<discovery, sessions>>
        ELSE UNCHANGED <<discovery, sessions, state, sync>>
    /\ msgs' = newMsgs

Recieve(dst, src) ==
    LET msg == Head(msgs[src][dst]) 
        newMsgs == [msgs EXCEPT ![src][dst] = Tail(@)] IN
    /\ dst \in sessions[src]
    /\ Len(msgs[src][dst]) > 0
    /\ CASE msg.type ="ADV" -> RecieveAdvertisement(dst, src, msg, newMsgs)
        [] msg.type = "REQ" -> RecieveRequest(dst, src, msg, newMsgs)
        [] msg.type = "RESP"-> RecieveResponse(dst, src, msg, newMsgs)
        [] OTHER            -> UNCHANGED <<discovery, sessions, state>>

====