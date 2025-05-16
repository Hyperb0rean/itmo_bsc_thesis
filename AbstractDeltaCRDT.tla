---- MODULE AbstractDeltaCRDT ----

(*
This module describes developed \delta-CRDT protocol and uses
MeshNetwork abstractions discussed previously
Using CvRDT (state CRDT) because network has only "at-least-once" guarantee
*)

EXTENDS TLC, Naturals, FiniteSets

CONSTANTS nodes, \* Set of all nodes participating in communication
          values \* Set of all valid values


VARIABLES discovery,\*  
          sessions, \*  from MeshNetwork
          msgs,     \* msgs -- set of all messages in network, destination is described by message
          sync,     \* sync[local] local \in nodes flag to synchronize state[local]
          state     (* state[local][n]: local, n \in nodes -- local CvRDT object 
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
    /\ msg.to \in nodes
    /\ msg.from \in nodes
    /\  \/ Advertisement(msg)
        \/ Request(msg)
        \/ Response(msg)
    

TypeOK == 
    /\ sync \in [nodes -> BOOLEAN]
    /\ \A n \in nodes: \E subset \in SUBSET nodes: 
                        state[n] \in [subset -> [seq: Nat, value: values]]
    /\ \A src, dst \in nodes: 
        \/ src = dst
        \/ \A msg \in msgs: Message(msg)

-----------------------------------------------------------------------------

Init == 
    /\ msgs = {}
    /\ state = [local \in nodes |-> [l \in {local} |->  [seq |-> 0, value |-> {}]]]


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
    LET vecClock == Get(state[local]) IN
    /\ sync[local] = TRUE
    /\ msgs' = msgs \cup {[from |-> local,
                           to |-> other, 
                           type |-> "ADV",
                           body |-> vecClock]: other \in sessions[local]}
    /\ sync' = [sync EXCEPT ![local] = FALSE] 
    /\ UNCHANGED <<discovery, sessions, state>>

LOCAL RecieveAdvertisement(dst, src, msg, newMsgs) ==
    LET req == Prepare(Get(state[dst]), msg.body) IN
    /\  IF req # {}
        THEN msgs' = newMsgs \cup {[from |-> dst, 
                                    to |-> src, 
                                    type |-> "REQ",
                                    body |-> req]}
        ELSE msgs' = newMsgs 
    /\ UNCHANGED <<discovery, sessions, state, sync>>

LOCAL RecieveRequest(dst, src, msg, newMsgs) ==
    LET resp == [n \in msg.body |-> state[dst][n]] IN
    /\ msgs' = newMsgs \cup {[from |-> dst,
                              to |-> src, 
                              type |-> "RESP",
                              body |-> resp]}
    /\ UNCHANGED <<discovery, sessions, state, sync>>


LOCAL RecieveResponse(dst, src, msg, newMsgs) ==
    LET affected == Merge(state[dst], msg.body) IN
    /\ IF affected # {}
        THEN /\ state' = [state EXCEPT ![dst] = 
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
    \E msg \in msgs: 
    /\ dst \in sessions[src]
    /\ msg.from = src
    /\ msg.to = dst
    /\ CASE msg.type ="ADV" -> RecieveAdvertisement(dst, src, msg,  msgs \ {msg})
        [] msg.type = "REQ" -> RecieveRequest(dst, src, msg,  msgs \ {msg})
        [] msg.type = "RESP"-> RecieveResponse(dst, src, msg,  msgs \ {msg})
        [] OTHER            -> UNCHANGED <<discovery, sessions, state>>

====