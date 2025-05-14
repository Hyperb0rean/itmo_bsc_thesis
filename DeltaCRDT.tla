---- MODULE DeltaCRDT ----

(*
Using CvRDT (state CRDT) because network has only "at-least-once" guarantee
*)

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS nodes, \* Set of all nodes participating in communication
          values \* Set of all valid values


VARIABLES discovery,\*  
          sessions, \*  
          msgs,     \* from ALOMeshNetwork
          sync,     \* sync[local]L local \in nodes flag to synchronize state[local]
          state     (* state[local][n]: local, n \in nodes -- local CvRDT object 
                        .seq -- value of Vector Clock
                        .value -- any CvRDT value 
                    *)

vars == <<discovery, sessions, msgs, sync, state>>

Network == INSTANCE ALOMeshNetwork

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


Init == 
    /\ sync = [local \in nodes |-> FALSE]
    /\ state = [local \in nodes |-> [l \in {local} |->  [seq |-> 0, value |-> {}]]]


Max(a, b) == IF a > b 
              THEN a 
              ELSE b

Get(data) == [n \in DOMAIN data |-> data[n].seq]

Prepare(local, incoming) == 
    LET new == (DOMAIN incoming) \ (DOMAIN local) IN
    LET intersection == (DOMAIN incoming \cap DOMAIN local) IN
    LET updated == {k \in intersection: Max(local[k], incoming[k]) # local[k]} IN
    new \cup updated

Set(local, incoming) == Prepare(Get(local), Get(incoming))

SendAdvertisement(local) ==
    /\ sync[local] = TRUE
    /\ Network!Broadcast(local, [type |-> "ADV", body |-> Get(state[local])])
    /\ sync' = [sync EXCEPT ![local] = FALSE] 
    /\ UNCHANGED <<discovery, sessions, state>>

RecieveAdvertisement(dst, src, msg, newMsgs) ==
    LET req == Prepare(Get(state[dst]), msg.body) IN
    /\  IF req # {}
        THEN msgs' = [newMsgs EXCEPT ![dst][src] 
                            = Append(@, [type |-> "REQ", body |-> req])]
        ELSE msgs' = newMsgs 
    /\ UNCHANGED <<discovery, sessions, state, sync>>

RecieveRequest(dst, src, msg, newMsgs) ==
    LET resp == [n \in msg.body |-> state[dst][n]] IN
    /\ msgs' = [newMsgs EXCEPT ![dst][src] 
                        = Append(@, [type |-> "RESP", body |-> resp])]
    /\ UNCHANGED <<discovery, sessions, state, sync>>


RecieveResponse(dst, src, msg, newMsgs) ==
    LET affected == Set(state[dst], msg.body) IN
    /\ IF affected # {}
        THEN 
            /\ state' = [state EXCEPT ![dst] = 
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