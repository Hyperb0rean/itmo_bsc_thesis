---- MODULE DeltaCRDT ----

(*
Using CvRDT (state CRDT) because network has only "at-least-once" guarantee
*)

EXTENDS TLC, Naturals, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          values, \* Set of all valid values
          ctag      \* tag for messages for concrete CvRDT object


VARIABLES discovery,\*  
          sessions, \*  
          msgs,     \*
          lmsg,     \* from ALOMeshNetwork
          sync,     \* sync[local]L local \in nodes flag to synchronize state[local]
          state     (* state[local][n]: local, n \in nodes -- local CvRDT object 
                        .seq -- value of Vector Clock
                        .value -- any CvRDT value 
                    *)

vars == <<discovery, sessions, msgs, lmsg, sync, state>>

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
        /\ \A m \in lmsg[src][dst]: Message(m) 
        /\ \A i \in 1..Len(msgs[src][dst]): Message(msgs[src][dst][i])


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
    /\ Network!Broadcast(local, [tag |-> ctag, type |-> "ADV", body |-> Get(state[local])])
    /\ sync' = [sync EXCEPT ![local] = FALSE] 
    /\ UNCHANGED <<discovery, sessions, state, lmsg>>

RecieveAdvertisement(dst, src, msg) ==
    LET req == Prepare(Get(state[dst]), msg.body) IN
    IF req # {}
    THEN 
        /\ Network!Send(dst, src, [tag |-> ctag, type |-> "REQ", body |-> req])
        /\ UNCHANGED <<state, sync>>
    ELSE UNCHANGED <<discovery, sessions, state, sync,  msgs>>

RecieveRequest(dst, src, msg) ==
    LET resp == [n \in msg.body |-> state[dst][n]] IN
    /\ Network!Send(dst, src, [tag |-> ctag, type |-> "RESP", body |-> resp])
    /\ UNCHANGED <<state, sync>>

RecieveResponse(dst, src, msg) ==
    LET affected == Set(state[dst], msg.body) IN
    IF affected # {}
    THEN 
        /\ state' = [state EXCEPT ![dst] = 
                    [n \in (affected \cup DOMAIN state[dst]) |-> 
                            IF n \in affected
                            THEN msg.body[n]
                            ELSE state[dst][n]
                    ]]
        /\ sync' = [sync EXCEPT ![dst] = TRUE]
        /\ UNCHANGED <<discovery, sessions, msgs>>
        \* /\ Network!Broadcast(dst, [tag |-> ctag, type |-> "ADV", body |-> Get(state'[dst])])
    ELSE UNCHANGED <<discovery, sessions, state, sync, msgs>>

Recieve(dst, src) ==
    /\ lmsg[dst][src] # {}
    /\ \E msg \in lmsg[dst][src]:
        /\ msg.tag = ctag
        /\ lmsg' = [lmsg EXCEPT ![dst][src] = @ \ {msg}]
        /\ CASE msg.type = "ADV" -> RecieveAdvertisement(dst, src, msg)
             [] msg.type = "REQ" -> RecieveRequest(dst, src, msg)
             [] msg.type = "RESP"-> RecieveResponse(dst, src, msg)
             [] OTHER            -> UNCHANGED <<discovery, sessions, state, msgs>>

====