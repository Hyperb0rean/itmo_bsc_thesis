---- MODULE DeltaCRDT ----

(*
Using CvRDT (state CRDT) because network has only "at-least-once" guarantee
*)

EXTENDS TLC, Naturals, Sequences

CONSTANTS nodes, \* Set of all nodes participating in communication
          values, \* Set of all valid values
          maxSeq \* maximum sequence number of node

VARIABLES discovery,\*  
          sessions, \*  
          msgs,     \*
          lmsg,     \* from ALOMeshNetwork
          state     (* state[local][n]: local, n \in nodes -- local CvRDT object 
                        .seq -- value of Vector Clock
                        .value -- any CvRDT value 
                    *)

vars == <<discovery, sessions, msgs, lmsg, state>>

Network == INSTANCE ALOMeshNetwork

MessageTypes == {"ADV", "REQ", "RESP"}

SequenceNumber == 0..maxSeq

Advertisement == UNION {[type: {"ADV"}, body: [s -> SequenceNumber]]: s \in SUBSET nodes}

Request == [type: {"REQ"}, body: SUBSET nodes]

Response ==  UNION {[type: {"RESP"}, body: [s -> [seq: SequenceNumber, value: values]]]: s \in SUBSET nodes}

Message == Advertisement \cup Request \cup Response


TypeOK == 
    /\ Network!TypeOK
    /\ \A n \in nodes: \E subset \in SUBSET nodes: 
                        state[n] \in [subset -> [seq: SequenceNumber, value: values]]
    /\ \A src, dst \in nodes: 
        /\ lmsg[src][dst] \subseteq Message
        /\ \A i \in 1..Len(msgs[src][dst]): msgs[src][dst][i] \in Message


Init == 
    /\ Network!Init
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

Update(local, value) ==
    LET newState == [[state EXCEPT ![local][local].seq = @ + 1] 
                            EXCEPT ![local][local].value = value] IN
    /\ Network!Broadcast(local, [type |-> "ADV", body |-> Get(newState[local])])
    /\ state' = newState
    /\ UNCHANGED lmsg

RecieveAdvertisement(dst, src, msg) ==
    LET req == Prepare(Get(state[dst]), msg.body) IN
    IF req # {}
    THEN 
        /\ Network!Send(dst, src, [type |-> "REQ", body |-> req])
        /\ UNCHANGED state
    ELSE UNCHANGED <<discovery, sessions, state, msgs>>

RecieveRequest(dst, src, msg) ==
    LET resp == [n \in msg.body |-> state[dst][n]] IN
    /\ Network!Send(src, dst, [type |-> "RESP", body |-> resp])
    /\ UNCHANGED state

RecieveResponse(dst, src, msg) ==
    LET affected == Set(state[dst], msg.body) IN
    IF affected # {}
    THEN 
        LET newState == [state EXCEPT ![dst] = 
        [n \in nodes |-> 
                IF n \in affected
                THEN msg.body[n]
                ELSE state[dst][n]
        ]] IN
        /\ state' = newState
        /\ Network!Broadcast(dst, [type |-> "ADV", body |-> newState])
    ELSE UNCHANGED <<discovery, sessions, state, msgs>>

Recieve(dst, src) ==
    /\ lmsg[dst][src] # {}
    /\ \E msg \in lmsg[dst][src]:
        /\ lmsg' = [lmsg EXCEPT ![dst][src] = @ \ {msg}]
        /\ CASE msg.type = "ADV" -> RecieveAdvertisement(dst, src, msg)
             [] msg.type = "REQ" -> RecieveRequest(dst, src, msg)
             [] msg.type = "RESP"-> RecieveResponse(dst, src, msg)
             [] OTHER            -> UNCHANGED <<discovery, sessions, state, msgs>>

Next == 
    \/ Network!Next /\ UNCHANGED state
    \/ \E n \in nodes:
        /\ state[n][n].value # n
        /\ Update(n, n)
    \/ \E dst, src \in nodes: Recieve(dst, src)

Spec == Init /\ [] [Next]_vars

Symmetry == Network!Symmetry

====