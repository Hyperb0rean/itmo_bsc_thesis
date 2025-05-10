---- MODULE DeltaCRDT ----

(*
Using CvRDT (state CRDT) because network has only "at-least-once" guarantee
*)

EXTENDS TLC, Naturals, Integers

CONSTANTS nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  
          sessions, \*  
          msgs, \*
          lmsg, \* from ATOMeshNetwork
          state (* state[local][n]: local, n \in nodes -- local CvRDT object 
                        .seq -- value of Vector Clock
                        .value -- any CvRDT value 
                *)

vars == <<discovery, sessions, msgs, lmsg, state>>

Network == INSTANCE ALOMeshNetwork

TypeOK == Network!TypeOK

Init == 
    /\ Network!Init
    /\ state = [local \in nodes |-> [n \in nodes |-> 
                IF local = n
                THEN [seq |-> 0, value |-> {}]
                ELSE [seq |-> -1, value |-> {}] \* Sentinel for non existing nodes
                ]]


Join(a, b) == IF a > b 
              THEN a 
              ELSE b

VectorClock(local) == [n \in nodes |-> local[n].seq]

Get(local) == [n \in {k \in nodes : local[k].seq # -1} |-> local[n].seq]

Prepare(local, incoming) == 
    DOMAIN [n \in {k \in DOMAIN incoming : Join(local[k], incoming[k]) # local[k]}  |-> {}]

Set(local, incoming) == Prepare(VectorClock(local), VectorClock(incoming))

Update(local, value) ==
    LET newState == [[state EXCEPT ![local][local].seq = @ + 1] 
                            EXCEPT ![local][local].value = value] IN
    /\ Network!Broadcast(local, [type |-> "ADV", body |-> Get(newState[local])])
    /\ state' = newState
    /\ UNCHANGED lmsg

RecieveAdvertisement(dst, src, msg) ==
    LET req == Prepare(VectorClock(state[dst]), msg.body) IN
    IF req # {}
    THEN 
        /\ Network!Send(src, dst, [type |-> "REQ", body |-> req])
        /\ lmsg' = [lmsg EXCEPT ![dst][src] = @ \ msg]
        /\ UNCHANGED state
    ELSE UNCHANGED vars

RecieveRequest(dst, src, msg) ==
    LET resp == [n \in msg.body |-> state[dst][n]] IN
    /\ Network!Send(src, dst, [type |-> "RESP", body |-> resp])
    /\ lmsg' = [lmsg EXCEPT ![dst][src] = @ \ msg]
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
    ELSE UNCHANGED vars

Recieve(dst, src) ==
    CHOOSE msg \in lmsg[dst][src]:
    CASE msg.type = "ADV" -> RecieveAdvertisement(dst, src, msg)
      [] msg.type = "REQ" -> RecieveRequest(dst, src, msg)
      [] msg.type = "RESP"-> RecieveResponse(dst, src, msg)
      [] OTHER                  -> UNCHANGED vars

Next == 
    \/ Network!Next /\ UNCHANGED state
    \/ \E n \in nodes:
        \* /\ state[n][n].seq = -1
        /\ Update(n, n)
    \/ \E dst, src \in nodes: 
        /\ lmsg[dst][src] # {}
        /\ Recieve(dst, src)

Spec == Init /\ [] [Next]_vars

\* Symmetry == Network!Symmetry

====