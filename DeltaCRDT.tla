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


Join(a, b) == IF a > b THEN a ELSE b

Get(local) == [n \in {k \in nodes : local[k] # {}} |-> local[n].seq]

Prepare(local, incoming) == 
    DOMAIN [n \in {k \in DOMAIN incoming : Join(local[k], incoming[k]) # local[k]}  |-> {}]

Set(local, incoming) == Prepare(Get(local), Get(incoming))

Update(local, value) ==
    /\ state' = [[state EXCEPT ![local][local].state = @ + 1] 
                        EXCEPT ![local][local].value = value]
    /\ Network!Broadcast(local, [type |-> "ADV", body |-> Get(state)])

RecieveAdvertisement(dst, src) ==
    LET req == Prepare(Get(state[dst]), lmsg[dst][src].body) IN
    IF req # {}
    THEN 
        /\ Network!Send(src, dst, [type |-> "REQ", body |-> req])
        /\ UNCHANGED state
    ELSE UNCHANGED vars

RecieveRequest(dst, src) ==
    LET resp == [n \in lmsg[dst][src].body |-> state[dst][n]] IN
    /\ Network!Send(src, dst, [type |-> "RESP", body |-> resp])
    /\ UNCHANGED state

RecieveResponse(dst, src) ==
    LET affected == Set(state[dst], lmsg[dst][src].body) IN
    IF affected # {}
    THEN 
        LET newState == [state EXCEPT ![dst] = 
        [n \in nodes |-> 
                IF n \in affected
                THEN lmsg[dst][src].body[n]
                ELSE state[dst][n]
        ]] IN
        /\ state' = newState
        /\ Network!Broadcast(dst, [type |-> "ADV", body |-> newState])
    ELSE UNCHANGED vars

Recieve(dst, src) ==
    CASE lmsg[dst][src].type = "ADV" -> RecieveAdvertisement(dst, src)
      [] lmsg[dst][src].type = "REQ" -> RecieveRequest(dst, src)
      [] lmsg[dst][src].type = "RESP"-> RecieveResponse(dst, src)
      [] OTHER                  -> UNCHANGED vars

Next == 
    \/ Network!Next /\ UNCHANGED state
    \/ \E n \in nodes:
        /\ state[n][n].seq = -1
        /\ Update(n, n)
    \/ \E dst, src \in nodes: 
        /\ lmsg[dst][src] # {}
        /\ Recieve(dst, src)

Spec == Init /\ [] [Next]_vars

Symmetry == Network!Symmetry

====