---- MODULE DeltaCRDT ----

(*
Using CvRDT (state CRDT) because network has only "at-least-once" guarantee
*)

EXTENDS TLC, Naturals, Integers

CONSTANTS nodes, \* Set of all nodes participating in communication

VARIABLES discovery, \*  
          sessions, \*  
          msgs, \*
          lmsg \* from ATOMeshNetwork
          state (* state[local][n]: local, n \in nodes -- local CvRDT object 
                        .seq -- value of Vector Clock
                        .value -- any CvRDT value 
                *)

vars == <<discovery, sessions, msgs, lmsg, state>>

Network == INSTANCE ATOMeshNetwork

TypeOK == Network!TypeOK

Init == 
    /\ Network!Init
    /\ state = [local \in nodes |-> [n \in nodes |-> 
                IF local = n
                THEN [seq |-> -1, value |-> {}] \* Sentinel seq
                THEN [seq |-> 0, value |-> {}]
                ]]


Max(a, b) == IF a > b THEN a ELSE b

Get(st) == [n \in nodes : (st[n].seq # -1) |-> st[n].seq]

Prepare(st, incoming) == DOMAIN 
                            [n \in DOMAIN incoming : (Max(st[n], incoming[n]) # st[n])  
                                |-> st[n]]
Set(st, incoming) == DOMAIN 
                        [n \in DOMAIN incoming : (Max(st[n].seq, incoming[n].seq) # st[n].seq)  
                                |-> st[n].seq]

Update(local, value) ==
    /\ state' = [[state EXCEPT ![local][local].state = @ + 1] 
                        EXCEPT ![local][local].value = value]
    /\ Network!Broadcast(local, [type -> "SYNC_ADV", body |-> GetClock(state)])

RecieveAdvertisement(dst, src) ==
    /\ Network!Broadcast

Recieve(dst, src) ==
    CASE lmsg[dst].type == "SYNC_ADV" -> RecieveAdvertisement(dst, src)
         lmsg[dst].type == "SYNC_REQ" -> UNCHANGED vars
         lmsg[dst].type == "SYNC_RESP"-> UNCHANGED vars

Next == Network!Next

Spec == Init /\ [] [Next]_vars

Symmetry == Network!Symmetry

====