---- MODULE DeltaCRDT ----

(*
Using state CRDT because network has only "at-least-once" guarantee
*)

EXTENDS TLC

CONSTANTS nodes, \* Set of all nodes participating in communication
          states \* possible state of channel


VARIABLES discovery, \*  
          sessions, \*  
          msgs, \*
          chanState \* from ATOMeshNetwork


vars == <<discovery, sessions, msgs, chanState>>

Network == INSTANCE ATOMeshNetwork

TypeOK == Network!TypeOK

Init == Network!Init


Advertisement(src, adv) == UNCHANGED vars

Request(src, dst, req) == UNCHANGED vars

Response(src, dst, resp) == UNCHANGED vars

Next == Network!Next

Spec == Init /\ [] [Next]_vars

Symmetry == Network!Symmetry

====