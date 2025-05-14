---- MODULE NeverConnector ----
EXTENDS TLC

CONSTANT nodes \* Set of all nodes participating in communication

VARIABLES discovery, \*  specifies which nodes could communicate
          sessions \*  specifies which nodes could send messages

vars == << discovery, sessions >>

Network == INSTANCE MeshNetwork

Init == TRUE

Connect(src, dst) == FALSE

Drop(src, dst) == FALSE

====