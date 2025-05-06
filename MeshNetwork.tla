---- MODULE MeshNetwork ----
EXTENDS TLC

CONSTANT nodes \* Set of all nodes participating in communication

VARIABLES discovery, \* Matrix that specifies which nodes could communicate
          sessions, \* Matrix that specifies which nodes could send messages
          msgs \* Matrix that specifies messages in flight

vars == << discovery, sessions, msgs >>



====