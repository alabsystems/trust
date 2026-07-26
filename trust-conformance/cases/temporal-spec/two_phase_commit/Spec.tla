---- MODULE Spec ----
EXTENDS Naturals

VARIABLES prepared, committed

Init == /\ prepared = FALSE
        /\ committed = FALSE

Prepare == /\ prepared = FALSE
           /\ prepared' = TRUE
           /\ committed' = committed

Commit == /\ prepared = TRUE
          /\ committed' = TRUE
          /\ prepared' = prepared

Next == Prepare \/ Commit

NoCommitWithoutPrepare == committed => prepared

====
