---- MODULE Network ----
EXTENDS FiniteSets

VARIABLES network  \* Imported

DeliverMsgs(pending) ==
  LET delivered == {m \in pending : m.ts + GST <= NOW}
  IN
  /\ network' = pending \ delivered
  /\ ProcessMsgs(delivered)  \* Deliver to receivers

ProcessMsgs(msgs) ==
  \* Abstract: Update local state based on msg type
  UNCHANGED <<network>>

\* Partial synchrony: Delays <= GST
NOW == slots * SlotTime  \* Global clock
Received(node, shred) == TRUE  \* Placeholder for delivery
====
