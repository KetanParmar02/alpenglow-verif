---- MODULE Network ----
EXTENDS FiniteSets, Sequences, Integers, Alpenglow  \* Import Nodes, GST, SlotTime, Byzantine(n), Offline(n), now (from RealTime)

VARIABLES network  \* Set of pending messages

\* Message type (Section 2.1: shreds; 2.4: votes/certs)
Msg == [from: Nodes, to: Nodes, type: {"shred", "vote", "cert", "repair"}, content: ANY, ts: Nat]

\* Deliver messages under partial synchrony: If sent by honest, delivered to honest within GST post-send (whitepaper Assumption 1)
DeliverMsgs ==
  LET deliverable == {m \in network : m.ts + GST <= now /\ ~Byzantine(m.from) /\ ~Offline(m.to)} IN
  /\ network' = network \ deliverable
  /\ \A m \in deliverable : ProcessMsg(m)  \* Update receiver state

\* Process message: Update local state based on type (refine per component)
ProcessMsg(m) ==
  CASE m.type = "shred" -> ReceiveShred(m.to, m.content)  \* Update shreds
    [] m.type = "vote" -> ReceiveVote(m.to, m.content)  \* Update votes
    [] m.type = "cert" -> ReceiveCert(m.to, m.content)  \* Update certs
    [] m.type = "repair" -> HandleRepair(m.to, m.content)  \* For recovery (Section 2.8)
    OTHER -> UNCHANGED vars  \* Placeholder

\* Byzantine/Offline faults: May drop/delay (non-deterministic for model checking)
FaultyDelivery ==
  \/ \E m \in network : Byzantine(m.from) \/ Offline(m.from) => DropOrDelay(m)  \* Remove or keep
  \/ UNCHANGED network

\* Drop or delay message (adversary choice under 20% stake)
DropOrDelay(m) ==
  \/ network' = network \ {m}  \* Drop
  \/ m' = [m EXCEPT !.ts = m.ts + 1] /\ network' = (network \ {m}) \union {m'}  \* Delay

\* Network partition: Model as temporary offline subsets (for resilience, Section 2.11/3.3)
PartitionAction ==
  \/ StartPartition(subset)  \* Set Offline for subset (non-det)
  \/ HealPartition(subset)  \* Reset Offline, trigger repair

\* Start partition: Mark nodes offline (adversary up to 20%)
StartPartition(subset) ==
  /\ SumStake(subset) <= OfflineThreshold
  /\ \A n \in subset : Offline'(n) = TRUE
  /\ UNCHANGED <<network>>

\* Heal: Reconnect, nodes request repair for missing (Section 3.3 re-sync)
HealPartition(subset) ==
  /\ \A n \in subset : Offline'(n) = FALSE /\ RequestRepair(n)  \* Send repair msgs
  /\ UNCHANGED <<network>>

\* Request repair for missing shreds/blocks (Section 2.8)
RequestRepair(node) ==
  \A peer \in HonestNodes \ {node} : SendMsg(node, peer, "repair", missingShreds[node])

\* Invariant: Post-GST, honest-to-honest msgs delivered if no partition
EventualDelivery ==
  \A m \in network : (~Byzantine(m.from) /\ ~Offline(m.to) /\ now >= m.ts + GST) => m \notin network'

\* Liveness under recovery: After heal, node syncs (for partition guarantees)
RecoveryLiveness ==
  \A n \in Nodes : Offline(n) ~> ~Offline(n) /\ Synced(n)  \* All missing filled via repair

====
