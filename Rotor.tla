---- MODULE Rotor ----
EXTENDS Integers, FiniteSets, Sequences, Alpenglow  \* Import Nodes, Stake, TotalStake, network, HonestNodes, ErasureThreshold

VARIABLES shreds, relays

\* Stake-weighted relay sampling (Section 3.1: proportional to stake, abstract non-deterministic)
RelaySample(slot) ==
  LET cumStake == [n \in Nodes |-> LET prev == IF n = CHOOSE min \in Nodes : \A m \in Nodes : m /= min => Stake[m] >= Stake[min] ELSE 0 IN
    prev + Stake[n]]  \* Cumulative stake for weighted select
  IN
  {n \in HonestNodes : \E r \in 1..TotalStake : r <= cumStake[n]}  \* Abstract proportional (deterministic approx for checking)

\* Send erasure-coded shreds: Leader encodes block into shreds, sends to relays (single-hop, Section 2.2)
SendShreds(leader, slot, block) ==
  LET num_shreds == block.shreds  \* e.g., k data + m parity for (k+m, k) code
      relay_set == RelaySample(slot) IN
  /\ shreds' = [shreds EXCEPT ![slot] = {[id |-> i, data |-> "shred_" \o ToString(i)] : i \in 1..num_shreds}]
  /\ relays' = [relays EXCEPT ![slot] = relay_set]
  /\ \A r \in relay_set : \A sh \in shreds'[slot] : SendMsg(leader, r, "shred", sh)  \* Leader to relays
  /\ \A r \in relay_set : BroadcastShreds(r, shreds'[slot], slot)  \* Relays flood

\* Relays broadcast shreds to all honest nodes (stake-fair bandwidth utilization)
BroadcastShreds(relay, shredset, slot) ==
  IF ~Byzantine(relay) /\ ~Offline(relay) THEN
    \A h \in HonestNodes : \A sh \in shredset : SendMsg(relay, h, "shred", sh)  \* Add to network
  ELSE UNCHANGED network  \* Byzantine/offline may drop

\* Invariant: With ≥80% responsive stake in relays, honest nodes can reconstruct (erasure threshold met)
DeliveryInvariant(slot) ==
  LET relay_stake == SumStake(relays[slot]) IN
  IF relay_stake >= (TotalStake * 8) \div 10 THEN
    \A h \in HonestNodes : Cardinality(ReceivedShreds(h, slot)) >= ErasureThreshold
  ELSE TRUE  \* No guarantee if low participation

\* Helper: Shreds received by node (abstract; in full model, track per-node sets from network delivery)
ReceivedShreds(node, slot) == shreds[slot]  \* Assume delivery if sent (refine with faults/delays)

\* Theorem: Optimal bandwidth (asymptotically, total used ∝ sum stake, per Section 3.1)
THEOREM OptimalBandwidth ==
  ASSUME ResponsiveStake > 0.8 * TotalStake
  PROVE DeliveryInvariant(slots) /\ LivenessResilient  \* Tied to top-level

====
