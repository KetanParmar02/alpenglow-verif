---- MODULE Rotor ----
EXTENDS FiniteSets, Random  \* Apalache for random sampling

VARIABLES shreds, relays  \* Imported

\* Stake-weighted relay sample (prob ~ Stake[n]/TotalStake)
RelaySample(slot) ==
  {n \in Nodes : RandomFair() < Stake[n] / TotalStake}  \* Abstract probabilistic

SendShreds(leader, slot, block) ==
  LET num_shreds == block.shreds  \* Erasure coding: k=10, n=20 say
  IN
  /\ shreds' = [shreds EXCEPT ![slot] = { [id |-> i, data |-> "shred_data"] : i \in 1..num_shreds }]
  /\ relays' = [relays EXCEPT ![slot] = RelaySample(slot)]
  /\ \A r \in @ : BroadcastShreds(r, shreds[slot], slot)

BroadcastShreds(relay, sset, slot) ==
  \* Flood to all honest nodes
  UNCHANGED <<shreds, relays>>  \* Delivery via network

\* Inv: Delivery with >80% stake
Inv_Delivery(slot) ==
  \A h \in HonestNodes : Cardinality({s \in shreds[slot] : Received(h, s)}) >= 8  \* Threshold for decoding
====
