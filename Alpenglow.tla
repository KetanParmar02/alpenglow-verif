---- MODULE Alpenglow ----
EXTENDS TLC, FiniteSets, Integers, Sequences, Apalache, RealTime

CONSTANTS
  Nodes,                  \* Set of nodes
  Stake,                  \* [Nodes -> Nat] stake per node
  TotalStake,             \* Sum of all stakes
  ByzantineThreshold,     \* 0.2 * TotalStake for Byzantine stake
  OfflineThreshold,       \* 0.2 * TotalStake for offline stake
  GST,                    \* Global Stabilization Time (ms)
  SlotTime,               \* Slot duration (ms)
  Delta80,                \* Fast path bound (150ms)
  Delta60                 \* Slow path round (200ms)
  ErasureThreshold        \* Shreds needed for decoding (e.g., 2/3 of shreds)

VARIABLES
  now,                    \* Global clock for real-time (from RealTime)
  slots,                  \* Current slot number
  leaders,                \* [Nat -> Nodes], VRF-based leader schedule
  blocks,                 \* [Nat -> Block \cup {NULL}]
  votes,                  \* [Nat -> [Nodes -> {"support", "skip", NULL}]]
  certs,                  \* [Nat -> SUBSET Cert]
  finalized,              \* [Nat -> BOOLEAN]
  network,                \* Set of pending messages
  shreds,                 \* [Nat -> SUBSET Shred]
  relays,                 \* [Nat -> SUBSET Nodes]
  missingShreds           \* [Nodes -> SUBSET (Nat \X Shred)], for repair

\* Types
Block == [hash: STRING, parent: Nat, shreds: Nat]
Shred == [id: Nat, data: STRING]
Cert == [type: {"support", "skip"}, slot: Nat, stake: Nat, sig: STRING]  \* BLS aggregate
Msg == [from: Nodes, to: Nodes, type: {"shred", "vote", "cert", "repair"}, content: ANY, ts: Nat]

\* Derived sets
ByzantineStake == LET ByzSet == {n \in Nodes : Byzantine(n)} IN Sum({Stake[m] : m \in ByzSet})
OfflineStake == LET OffSet == {n \in Nodes : Offline(n)} IN Sum({Stake[m] : m \in OffSet})
HonestNodes == {n \in Nodes : ~Byzantine(n) /\ ~Offline(n)}
ResponsiveStake == TotalStake - OfflineStake  \* For liveness

ASSUME
  /\ TotalStake = Sum(Stake)
  /\ ByzantineThreshold = (TotalStake * 2) \div 10
  /\ OfflineThreshold = (TotalStake * 2) \div 10
  /\ ByzantineStake <= ByzantineThreshold
  /\ OfflineStake <= OfflineThreshold
  /\ Cardinality(Nodes) >= 4
  /\ GST = 100
  /\ SlotTime = 400
  /\ Delta80 = 150
  /\ Delta60 = 200
  /\ ErasureThreshold = 8  \* Example: 8/10 shreds for decoding

\* Byzantine/Offline predicates (parameterized for model checking)
Byzantine(n) == FALSE  \* Override in cfg for faults
Offline(n) == FALSE

\* Include sub-modules (assume defined separately with fixes)
INCLUDE Votor  \* Dual paths, IssueVote (support/skip based on timeout), AggregateCert (80%/60%)
INCLUDE Rotor  \* SendShreds with stake-weighted RelaySample, Inv_Delivery (>ErasureThreshold)
INCLUDE Network  \* DeliverMsgs with ts + GST <= now, Byzantine drops/delays

Init ==
  /\ now = 0
  /\ slots = 0
  /\ leaders = [s \in Nat |-> StakeWeightedLeader(s)]  \* Abstract VRF: stake-proportional
  /\ blocks = [s \in Nat |-> NULL]
  /\ votes = [s \in Nat |-> [n \in Nodes |-> NULL]]
  /\ certs = [s \in Nat |-> {}]
  /\ finalized = [s \in Nat |-> FALSE]
  /\ network = {}
  /\ shreds = [s \in Nat |-> {}]
  /\ relays = [s \in Nat |-> {}]
  /\ missingShreds = [n \in Nodes |-> {}]

\* Next: Advance slot, leader actions, concurrent voting/aggregation, delivery, repair
Next ==
  /\ now' \in now .. now + SlotTime  \* Bounded time advance (RealTime)
  /\ slots' = slots + 1
  /\ LET slot == slots'
         leader == leaders[slot] IN
       /\ IF ~Byzantine(leader) /\ ~Offline(leader)
          THEN /\ blocks' = [blocks EXCEPT ![slot] = ConstructBlock(slot)]
               /\ Rotor!SendShreds(leader, slot, blocks'[slot])  \* Updates shreds, relays, network
          ELSE UNCHANGED <<blocks, shreds, relays>>
       /\ \A n \in HonestNodes: Votor!IssueVote(n, slot, blocks[slot], now)  \* Support if on-time, else skip
       /\ Votor!AggregateCert(slot)  \* Concurrent 80% fast and 60% slow
       /\ Network!DeliverMsgs(network')  \* Updates local states (votes, shreds)
       /\ RepairMissing  \* On-demand fetches for missingShreds
       /\ RTBound(Delta80, Votor!FastPathFinalized(slot))  \* Bound fast path
       /\ RTBound(2 * Delta60, Votor!SlowPathFinalized(slot))  \* Bound slow path
       /\ UNCHANGED <<leaders, finalized>>  \* Finalized updated in AggregateCert

\* Abstract block creation (Section 2.7)
ConstructBlock(s) == [hash |-> "block_" \o ToString(s), parent |-> s-1, shreds |-> 10]

\* Repair action (Section 2.8): Fetch missing shreds from peers
RepairMissing ==
  \A n \in HonestNodes:
    \A <sl, sh> \in missingShreds[n]:
      \E p \in HonestNodes \ {n}: HasShred(p, sl, sh) =>
        /\ SendRepairRequest(n, p, sl, sh)  \* Add to network
        /\ missingShreds' = [missingShreds EXCEPT ![n] = @ \ {<<sl, sh>>}]
        /\ shreds' = [shreds EXCEPT ![sl] = @ \union {sh}]  \* Upon delivery

\* Stake-weighted leader (abstract VRF, Section 1.1)
StakeWeightedLeader(s) == CHOOSE l \in Nodes: Stake[l] > 0  \* Probabilistic in full model

\* Spec with fairness for liveness (Section 2.10)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ SF_vars(Votor!AggregateCert) /\ RTNowBound(0, SlotTime)

vars == <<now, slots, leaders, blocks, votes, certs, finalized, network, shreds, relays, missingShreds>>

\* Safety: No two conflicting finalized blocks per slot (Theorem 2.9.1)
NoConflicts ==
  \A s \in Nat: finalized[s] =>
    \E! b: blocks[s] = b /\ \E c \in certs[s]: c.type = "support" /\ c.stake >= 0.8 * TotalStake

\* Safety: Chain consistency under ≤20% Byzantine (Theorem 2.9.2)
ChainConsistency ==
  \A s \in Nat: finalized[s+1] => blocks[s+1].parent = s /\ ByzantineStake <= ByzantineThreshold

\* Safety: Certificate uniqueness/non-equivocation (Section 2.4)
CertUnique ==
  \A s \in Nat: Cardinality(certs[s]) <= 1 /\ \A c \in certs[s]: ~ \E n: Equivocates(n, c)

\* Liveness: Progress under partial synchrony >60% honest (Theorem 2.10.1)
Progress ==
  ResponsiveStake > 0.6 * TotalStake ~> \A s \in Nat: finalized[s]

\* Liveness: Fast path in 1 round with >80% responsive (Claim)
FastPathLiveness ==
  ResponsiveStake > 0.8 * TotalStake ~> \A s \in Nat: finalized[s] /\ RTBound(Delta80, finalized[s])

\* Resilience: Safety with ≤20% Byzantine
SafetyResilient ==
  ByzantineStake <= ByzantineThreshold => []NoConflicts /\ []ChainConsistency /\ []CertUnique

\* Resilience: Liveness with ≤20% non-responsive
LivenessResilient ==
  OfflineStake <= OfflineThreshold /\ ResponsiveStake > 0.6 * TotalStake => Progress

\* Resilience: Network partition recovery (Section 3.3)
Recovery ==
  \A n \in Nodes: Partitioned(n) ~> Synced(n)  \* Via repair

Invariants == NoConflicts /\ ChainConsistency /\ CertUnique
Temporal == Progress /\ FastPathLiveness /\ SafetyResilient /\ LivenessResilient /\ Recovery

THEOREM Spec => []Invariants /\ Temporal
\* Hierarchical proofs (lemmas in Proofs.tla)

====
