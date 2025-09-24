---- MODULE Alpenglow ----
EXTENDS TLC, FiniteSets, Integers, Sequences, Apalache  (* For bounded checking *)

CONSTANTS
  Nodes,                  \* Set of nodes
  Stake,                  \* [Nodes -> Nat] stake per node
  TotalStake,
  ByzantineThreshold,     \* 0.2 * TotalStake
  GST,                    \* Global Stabilization Time (ms)
  SlotTime,               \* Slot duration (ms)
  Delta80,                \* Fast path bound (150ms)
  Delta60                 \* Slow path round (200ms)

VARIABLES
  slots,                  \* Current slot number
  leaders,                \* Leader schedule [Nat -> Nodes]
  blocks,                 \* [Nat -> Block] or NULL
  votes,                  \* [Nat -> [Nodes -> {"support" | "skip" | NULL}]]
  certs,                  \* [Nat -> SET OF Cert]
  finalized,              \* [Nat -> BOOLEAN]
  network,                \* Pending messages
  shreds,                 \* [Nat -> SET OF Shred]
  relays                   \* [Nat -> SET OF Nodes]

\* Types
Block == [hash: STRING, parent: Nat, shreds: Nat]
Shred == [id: Nat, data: STRING]
Cert == [type: {"support", "skip"}, slot: Nat, stake: Nat, sig: STRING]
Msg == [from: Nodes, to: Nodes, type: {"block", "vote", "cert"}, content: ANY, ts: Nat]

HonestNodes == {n \in Nodes : Stake[n] > 0}  \* Assume all staked are honest unless Byzantine
ByzNodes == {}  \* Parameterize for faults

ASSUME
  /\ TotalStake = Sum(Stake)
  /\ ByzantineThreshold = TotalStake * 2 \div 10
  /\ Cardinality(Nodes) >= 4
  /\ GST = 100
  /\ SlotTime = 400
  /\ Delta80 = 150
  /\ Delta60 = 200
  /\ HonestStake == TotalStake - ByzantineThreshold > TotalStake * 6 \div 10  \* >60%

INCLUDE Votor
INCLUDE Rotor
INCLUDE Network

Init ==
  /\ slots = 0
  /\ leaders = [n \in Nat -> CHOOSE l \in Nodes : TRUE]  \* VRF-abstracted
  /\ blocks = [n \in Nat |-> NULL]
  /\ votes = [n \in Nat |-> [m \in Nodes |-> NULL]]
  /\ certs = [n \in Nat |-> {}]
  /\ finalized = [n \in Nat |-> FALSE]
  /\ network = {}
  /\ shreds = [n \in Nat |-> {}]
  /\ relays = [n \in Nat |-> {}]

Next ==
  /\ slots' = slots + 1
  /\ LET leader == leaders[slots] IN
    /\ Rotor!SendShreds(leader, slots, ConstructBlock())  \* Abstract block creation
    /\ \A n \in Nodes : IF n \in HonestNodes THEN Votor!IssueVote(n, slots, blocks[slots])
    /\ Votor!AggregateCert(slots)
    /\ IF slots > 0 THEN Votor!SlowPath(slots)
    /\ Network!DeliverMsgs(network)
    /\ UNCHANGED finalized  \* Updated in AggregateCert

Spec == Init /\ [][Next]_<<slots, blocks, votes, certs, finalized, network, shreds, relays>>
Invariants == {TypeOK, NoConflicts, ChainConsistency}  \* From Proofs.tla

THEOREM Spec => []Invariants
<1>1. Init => Invariants  BY DEF Init, TypeOK, NoConflicts, ChainConsistency
<1>2. Invariants /\ [Next] => Invariants'  BY DEF Next, Votor!IssueVote, Rotor!SendShreds
<1> QED
  BY <1>1, <1>2 DEF Spec

====
\* ConstructBlock: Placeholder
ConstructBlock() == [hash |-> "block_hash", parent |-> slots-1, shreds |-> 10]
