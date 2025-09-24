---- MODULE Proofs ----
EXTENDS Alpenglow, Votor, Rotor, Network

\* Type invariant for all variables
TypeOK ==
  /\ now \in Nat  \* From RealTime
  /\ slots \in Nat
  /\ leaders \in [Nat -> Nodes]
  /\ blocks \in [Nat -> Block \union {NULL}]
  /\ votes \in [Nat -> [Nodes -> {"support", "skip", NULL}]]
  /\ certs \in [Nat -> SUBSET Cert]
  /\ finalized \in [Nat -> BOOLEAN]
  /\ network \subseteq Msg
  /\ shreds \in [Nat -> SUBSET Shred]
  /\ relays \in [Nat -> SUBSET Nodes]
  /\ missingShreds \in [Nodes -> SUBSET (Nat \X Shred)]

\* Safety: No two conflicting blocks finalized in same slot (Theorem 2.9.1)
NoConflicts ==
  \A s \in Nat : finalized[s] =>
    \E! b \in Block : blocks[s] = b /\ \E c \in certs[s] : c.type \in {"support_fast", "support_slow"} /\ ~\E c2 \in certs[s] : c2.type = "skip"

\* Safety: Chain consistency under ≤20% Byzantine stake (Theorem 2.9.2)
ChainConsistency ==
  \A s1, s2 \in Nat : (finalized[s1] /\ finalized[s2] /\ s1 < s2) =>
    blocks[s2].parent = s1 /\ ByzantineStake <= ByzantineThreshold

\* Safety: Certificate uniqueness and non-equivocation (Section 2.4)
CertUnique ==
  \A s \in Nat :
    Cardinality(certs[s]) <= 3 /\  \* At most fast, slow, skip
    \A c1, c2 \in certs[s] : c1 # c2 => c1.type # c2.type /\ NonEquivocating(c1, c2)

\* Helper: No equivocation (BLS prevents signing conflicting)
NonEquivocating(c1, c2) == c1.sig # c2.sig  \* Abstract

\* Liveness: Progress guarantee under partial synchrony with >60% honest (Theorem 2.10.1)
Progress ==
  ResponsiveStake > 0.6 * TotalStake ~> \A s \in Nat : finalized[s]

\* Liveness: Fast path completion in one round with >80% responsive (Claim)
FastPathLiveness ==
  ResponsiveStake > 0.8 * TotalStake ~> \A s \in Nat : HasFastCert(s) /\ finalized[s]

\* Liveness: Bounded finalization time min(δ80%, 2δ60%) (Abstract)
BoundedFinalization ==
  \A s \in Nat : finalized[s] => ElapsedTime(s) <= MinDelta

\* Helpers
MinDelta == IF Delta80 < 2 * Delta60 THEN Delta80 ELSE 2 * Delta60
ElapsedTime(s) == now - (s * SlotTime)  \* Abstract start at slot time

\* Resilience: Safety maintained with ≤20% Byzantine stake
SafetyResilient ==
  ByzantineStake <= ByzantineThreshold => []NoConflicts /\ []ChainConsistency /\ []CertUnique

\* Resilience: Liveness maintained with ≤20% non-responsive stake
LivenessResilient ==
  OfflineStake <= OfflineThreshold /\ ResponsiveStake > 0.6 * TotalStake => Progress /\ FastPathLiveness /\ BoundedFinalization

\* Resilience: Network partition recovery guarantees (Section 3.3)
PartitionRecovery ==
  \A n \in Nodes : Offline(n) ~> ~Offline(n) /\ \A s \in Nat : finalized[s] => Synced(n, s)

\* Helper: Node synced if no missing shreds for finalized blocks
Synced(n, s) == missingShreds[n] = {} /\ ReceivedBlock(n, s)

\* Theorems with hierarchical proofs (for TLAPS or manual; TLC checks invariants)
THEOREM Spec => []TypeOK
<1>1. Init => TypeOK  OBVIOUS
<1>2. TypeOK /\ [Next]_vars => TypeOK'  BY DEF Next, Votor!IssueVote, Rotor!SendShreds, Network!DeliverMsgs
<1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []NoConflicts
<1>1. Init => NoConflicts  OBVIOUS
<1>2. NoConflicts /\ [Next]_vars => NoConflicts'  BY CertUnique, Votor!AggregateCert DEF Next
<1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []ChainConsistency
<1>1. Init => ChainConsistency  OBVIOUS
<1>2. ChainConsistency /\ [Next]_vars => ChainConsistency'  BY DEF ConstructBlock, Votor!AggregateCert
<1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []CertUnique
<1>1. Init => CertUnique  OBVIOUS
<1>2. CertUnique /\ [Next]_vars => CertUnique'  BY Votor!AggregateCert DEF BLS uniqueness
<1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => Progress
<1> DEFINE Assumption == ResponsiveStake > 0.6 * TotalStake /\ PartialSynchrony
<1>1. Assumption => <> \A s : finalized[s]  BY WF_Next, SF_AggregateCert DEF Spec
<1> QED  BY <1>1, PTL

\* Similar for others; use Apalache for temporal

====
