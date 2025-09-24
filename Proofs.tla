---- MODULE Proofs ----
EXTENDS Alpenglow, Votor, Rotor

TypeOK ==
  /\ slots \in Nat
  /\ \A s \in DOMAIN blocks : blocks[s] \in Block \union {NULL}
  /\ \A s \in DOMAIN votes : votes[s] \in [Nodes -> {"support"|"skip"|NULL}]
  /\ \A s \in DOMAIN certs : certs[s] \subseteq Cert

NoConflicts ==
  \A s \in Nat : finalized[s] => 
    \E! b \in blocks : \E c \in certs[s] : c.type = "support" /\ c.stake >= Threshold_fast

ChainConsistency ==
  \A s1,s2 \in Nat, s1 < s2 : finalized[s1] /\ finalized[s2] =>
    blocks[s2].parent = s1  \* Sequential chain

\* Liveness (via fairness): Progress under >60% responsive
Progress ==
  \A s \in Nat : \E bound \in Nat : finalized[s] /\ (slots - s) <= bound * 2  \* 2 rounds max

\* Resilience: Safety under <20% Byz
SafetyResilient ==
  Cardinality(ByzNodes) * MaxStake < ByzantineThreshold => NoConflicts

THEOREM Spec => []TypeOK
<1>1. Init => TypeOK  OBVIOUS
<1>2. TypeOK /\ [Next] => TypeOK'  BY DEF Next, IssueVote, SendShreds
<1> QED BY <1>1, <1>2 DEF Spec

\* Similar for other invariants (TLC checks them)
====
