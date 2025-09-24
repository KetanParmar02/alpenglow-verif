---- MODULE Votor ----
EXTENDS Integers, FiniteSets

VARIABLES votes, certs, finalized  \* Imported from Alpenglow

Threshold_fast == 0.8 * TotalStake
Threshold_slow == 0.6 * TotalStake
Threshold_skip == 0.6 * TotalStake

RECURSIVE SumStake(_)
SumStake(S) == IF S = {} THEN 0 ELSE HEAD(S) + SumStake(TAIL(S))

IssueVote(node, slot, block) ==
  LET timeout == slot * SlotTime + GST
  IN
  IF block # NULL /\ NOW < timeout THEN  \* On time
    /\ votes' = [votes EXCEPT ![slot][node] = "support"]
    /\ SendVote(node, "support", block.hash, slot)
  ELSE
    /\ votes' = [votes EXCEPT ![slot][node] = "skip"]
    /\ SendVote(node, "skip", slot)

AggregateCert(slot) ==
  LET supp_stake == SumStake({Stake[n] : n \in DOMAIN votes[slot], votes[slot][n] = "support"})
      skip_stake == SumStake({Stake[n] : n \in DOMAIN votes[slot], votes[slot][n] = "skip"})
  IN
  /\ IF supp_stake >= Threshold_fast THEN
       /\ certs' = certs \union { [type |-> "support", slot |-> slot, stake |-> supp_stake, sig |-> "BLS_agg"] }
       /\ finalized' = [finalized EXCEPT ![slot] = TRUE]
    ELSE UNCHANGED <<certs, finalized>>
  /\ IF skip_stake >= Threshold_skip THEN
       certs' = certs \union { [type |-> "skip", slot |-> slot, stake |-> skip_stake, sig |-> "BLS_agg"] }

SlowPath(slot) ==
  LET round2_supp == SumStake({Stake[n] : n \in DOMAIN votes[slot], votes[slot][n] = "support"})  \* Round 2 aggregate
  IN
  IF round2_supp >= Threshold_slow /\ ~\E c \in certs[slot] : c.type = "skip" THEN
    finalized' = [finalized EXCEPT ![slot] = TRUE]

\* SendVote: Abstract
SendVote(n, type, content, slot) == UNCHANGED <<votes, certs>>  \* Broadcast via network
====
