---- MODULE Votor ----
EXTENDS Integers, FiniteSets, Sequences, Alpenglow  \* Import Nodes, Stake, TotalStake, now, GST

VARIABLES votes, certs, finalized  \* Shared with Alpenglow

Threshold_fast == (TotalStake * 8) \div 10
Threshold_slow == (TotalStake * 6) \div 10
Threshold_skip == (TotalStake * 6) \div 10

\* Sum stake for a set of nodes
SumStake(nodes) == LET stakes == {Stake[n] : n \in nodes} IN
  IF stakes = {} THEN 0 ELSE LET s == CHOOSE x \in stakes : TRUE IN s + SumStake(stakes \ {s})

\* Issue vote: Support if block received on time (timeout based on GST/PoH abstract), else skip
IssueVote(node, slot, block, current_time) ==
  LET timeout == slot * SlotTime + GST IN
  IF block # NULL /\ current_time <= timeout THEN
    /\ votes' = [votes EXCEPT ![slot][node] = "support"]
    /\ SendMsg(node, Nodes, "vote", [type |-> "support", hash |-> block.hash, slot |-> slot])
  ELSE
    /\ votes' = [votes EXCEPT ![slot][node] = "skip"]
    /\ SendMsg(node, Nodes, "vote", [type |-> "skip", slot |-> slot])

\* Aggregate certificates concurrently for support/skip (BLS multi-sig abstraction)
AggregateCert(slot) ==
  LET supp_nodes == {n \in Nodes : votes[slot][n] = "support"}
      supp_stake == SumStake(supp_nodes)
      skip_nodes == {n \in Nodes : votes[slot][n] = "skip"}
      skip_stake == SumStake(skip_nodes) IN
  /\ IF supp_stake >= Threshold_fast /\ ~\E c \in certs[slot] : c.type = "support_fast" THEN
       /\ certs' = [certs EXCEPT ![slot] = @ \union {[type |-> "support_fast", slot |-> slot, stake |-> supp_stake, sig |-> "BLS_agg"]}]
       /\ finalized' = [finalized EXCEPT ![slot] = TRUE]  \* Fast path finalizes immediately
     ELSE UNCHANGED <<certs, finalized>>
  /\ IF supp_stake >= Threshold_slow /\ ~\E c \in certs[slot] : c.type = "support_slow" THEN
       certs' = [certs EXCEPT ![slot] = @ \union {[type |-> "support_slow", slot |-> slot, stake |-> supp_stake, sig |-> "BLS_agg"]}]
     ELSE UNCHANGED certs
  /\ IF skip_stake >= Threshold_skip /\ ~\E c \in certs[slot] : c.type = "skip" THEN
       certs' = [certs EXCEPT ![slot] = @ \union {[type |-> "skip", slot |-> slot, stake |-> skip_stake, sig |-> "BLS_agg"]}]
     ELSE UNCHANGED certs

\* Slow path finalization: Confirm with 60% if no skip cert (after extra round delay)
SlowPathFinalization(slot) ==
  LET supp_stake == SumStake({n \in Nodes : votes[slot][n] = "support"}) IN
  IF supp_stake >= Threshold_slow /\ ~\E c \in certs[slot] : c.type = "skip" THEN
    finalized' = [finalized EXCEPT ![slot] = TRUE]
  ELSE UNCHANGED finalized

\* Helper: Check if fast path certified
HasFastCert(slot) ==
  \E c \in certs[slot] : c.type = "support_fast" /\ c.stake >= Threshold_fast

\* Helper: Check if slow path certified
HasSlowCert(slot) ==
  \E c \in certs[slot] : c.type = "support_slow" /\ c.stake >= Threshold_slow

\* Invariant: Certificate uniqueness/non-equivocation (BLS prevents duplicates/equivocation)
CertUniqueness ==
  \A s \in Nat : Cardinality(certs[s]) <= 3 /\  \* One each for fast, slow, skip
    ~\E c1, c2 \in certs[s] : c1 # c2 /\ c1.type = c2.type  \* No duplicates per type

\* Abstract send (broadcast vote msgs)
SendMsg(from, to_set, msg_type, content) ==
  network' = network \union {[from |-> from, to |-> t, type |-> msg_type, content |-> content, ts |-> now] : t \in to_set}

====
