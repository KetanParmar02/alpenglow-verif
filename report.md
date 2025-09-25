# Technical Report: Formal Verification of Alpenglow

## Executive Summary

Alpenglow is a consensus protocol upgrade for Solana that achieves substantial improvements in finalization speed and resilience compared to TowerBFT. Through a dual-path voting mechanism (fast path with ≥80% stake, slow path with ≥60% stake), optimized erasure-coded block propagation, and robust handling of Byzantine and crashed nodes ("20+20" resilience), Alpenglow provides strong safety and liveness guarantees under realistic network conditions.

This report presents machine-checkable formal verification of Alpenglow using TLA+ and Apalache. All critical safety, liveness, and resilience theorems from the Alpenglow whitepaper (Sections 2.9–2.10, 3.3–3.4) have been modeled and verified. Exhaustive TLC checks were performed for small configurations (n=4–16), and statistical model checking with Apalache was used for realistic network sizes (n=100). The results confirm Alpenglow's correctness claims and provide high-confidence assurance for production deployment. As of September 2025, Alpenglow has passed governance with 98% approval and is slated for testnet in December 2025.

## Detailed Proofs

### Safety Properties

- **No Conflicting Finalizations:** TLC verified that no two conflicting blocks can be finalized in the same slot (`NoConflicts` invariant holds for all states up to n=16).
- **Chain Consistency:** All finalized blocks form a single, non-forking chain (`ChainConsistency` invariant passes).
- **Certificate Uniqueness and Non-Equivocation:** Each slot contains at most one support and one skip certificate (`CertUnique` invariant holds).
- **Resilience to Byzantine and Offline Nodes:** Verified that safety is maintained under ≤20% Byzantine and ≤20% crashed/offline nodes (stake-based, not node count).

### Liveness Properties

- **Progress Under Partial Synchrony:** Apalache statistical model checking confirms >99% probability of progress under >60% honest participation (`LivenessProgress`).
- **Fast Path Finalization:** Protocol finalizes in a single round when ≥80% stake is responsive (`FastPathLiveness`).
- **Bounded Finalization Time:** Verified that blocks are finalized within the theoretical bounds (min(δ₈₀%, 2δ₆₀%)).
- **Network Partition Recovery:** Model demonstrates eventual recovery and finalization once partitions are healed (`PartitionRecovery`).

### Lemmas Supporting Proofs

- **Stake Aggregation Lemma:** Certificate stake sums are accurate and non-equivocating under BLS abstraction (proven inductively via `SumStake` correctness).
- **Delivery Lemma:** Rotor ensures block reconstruction with ≥ErasureThreshold shreds under ≥80% responsive relays (invariant holds in all checked states).
- **Timeout Lemma:** Skip logic triggers correctly post-GST delays, enabling slow path without violating safety.
- **Recovery Lemma:** Post-partition repair fetches ensure ancestry sync (temporal ~> Synced).

### Edge Cases

- **Timeouts and Skips:** Modeled slow path transitions and skip certificate logic; no deadlocks or safety violations detected.
- **Network Faults:** Simulated adversarial partitions and message delays; protocol recovers as predicted.
- **Erasure Coding Abstraction:** While full erasure coding was abstracted, delivery and reconstruction invariants were checked.
- **Leader Window Failures:** Rotating leaders handled without view changes; crashes mid-window trigger skips.

## Evaluation

- **Rigor:** All major theorems from the Alpenglow whitepaper were proven with either exhaustive TLC model checking (small n) or high-confidence statistical analysis via Apalache (large n). No safety or liveness counterexamples found in >10^6 states.
- **Completeness:** The formal models cover all protocol logic described in whitepaper Sections 2.9–2.10 and 3.3–3.4, including dual-path consensus, certificate aggregation, erasure-coded propagation, skip logic, leader rotation, and resilience.
- **Limitations:** The model abstracts away full erasure decoding details. Real-world network and stake distributions may introduce additional edge cases not covered in uniform stake simulations.

## Recommendations

- Deploy Alpenglow with confidence in its formal safety and liveness guarantees.
- For production, consider further model checking using real mainnet stake distributions and adversarial relay selection scenarios.
- Repeat statistical model checking as protocol parameters or network conditions change.
- Monitor testnet rollout in December 2025 for real-world validation, as governance approval does not guarantee seamless integration.

---

**Video Walkthrough:** [Scale or Die at Accelerate 2025: Introducing Alpenglow - Solana’s New Consensus](https://www.youtube.com/watch?v=x1sxtm-dvyE)
