# alpenglow-verif
Formal Verification of Solana Alpenglow: TLA+ spec models Votor's dual voting (80%/60% paths) &amp; abstracted Rotor propagation. Verifies safety (no conflicts), liveness (min(δ80%,2δ60%) finality), &amp; "20+20" resilience. TLC exhausts small nets; Apalache sims large. Open-source Apache 2.0 repo w/ proofs.
