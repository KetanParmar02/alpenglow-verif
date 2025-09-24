# Formal Verification of Solana Alpenglow Consensus Protocol

This repo provides a TLA+ formal specification and verification of Alpenglow, Solana's consensus upgrade. It verifies safety (no forks), liveness (progress under partial synchrony), and resilience ("20+20" faults) per the whitepaper.

## Setup
1. Install TLA+ Toolbox: https://github.com/tlaplus/tlaplus
2. Clone this repo.
3. Open `Alpenglow.tla` in Toolbox.

## Running Verification
- **Exhaustive Model Checking**: Run TLC on `MC.cfg` (4-16 nodes). Checks invariants in Proofs.tla.
- **Larger Sims**: Use Apalache with `apalache.cfg` for n=100.
- **Statistical**: `cd simulations && python run_sim.py` (requires NumPy; simulates stake dist).

## Key Files
- `Alpenglow.tla`: Composes modules.
- `Votor.tla`: Dual-path voting (80%/60% thresholds).
- `Rotor.tla`: Abstracted erasure-coded propagation.
- `Proofs.tla`: Safety/liveness invariants.

## Results
All core theorems verified (see report.md). No violations in small models.

License: Apache 2.0

# alpenglow-verif
Formal Verification of Solana Alpenglow: TLA+ spec models Votor's dual voting (80%/60% paths) &amp; abstracted Rotor propagation. Verifies safety (no conflicts), liveness (min(δ80%,2δ60%) finality), &amp; "20+20" resilience. TLC exhausts small nets; Apalache sims large. Open-source Apache 2.0 repo w/ proofs.
