# Alpenglow-Verif: Running Instructions

This guide explains how to run verification, model checking, and simulations for the [`KetanParmar02/alpenglow-verif`](https://github.com/KetanParmar02/alpenglow-verif) repo.

---

## 1. **Prerequisites**

### A. **TLA+ Tools**
- **TLA+ Toolbox**: For editing and running specs.
- **TLC Model Checker**: For small exhaustive checks (`MC.cfg`).
  - **Download:** [TLA+ Toolbox](https://github.com/tlaplus/tlaplus/releases)

### B. **Apalache Model Checker**
- For bounded, large-scale simulations (`apalache.cfg`).
  - **Install via Docker (recommended):**
    ```bash
    docker pull palach/apalache
    ```
  - Or [see Apalache docs](https://apalache.informal.systems/docs/intro.html#installation)

### C. **Python & Libraries** (for simulations)
- **Python 3.8+**
- **Required libraries:**  
  - `numpy`
  - `pandas`
- **Install:**
    ```bash
    pip install numpy pandas
    ```

---

## 2. **Folder Structure Overview**

- `Alpenglow.tla` – Main TLA+ spec (imports Votor, Rotor, Network).
- `Votor.tla`, `Rotor.tla`, `Network.tla` – Submodules.
- `Proofs.tla` – Formal proofs (Safety, Liveness, Resilience).
- `MC.cfg` – TLC config for small exhaustive checks.
- `apalache.cfg` – Apalache config for bounded simulations.
- `report.md` – Detailed proofs/results.
- `simulations/run_sim.py` – Python simulation script.
- `simulations/stake_data.csv` – Example stake distribution.

---

## 3. **Running TLA+ Model Checking**

### A. **With TLC (Small Exhaustive Checks)**
1. Open `Alpenglow.tla` in TLA+ Toolbox.
2. Load `MC.cfg` as the model configuration.
3. Run TLC (`Model > Run Model`).

### B. **With Apalache (Bounded Model Checking)**
1. Ensure Apalache is installed.
2. Run in terminal:
    ```bash
    docker run -v $PWD:/data palach/apalache check --config apalache.cfg Alpenglow.tla
    ```
    Or with local install:
    ```bash
    apalache check --config apalache.cfg Alpenglow.tla
    ```

---

## 4. **Running Python Simulations**

1. **Install dependencies:**  
    ```bash
    pip install numpy pandas
    ```
2. **Run simulation:**  
    ```bash
    cd simulations
    python run_sim.py
    ```
   - Uses `stake_data.csv` for input data.
   - Outputs finality statistics and analysis to the console.

---

## 5. **Viewing Proofs and Results**

- Read `report.md` for theorems, lemmas, and evaluation results.
- For TLA+ proof details, see `Proofs.tla`.

---

## 6. **Summary of Tools/Libraries Needed**

| Purpose                | Tool/Library       | Install/Download                     |
|------------------------|-------------------|--------------------------------------|
| TLA+ editing/checking  | TLA+ Toolbox, TLC | [TLA+ Toolbox](https://github.com/tlaplus/tlaplus/releases) |
| Bounded Model Checking | Apalache           | `docker pull palach/apalache` or [Apalache Docs](https://apalache.informal.systems/docs/intro.html#installation) |
| Python simulations     | Python 3.8+, numpy, pandas | `pip install numpy pandas`           |

---

## 7. **References**

- [TLA+ Documentation](http://lamport.azurewebsites.net/tla/tla.html)
- [Apalache Model Checker](https://apalache.informal.systems/)
- [NumPy](https://numpy.org/)
- [Pandas](https://pandas.pydata.org/)

---

**If you encounter issues or need more help, check `report.md` or open an Issue in the repository.**
