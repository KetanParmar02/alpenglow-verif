import numpy as np
import pandas as pd
from scipy import stats

# Load stake data (assume full CSV without ellipsis; sort for realistic faults)
df = pd.read_csv('stake_data.csv')
df = df.sort_values('stake', ascending=False).reset_index(drop=True)  # Sort descending for stake-based faults
stakes = df['stake'].values
total_stake = stakes.sum()
n_nodes = len(stakes)

# "20+20" resilience: Select top stake for Byzantine/offline (adversary targets high-stake)
byz_frac = 0.2
offline_frac = 0.2
byz_n = int(byz_frac * n_nodes)
offline_n = int(offline_frac * n_nodes)
byz_indices = np.arange(byz_n)  # Top stake
offline_indices = np.arange(byz_n, byz_n + offline_n)
responsive_indices = np.arange(byz_n + offline_n, n_nodes)

byz_stake = stakes[byz_indices].sum()
offline_stake = stakes[offline_indices].sum()
responsive_stake = stakes[responsive_indices].sum()

print(f"Total nodes: {n_nodes}")
print(f"Total stake: {total_stake}")
print(f"Responsive stake: {responsive_stake} ({responsive_stake/total_stake:.2f})")
print(f"Byzantine stake: {byz_stake} ({byz_stake/total_stake:.2f})")
print(f"Offline stake: {offline_stake} ({offline_stake/total_stake:.2f})")

# Simulate 1000 runs: Finality time with dual-path (fast ≥80%, slow ≥60%, stall <60%)
# Add partial synchrony noise (GST ~100ms uniform)
def sim_finality(responsive_frac):
    gst_delay = np.random.uniform(0, 100)  # Partial synchrony delay
    if responsive_frac >= 0.8:
        # Fast path: 1 round, ~120ms (std 30ms), bound <=150ms
        time = np.random.normal(120, 30) + gst_delay
        return min(time, 150)
    elif responsive_frac >= 0.6:
        # Slow path: 2 rounds, ~300ms (std 50ms), bound <=400ms
        time = np.random.normal(300, 50) + gst_delay
        return min(time, 400)
    else:
        # No progress under partial synchrony: Stall/timeout
        return 1000  # Arbitrary large for failure

responsive_frac = responsive_stake / total_stake
times = [sim_finality(responsive_frac) for _ in range(1000)]
mean_finality = np.mean(times)
ci_95 = stats.t.interval(0.95, len(times)-1, loc=mean_finality, scale=stats.sem(times))

print(f"Mean finality: {mean_finality:.2f} ms")
print(f"95% CI: ({ci_95[0]:.2f} ms, {ci_95[1]:.2f} ms)")
print(f"Fraction fast path (<200ms): {np.mean(np.array(times) < 200):.2f}")
print(f"Fraction stalled (>600ms): {np.mean(np.array(times) > 600):.2f}")

# Histogram for latency (presentation-inspired)
try:
    import matplotlib.pyplot as plt
    plt.hist(times, bins=30, color='skyblue')
    plt.title("Alpenglow Finality Time Simulation under '20+20' Resilience")
    plt.xlabel("Finality time (ms)")
    plt.ylabel("Frequency")
    plt.axvline(150, color='green', linestyle='--', label='δ80% bound')
    plt.axvline(400, color='orange', linestyle='--', label='2δ60% bound')
    plt.legend()
    plt.show()
except ImportError:
    print("Matplotlib not available for histogram.")
