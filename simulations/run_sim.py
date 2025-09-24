import numpy as np
import pandas as pd
from scipy import stats

# Load stake data
df = pd.read_csv('stake_data.csv')
stakes = df['stake'].values
total_stake = stakes.sum()

# Simulate 1000 runs: Finality time
def sim_finality(responsive_frac=0.8):
    responsive_stake = responsive_frac * total_stake
    if responsive_stake > 0.8 * total_stake:
        return np.random.normal(120, 30)  # Fast path ~120ms
    else:
        return np.random.normal(300, 50)  # Slow path ~300ms

times = [sim_finality() for _ in range(1000)]
print(f"Mean finality: {np.mean(times):.2f}ms")
print(f"95% CI: {stats.t.interval(0.95, len(times)-1, loc=np.mean(times), scale=stats.sem(times))}")
