import numpy as np
from scipy.stats import binom

n = 121

err_len = 60

err_set = np.sort(np.random.choice(n, err_len, replace=False))

print