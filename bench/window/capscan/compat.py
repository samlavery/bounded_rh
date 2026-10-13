"""min over gaps of the average of k overlapping 8-point windows of PC8C5BF's functional F (rwin8.json weights,
R8 kernel), k = 1, 2, 3: how much of the local-functional slack L3 overlapping-window compatibility could recover
(the mechanism of Gebendorfer's three-window gate, txt:142-147).  Double precision, multistart L-BFGS-B."""
import json, math, itertools, time
import numpy as np
from scipy.optimize import minimize
from slack import W, bN, aN, cc
pairs = [(a, b, wt) for (a, b), wt in aN.items() if wt]
def F(g):                       # 7 gaps
    x = np.concatenate([[0.0], np.cumsum(g)])
    return float(np.dot(bN, g) + sum(wt * W(np.array([x[b] - x[a]]))[0] for a, b, wt in pairs))
def Fk(G, k):
    return sum(F(G[s:s + 7]) for s in range(k)) / k
t0 = time.time(); rng = np.random.default_rng(5)
for k in (1, 2, 3):
    n = 6 + k; best = (np.inf, None)
    starts = [np.array(p) for p in itertools.product((1.04, 1.97), repeat=n)]
    starts += [rng.uniform(0.3, 3.0, n) for _ in range(200)]
    for s in starts:
        r = minimize(lambda G: Fk(G, k), s, method='L-BFGS-B', bounds=[(0, 6)] * n)
        if r.fun < best[0]: best = (r.fun, r.x)
    print('k = %d windows: min avg F = %.9f  (c = %.9f; excess %.3f%%) at %s (%.0fs)'
          % (k, best[0], cc, 100 * (best[0] / cc - 1), np.round(best[1], 3), time.time() - t0), flush=True)
