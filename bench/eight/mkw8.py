"""Weights for the eight-point certificate: symmetrise the LP weights, round to integers over SA = 10^8, find the local
minima of the rounded functional on the half-space g0 <= g6.  Usage: mkw8.py LP.npz OUT.npz [starts]"""
import sys, time, numpy as np
from fractions import Fraction as F
sys.path.insert(0, '.')
from sevenw import Fun, symmetrise, round_weights, local_minima, Q, SA
d = np.load(sys.argv[1]); starts = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
a, b = symmetrise(d['a'], d['b']); aN, bN = round_weights(a, b)
Fr = Fun(np.array(aN, float) / SA, np.array(bN, float) / SA)
t0 = time.time()
mins = local_minima(Fr, starts=starts, keep=800, seed=1)
vals = np.array([v for v, _ in mins]); X = np.array([x for _, x in mins])
np.savez(sys.argv[2], aN=aN, bN=bN, mins=X, vals=vals)
n = Q + 1; H_lo = F(3, 2) - F(8274993018, 10**10); B = sum(F(x, SA) for x in bN)
def kappa(cN):
    c = F(cN, SA); m = (n - 1) + int(1 / c)
    return float((m * H_lo - B * (m - (n - 1))) / (m - c * (m - (n - 1)))), m
print(f"LP eps* {float(d['lower']):.8f}; rounded min {vals[0]:.10f}; {len(vals)} minima, within 1%: {(vals < vals[0] * 1.01).sum()}, 3%: {(vals < vals[0] * 1.03).sum()} ({time.time() - t0:.0f}s)")
for delta in (0, 0.0005, 0.001, 0.002, 0.003):
    cN = int(vals[0] * SA * (1 - delta)); k, m = kappa(cN); print(f"  delta {delta}: cN {cN} m {m} kappa {k:.7f}")
print("aN", aN); print("bN", bN)
