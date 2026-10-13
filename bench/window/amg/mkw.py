"""Weights for the AM seven-point certificate: symmetrise the LP weights, round to integers over SA = 10^8 (as
seven/sevenw.round_weights), find the local minima of the rounded functional with w = k_AM^2 on g0 <= g5.
Usage: mkw.py LP.npz OUT.npz [starts]"""
import sys, os, time, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "..", "seven"))
import amk, sevenw
sevenw.w = amk.w; sevenw.w1 = amk.w1; sevenw.w2 = amk.w2
from sevenw import Fun, symmetrise, round_weights, local_minima, Q, SA
H_AM = 0.6721883029 - 2e-9            # AM13 H (window-scope, trunc_runs.log), floored
def kappa(cN, bN, n=Q + 1):
    c = cN / SA; B = sum(bN) / SA; q = n - 1
    best = (0, 0)
    for m in range(2 * n, 2000):
        if c * (m - q) > 1: break
        best = max(best, ((H_AM - B * (m - q) / m) / (1 - c * (m - q) / m), m))
    return best
if __name__ == "__main__":
    d = np.load(sys.argv[1]); starts = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
    a, b = symmetrise(d['a'], d['b']); aN, bN = round_weights(a, b)
    Fr = Fun(np.array(aN, float) / SA, np.array(bN, float) / SA)
    t0 = time.time()
    mins = local_minima(Fr, starts=starts, keep=800, seed=1)
    vals = np.array([v for v, _ in mins]); X = np.array([x for _, x in mins])
    np.savez(sys.argv[2], aN=aN, bN=bN, mins=X, vals=vals)
    print(f"LP eps {float(d['eps']):.9f}; rounded min {vals[0]:.10f} at {np.round(X[0], 4)}; {len(vals)} minima, "
          f"within 1%: {(vals < vals[0] * 1.01).sum()}, 3%: {(vals < vals[0] * 1.03).sum()} ({time.time() - t0:.0f}s)")
    for delta in (0, 0.0005, 0.001, 0.0015, 0.002, 0.0025, 0.003, 0.01):
        cN = int(vals[0] * SA * (1 - delta)); k, m = kappa(cN, bN); print(f"  delta {delta}: cN {cN} m {m} kappa {k:.7f}")
    print("aN", aN); print("bN", bN)
    for v, x in list(zip(vals, X))[:12]: print(f"  {v:.10f} {np.round(x, 4)}")
