"""Local minima of the weighted seven-point functional for a window file (window-scope's rwin*.json: integer pair
weights aN over SA, pressures bN, numerators cnum), w = k^2 of that window (amk with AMWIN set to the same file).
Usage: AMWIN=rwin7.json mkwj.py rwin7.json OUT.npz [starts]"""
import sys, os, time, json, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
J = json.load(open(sys.argv[1]))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "..", {7: "seven", 8: "eight"}[J["n"]]))
import amk, sevenw
sevenw.w = amk.w; sevenw.w1 = amk.w1; sevenw.w2 = amk.w2
from sevenw import Fun, local_minima, Q, SA
assert J["n"] == Q + 1 and os.environ.get("AMWIN")
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
aN = [int(J["aN"][f"{i},{j}"]) for (i, j) in PAIRS]; bN = [int(x) for x in J["bN"]]
Fr = Fun(np.array(aN, float) / SA, np.array(bN, float) / SA)
starts = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
t0 = time.time()
mins = local_minima(Fr, starts=starts, keep=800, seed=1)
vals = np.array([v for v, _ in mins]); X = np.array([x for _, x in mins])
np.savez(sys.argv[2], aN=aN, bN=bN, mins=X, vals=vals)
print(f"eps_strong {J['eps_strong']:.10f}; rounded min {vals[0]:.10f} at {np.round(X[0], 4)}; {len(vals)} minima, "
      f"within 1%: {(vals < vals[0] * 1.01).sum()}, 3%: {(vals < vals[0] * 1.03).sum()} ({time.time() - t0:.0f}s)")
for v, x in list(zip(vals, X))[:8]: print(f"  {v:.10f} {np.round(x, 4)}")
