"""bridge-port 2026-10-10, ANATOMY.md §3: the end-gap sub-frame of a 9-point weight vector.
Decoupling the last point (gap 7 >= g*): F(g_0..g_7) >= b_7 g* + F_L(g_0..g_6), F_L = the 8-point sub-frame functional on
points 0..7 (pairs (i, j) with j <= 7, pressures b_0..b_6); cross pairs (i, 8) dropped (w >= 0).  The sub-certificate needs
F_L >= cN - b_7 g* (units 1e-8).  This script (1) finds the global minimum of F_L (lattice starts {0.5,1.04,1.97,2.91}^7 plus
random, L-BFGS-B), (2) writes, per g*, the sizer json (n = 8, eps_strong set so that DELTA = 0 gives cN_L) and reports the
margin min F_L / cN_L - 1.  Usage: python3 subframe9.py WEIGHTS.json DELTA OUTPREFIX g1 g2 ..."""
import sys, os, json, itertools
import numpy as np
from scipy.optimize import minimize
os.environ.setdefault("AMWIN", "/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json")
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/window/amg")
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/pyr")
import amk
WJ, DELTA, PRE = sys.argv[1], float(sys.argv[2]), sys.argv[3]; GS = [float(x) for x in sys.argv[4:]]
J = json.load(open(WJ)); n = J["n"]; assert n == 9
cN = int(J["eps_strong"] * 1e8 * (1 - DELTA))
m = 8; Q = 7
P = [(i, j) for i in range(m) for j in range(i + 1, m)]
aN = {f"{i},{j}": int(J["aN"][f"{i},{j}"]) for (i, j) in P}; bN = [int(x) for x in J["bN"][:Q]]
a = np.array([aN[f"{i},{j}"] for (i, j) in P]) / 1e8; b = np.array(bN) / 1e8
INC = np.zeros((len(P), Q))
for t, (i, j) in enumerate(P): INC[t, i:j] = 1
def fg(g):
    s = INC @ g; return float(b @ g + a @ amk.w(s)), b + INC.T @ (a * amk.w1(s))
best = (np.inf, None); rng = np.random.default_rng(7)
starts = [np.array(v) for v in itertools.product([0.5, 1.04, 1.97, 2.91], repeat=Q)] + [rng.uniform(0, 4, Q) for _ in range(4000)]
for x0 in starts:
    r = minimize(fg, x0, jac=True, method="L-BFGS-B", bounds=[(0, 40)] * Q, options={"ftol": 1e-15, "gtol": 1e-11})
    if r.fun < best[0]: best = (float(r.fun), r.x.copy())
fmin = best[0]
print(f"{WJ}: cN {cN}; left sub-frame (points 0..7) global min F_L = {fmin:.10f} at {np.round(best[1], 4)} "
      f"({len(starts)} starts)", flush=True)
b7 = int(J["bN"][7])
for gs in GS:
    cNL = cN - int(np.ceil(b7 * gs))
    marg = fmin * 1e8 / cNL - 1
    out = dict(n=m, SA=100000000, B_SA=sum(bN), cnum=J["cnum"], cden=J["cden"], H=J["H"], aN=aN, bN=bN,
               eps_strong=(cNL + 0.5) / 1e8, cN_L=cNL, gstar=gs, Fmin_true=fmin, margin=marg,
               source=f"{WJ}: points 0..7 sub-frame; floor cN - b_7 g* = {cN} - {b7}*{gs}")
    fn = f"{PRE}_g{gs}.json"
    json.dump(out, open(fn, "w"), indent=1)
    print(f"  g* = {gs}: cN_L = {cNL} (= {cN} - {b7}*{gs}); margin min F_L / cN_L - 1 = {marg:+.4%} -> "
          f"{'FEASIBLE' if marg > 0 else 'INFEASIBLE (the sub-frame inequality is false)'}; wrote {fn}", flush=True)
