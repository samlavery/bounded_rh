"""bridge-port 2026-10-10: the sizer's window json for the 9-point certificate from window-scope's rounded weights
(bench/arun/est/cert9_final.json: a by floor over 1e8, b nearest, B = 437542/1e8, c_true of the rounded weights by a fresh
global search).  Format as window/rwin8.json (n, SA, B_SA, cnum, cden, H, aN, bN, eps_strong, delta_*).

Independent checks before writing (pre-registered: all must hold, else no file):
  (1) symmetry a(i,j) = a(8-j, 8-i), b palindromic; capacities sum_{j-i=s} a <= 2e8; a >= 0.
  (2) F at window-scope's argmin, with the R8 kernel evaluated by my own closed form (sat9/e46_sepgram.k_R8,
      normalised kfun, w = kfun^2), equals their c_true to <= 1e-12.
  (3) a short local re-minimisation from each of their 16 near-binding basins finds nothing below c_true - 1e-10.
"""
import json, sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/window/sat9")
src = open("/Users/samuellavery/work/riemann-submission/bench/window/sat9/e46_sepgram.py").read()
exec(src.split("\nif __name__ == \"__main__\":\n")[0])

C = json.load(open("/Users/samuellavery/work/riemann-submission/bench/arun/est/cert9_final.json"))
W8 = json.load(open("/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json"))
n = C["n"]; assert n == 9
P = [(i, j) for i in range(n) for j in range(i + 1, n)]
aN = {f"{i},{j}": int(C["a_int_over_1e8"][f"{i},{j}"]) for (i, j) in P}
bN = [int(x) for x in C["b_int_over_1e8"]]
assert sum(bN) == C["B_int"] == 437542
for (i, j) in P:
    assert aN[f"{i},{j}"] == aN[f"{n-1-j},{n-1-i}"] and aN[f"{i},{j}"] >= 0
assert bN == bN[::-1]
caps = [sum(aN[f"{i},{j}"] for (i, j) in P if j - i == s) for s in range(1, n)]
assert max(caps) <= 2 * 10 ** 8, caps
a = np.array([aN[f"{i},{j}"] for (i, j) in P]) / 1e8; b = np.array(bN) / 1e8
PI = np.array([p[0] for p in P]); PJ = np.array([p[1] for p in P])

def F(g):
    y = np.concatenate([[0.0], np.cumsum(g)])
    k, _ = k_R8(y[PJ] - y[PI])
    return float(b @ g + a @ (k * k))

c_ws = C["c_true"]
g0 = np.array(C["near_binding_2e-4"][0]["gaps"])
f0 = F(g0)
print(f"(2) F(argmin) mine {f0:.15f} | window-scope c_true {c_ws:.15f} | diff {f0 - c_ws:+.2e}")
assert abs(f0 - c_ws) <= 1e-12
best = f0
for row in C["near_binding_2e-4"]:
    r = minimize(F, np.array(row["gaps"]), method="L-BFGS-B", bounds=[(0, 40)] * (n - 1), options={"ftol": 1e-16, "gtol": 1e-12})
    best = min(best, r.fun)
print(f"(3) local re-minimisation over {len(C['near_binding_2e-4'])} basins: min {best:.15f} (c_true - min = {c_ws - best:+.2e})")
assert best >= c_ws - 1e-10
out = dict(n=n, SA=100000000, B_SA=437542, cnum=W8["cnum"], cden=W8["cden"], H=W8["H"], aN=aN, bN=bN,
           eps_strong=c_ws, source="bench/arun/est/cert9_final.json (window-scope; a floor, b nearest; fresh global search)",
           caps=caps)
for d in (0.0, 0.0002, 0.0005, 0.001):
    out[f"delta_{d}"] = {"cN": int(c_ws * 1e8 * (1 - d))}
json.dump(out, open("/Users/samuellavery/work/riemann-submission/bench/arun/cert/n9/rwin9_lp9.json", "w"), indent=1)
print("wrote rwin9_lp9.json; cN at delta 2e-4 / 5e-4 / 1e-3:", [out[f"delta_{d}"]["cN"] for d in (0.0002, 0.0005, 0.001)], "caps", caps)
