"""ROUTE3_B1 (bridge-port): largest x* such that some height weight omega >= 0 on [c, 1] (s = tau/T_max, so the counting window
[cT', T']) has a kernel K(x) = int omega(s) cos(s x) ds >= 0 for all x in [0, x*]; LP feasibility + bisection.
x is T'·Delta.  For the dyadic window [T, 2T]: c = 1/2 (x measured in units of 2T·Delta)."""
import numpy as np, sys
from scipy.optimize import linprog
def feasible(c, R, ns=400, nx=1500):
    s = np.linspace(c, 1.0, ns); x = np.linspace(0, R, nx)
    A = -np.cos(np.outer(x, s))            # -K(x) <= 0
    res = linprog(np.zeros(ns), A_ub=A, b_ub=np.zeros(nx), A_eq=np.ones((1, ns)), b_eq=[1.0], bounds=[(0, None)] * ns, method="highs")
    return res.status == 0, (res.x if res.status == 0 else None)
def xstar(c):
    lo, hi = 0.1, 200.0
    if not feasible(c, lo)[0]: return 0.0
    while hi - lo > 1e-3:
        mid = 0.5 * (lo + hi)
        if feasible(c, mid)[0]: lo = mid
        else: hi = mid
    return lo
for c in [0.5, 0.25, 0.1, 0.05, 0.01]:
    xs = xstar(c)
    print(f"window [{c}, 1] (ratio {1/c:g}): positivity range x* = {xs:.3f}  (in units of T_max*Delta; = {xs*c:.3f} in units of T_min*Delta)")
