"""R window (re-optimised AMTOPA family) for n points: rational coefficients, LP re-solved on the ROUNDED window,
mirror-symmetric integer weights over SA = 10^8, strong floor, admissibility numbers.  Writes rwin6.json."""
import sys, json, itertools
import numpy as np, mpmath as mp
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window')
from wopt import evaluate, best_phi, window, strong_floor
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import Family, H_of

n = int(sys.argv[1]); B_SA = int(sys.argv[2]); THETA = json.loads(sys.argv[3]); out = sys.argv[4]
SA = 10**8; DEN = 10**9; Q = n - 1
cnum = [DEN] + [int(round(x * DEN)) for x in THETA[1:]]          # c_0 = 1, c_j over 10^9
c = np.array(cnum, float) / DEN; w = np.concatenate([[np.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cnum))])
B = B_SA / SA
import os
BETA = float(os.environ.get('RWIN_BFLOOR', '0'))   # pressure floor b_r >= BETA * B / Q (more uniform b: larger prod b)
if BETA > 0:
    import wopt
    from scipy.optimize import linprog
    def solve_lp_floor(self):
        fam, Qf, NP, Bf = self.fam, self.fam.Q, self.fam.NP, self.B
        Wm = fam.Wmat(self.G)
        nvar = NP + Qf + 1; cost = np.zeros(nvar); cost[-1] = -1.0
        A_eq = np.zeros((Qf + 1, nvar))
        for s, cols in enumerate(fam.blocks): A_eq[s, cols] = 1.0
        A_eq[Qf, NP:NP + Qf] = 1.0; b_eq = np.concatenate([np.full(Qf, 2.0), [Bf]])
        A_ub = np.hstack([-Wm, -self.G, np.ones((Wm.shape[0], 1))])
        res = linprog(cost, A_ub=A_ub, b_ub=np.zeros(Wm.shape[0]), A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 2)] * NP + [(BETA * Bf / Qf, Bf)] * Qf + [(None, None)], method='highs')
        if not res.success: raise RuntimeError(res.message)
        return res.x[:NP], res.x[NP:NP + Qf], float(res.x[-1]), -res.ineqlin.marginals
    wopt.LPState.solve_lp = solve_lp_floor
if n >= 8 or os.environ.get("RWIN_STRONG"):      # the plain LP oracle misses lattice basins at seven gaps; fold the strong search into the LP
    from wopt8 import evaluate_s, smin
    r = evaluate_s(n, B, np.sqrt(2.0), c[1:], rounds=40)
else:
    r = evaluate(n, B, np.sqrt(2.0), c[1:], rounds=40, strong=False)
fam = r['fam']; a, b = r['state'].a, r['state'].b
# mirror symmetrisation: pair (i,j) <-> (n-1-j, n-1-i); gap r <-> Q-1-r
mir = [fam.pairs.index((n - 1 - j, n - 1 - i)) for (i, j) in fam.pairs]
a = (a + a[mir]) / 2; b = (b + b[::-1]) / 2
# integer rounding: per span sum <= 2 SA (floor, then top up symmetric pairs), b sums to B_SA exactly
aN = np.floor(a * SA + 1e-9).astype(np.int64)
for s, cols in enumerate(fam.blocks):
    deficit = 2 * SA - aN[cols].sum()
    assert deficit >= 0
bN = np.floor(b * SA).astype(np.int64)
bN = (bN + bN[::-1]) // 2
mid = Q // 2
if Q % 2 == 1: bN[mid] = B_SA - (bN.sum() - bN[mid])
else:
    rem = B_SA - bN.sum(); assert rem % 2 == 0
    bN[mid - 1] += rem // 2; bN[mid] += rem // 2
assert bN.sum() == B_SA and all(bN > 0) and all(bN == bN[::-1])
aR, bR = aN / SA, bN / SA
lat4 = np.array(list(itertools.product((1.04, 1.97, 2.91, 0.5), repeat=Q)))
floors = [fam.global_min(aR, bR, coarse=400000, keep=250, seed=s, extra_starts=lat4)[0] for s in (1, 2, 3)]
if n >= 8 or os.environ.get("RWIN_STRONG"): floors += [smin(fam, aR, bR, lat4, seed=s)[0] for s in (11, 12)]
eps = min(floors)
mp.mp.dps = 40
t = 1 / mp.sqrt(2)
P = sum((mp.mpf(cnum[j]) / DEN) ** 2 * (mp.mpf(1) / 2 - 1 / (4 * mp.pi ** 2 * j ** 2)) for j in range(1, len(cnum)))
Hx = mp.mpf(3) / 2 - mp.cos(t) / (mp.sqrt(2) * mp.sin(t)) - P / (2 * mp.sin(t) ** 2)
H = float(Hx)
s = np.linspace(0, 0.5, 2000001)
v = (c[:, None] * np.cos(w[:, None] * s[None, :])).sum(0)
pv = np.clip(np.diff(v), 0, None).sum(); pvs = np.clip(np.diff(np.sqrt(v / 1.25)), 0, None).sum()
sabs = float(np.abs(c[1:]).sum()); sj = float(sum(abs(c[j]) * j for j in range(1, len(c)))); sj2 = float(sum(abs(c[j]) * j * j for j in range(1, len(c))))
res = dict(n=n, B_SA=B_SA, SA=SA, cnum=cnum, cden=DEN, H=str(Hx), aN={f'{i},{j}': int(aN[k]) for k, (i, j) in enumerate(fam.pairs)},
           bN=[int(x) for x in bN], eps_strong=eps, eps_lp_float=r['eps'], spans=[int(aN[cols].sum()) for cols in fam.blocks],
           sum_abs=sabs, vd_bound=1.5 + 6.3 * sj, vdd_bound=2 + 39.7 * sj2, v0=float(v[0]), vmin=float(v.min()),
           pv_v=float(pv), pv_sqrt_v_over_M=float(pvs))
for d in (0.0, 0.0002, 0.0005, 0.001, 0.002, 0.003):
    cc = int(np.floor(eps * (1 - d) * SA))
    phi, m = best_phi(H - 1e-9, cc / SA, B, n)
    res[f'delta_{d}'] = dict(cN=cc, m=m, phi=phi)
json.dump(res, open(out, 'w'), indent=1)
print(json.dumps({k: v for k, v in res.items() if k not in ('aN',)}, indent=1))
print('aN', res['aN'])
