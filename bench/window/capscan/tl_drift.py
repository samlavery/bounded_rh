"""Two-level simulation (idealised M2: the certificate knows a U-run's drift exactly).  For slip patterns P with
integer period L0, e_P(d) = min over words of pattern P with period L0 + d of the max window excess (F/c - 1); a
pattern's words lie in U_delta iff e_P(d) <= delta.  The least favourable U-config takes the pattern and drift with the
smallest resonance credit (exact rank >= 8 energy in the 152-block, phase-averaged; an UPPER bound on any certified
interval credit).  R_2L(delta) = min( g(c(m-q)) + credit_min(delta),  g(c(1+delta)(m-q)) ) [all-out-of-U configs]."""
import numpy as np, json, math
from scipy.optimize import minimize
from rmax import Fwin, wbar, kappa, B, tau, m
c = 805165 / 1e8; cN = 805124 / 1e8; q = 7
def g(E): return E if E <= tau else 2 * math.sqrt(tau * E) - tau
def win_exc(gw):
    gw = np.asarray(gw, float); ext = np.tile(gw, 8 // len(gw) + 2)
    return np.array([Fwin(ext[s:s + 7]) for s in range(len(gw))]) / c - 1
def best_word(p, L):
    qq = len(p); base = np.array([1.04 if ch == 'a' else 1.97 for ch in p]); base *= L / base.sum()
    best = (np.inf, None); rng = np.random.default_rng(2)
    for s0 in [base] + [base + rng.normal(0, 0.008, qq) for _ in range(6)]:
        s0 = s0 * L / s0.sum(); x0 = np.concatenate([s0, [win_exc(s0).max()]])
        cs = [{'type': 'eq', 'fun': lambda z: z[:qq].sum() - L}] + [{'type': 'ineq', 'fun': (lambda z, s=s: z[qq] - win_exc(z[:qq])[s])} for s in range(qq)]
        r = minimize(lambda z: z[qq], x0, method='SLSQP', constraints=cs, bounds=[(0.5, 3.5)] * qq + [(-1, 1)], options={'maxiter': 200, 'ftol': 1e-12})
        if r.success and r.fun < best[0]: best = (float(r.fun), r.x[:qq].copy())
    return best
def credit(gw):
    w = wbar(gw, m - 1); kk = np.arange(1, m); Ek = 2 * (m - kk) * w
    return float(Ek[7:].sum())
pats = {'ab': ('ab', 3), 'abb': ('abb', 5), 'babab': ('babab', 8), 'abbabab': ('abbabab', 11), 'ababababb': ('ababababb', 14), 'aab': ('aab', 4)}
curves = {}
for nm, (p, L0) in pats.items():
    rows = []
    for d in np.round(np.concatenate([-np.geomspace(0.1, 0.0005, 12), [0.0], np.geomspace(0.0005, 0.1, 12)]), 6):
        e, gw = best_word(p, L0 + d)
        if gw is None: continue
        rows.append((float(d), e, credit(gw), list(map(float, gw))))
    curves[nm] = rows
    print('%-10s ' % nm + ' '.join('[d %+.4f e %.2f%% cr %.4f]' % (d, 100 * e, cr) for d, e, cr, _ in rows if abs(d) <= 0.06), flush=True)
json.dump(curves, open('tl_drift.json', 'w'), indent=1)
R0 = g(cN * (m - q)); k0 = kappa(R0)
print('\nPC8SF: R = g(c(m-q)) = %.6f, kappa %.7f' % (R0, k0))
for delta in (0.0025, 0.005, 0.01, 0.02, 0.04):
    cand = []
    for nm, rows in curves.items():
        inU = [r for r in rows if r[1] <= delta]
        if inU:
            r = min(inU, key=lambda r: r[2]); cand.append((r[2], nm, r[0]))
    crmin = min(cand) if cand else (np.inf, '-', 0)
    RU = R0 + crmin[0]                          # all windows in U: only c certified, plus the run credit
    Rout = g(cN * (1 + delta) * (m - q))        # all windows outside U
    R2 = min(RU, Rout)
    print('delta %.2f%%: least credit U-pattern %s (drift %+.4f, credit %.5f/block) -> R_U %.6f; all-out R %.6f; R_2L %.6f; kappa_2L %.7f (gain %.2e)'
          % (100 * delta, crmin[1], crmin[2], crmin[0], RU, Rout, R2, kappa(R2), kappa(R2) - k0), flush=True)
