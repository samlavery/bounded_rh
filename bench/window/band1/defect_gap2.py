"""Full LP on the multi-double curvature-maximising configurations (k doubles, one at s, Q2 < 0 at moderate slack):
LP(D, y) = slack(D) + Delta_B(y) with a pair of depth y at s (two-sided), on y in [0.1, 0.8]; then minimise LP directly at
fixed y from those configurations (pair at s, the other k-1 doubles and the simples free)."""
import sys, numpy as np
from scipy.optimize import minimize
exec(open('defect_gap.py').read().split("print('certificate v1")[0].replace("NN = int(sys.argv[1])", "NN = 48"))
def configs(k, sig, tries=14, seed=0):
    rr = np.random.default_rng(seed); found = []
    for t in range(tries):
        nsimp = N - 2 * k; dsites = [0] + [int(v) for v in rr.choice(np.arange(-6, 7)[np.arange(-6, 7) != 0], k - 1, replace=False)]
        vac = [int(v) for v in rr.choice(np.arange(N // 2 - 8, N // 2 + 8), k, replace=False)]
        occ = set(dsites) | set(vac); simp = np.array([t2 for t2 in range(-N // 2, N // 2) if t2 not in occ][:nsimp], float)
        x0 = np.concatenate([simp + rr.normal(0, 0.03, len(simp)), np.array(dsites[1:], float)]); m = np.concatenate([np.ones(len(simp)), np.full(k - 1, 2.0), [2.0]])
        full = lambda x: np.concatenate([x, [0.0]])
        cons = {'type': 'ineq', 'fun': lambda x: sig - slack(full(x), m)}
        r = minimize(lambda x: -Vpp(full(x), m, 0.0), x0, method='SLSQP', constraints=[cons], options={'maxiter': 300, 'ftol': 1e-10})
        if slack(full(r.x), m) <= sig * 1.001: found.append((-2 * Vpp(full(r.x), m, 0.0), slack(full(r.x), m), full(r.x), m))
    return sorted(found, key=lambda t: t[0])[:3]
def DeltaB(x, m, y):   # pair at s = 0 (the double at 0 in D is the pair's own double)
    B = 2 * (np.cosh(2 * np.pi * JJ * y / N) - 1); S = S_of(x, m)
    return float(np.sum(qq * (B ** 2 + 2 * B * np.real(S))) / N)
for k in (4, 6):
    for sig in (0.5, 2.0):
        for (q2, sl, x, m) in configs(k, sig)[:2]:
            prof = ' '.join('y=%.1f:%+.3f' % (y, sl + DeltaB(x, m, y)) for y in (0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.8))
            dbl = np.sort(x[m == 2]); print('k=%d sig<=%.1f: Q2 %+.2f slack %.3f | doubles at %s | LP(y): %s' % (k, sig, q2, sl, np.round(dbl, 2), prof), flush=True)
            # direct minimisation of LP at the worst y from this configuration (all positions free except the pair at 0)
            for y in (0.3, 0.4, 0.5):
                idx = np.arange(len(x)); keep = np.abs(x) > 1e-12
                def f(xx):
                    full = x.copy(); full[keep] = xx; return slack(full, m) + DeltaB(full, m, y)
                r = minimize(f, x[keep], method='L-BFGS-B', options={'maxiter': 500})
                full = x.copy(); full[keep] = r.x
                print('    min LP at y=%.1f from here: %+.4f (slack %.3f, Q2 %+.2f)' % (y, r.fun, slack(full, m), -2 * Vpp(full, m, 0.0)), flush=True)
