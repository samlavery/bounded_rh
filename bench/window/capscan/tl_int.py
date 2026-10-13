"""delta*: for slip patterns at EXACT integer period, the least possible max-window excess of PC8C5BF's F over
c = eps_strong (min over gap values with the period fixed).  An integer-period word whose windows all lie in U_delta
carries (almost) no resonance energy, so it caps the two-level credit for every delta >= its delta*."""
import itertools, numpy as np
from scipy.optimize import minimize
from rmax import Fwin
c = 805165 / 1e8
def win_excess(g):
    g = np.asarray(g, float); ext = np.tile(g, 8 // len(g) + 2)
    return np.array([Fwin(ext[s:s + 7]) for s in range(len(g))]) / c - 1
pats = {'ab (L=3)': ('ab', 3), 'aab (L=4)': ('aab', 4), 'abb (L=5)': ('abb', 5), 'babab (L=8)': ('babab', 8),
        'abbab (L=8)': ('abbab', 8), 'abbabab (L=11)': ('abbabab', 11), 'ababababb (L=14)': ('ababababb', 14),
        'abababb (L=11)': ('abababb', 11), 'aabab (L=7)': ('aabab', 7), 'ababb (L=8)': ('ababb', 8)}
for nm, (p, L) in pats.items():
    q = len(p); base = np.array([1.04 if ch == 'a' else 1.97 for ch in p]); base *= L / base.sum()
    cons = ({'type': 'eq', 'fun': lambda g: g.sum() - L},)
    best = (np.inf, None)
    rng = np.random.default_rng(1)
    for s0 in [base] + [base + rng.normal(0, 0.01, q) for _ in range(12)]:
        s0 = s0 * L / s0.sum()
        # minimise the max window excess via a smooth epigraph: min t s.t. excess_s <= t
        x0 = np.concatenate([s0, [win_excess(s0).max()]])
        cs = [{'type': 'eq', 'fun': lambda z: z[:q].sum() - L}] + \
             [{'type': 'ineq', 'fun': (lambda z, s=s: z[q] - win_excess(z[:q])[s])} for s in range(q)]
        r = minimize(lambda z: z[q], x0, method='SLSQP', constraints=cs, bounds=[(0.5, 3.5)] * q + [(-1, 1)],
                     options={'maxiter': 300, 'ftol': 1e-12})
        if r.success and r.fun < best[0]: best = (float(r.fun), r.x[:q].copy())
    g = best[1]
    print('%-18s delta* = %+.4f%%   gaps %s  window excesses %s' % (nm, 100 * best[0], np.round(g, 4), np.round(100 * win_excess(g), 3)), flush=True)
