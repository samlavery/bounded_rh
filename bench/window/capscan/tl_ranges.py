"""U_delta = {7-gap windows with F <= c(1+delta)} (PC8C5BF's F, c = eps_strong): ranges of single gaps by class
(short a < 1.5 <= long b) and of adjacent-pair sums by type (ab/ba, bb, aa), by SLSQP from many U seeds."""
import itertools, json, numpy as np
from scipy.optimize import minimize
from rmax import Fwin
c = 805165 / 1e8
SEEDW = [[1.0451, 1.9866, 1.9866, 1.0451, 1.9758, 1.0436, 1.9759], [1.9745, 1.0427], [1.9791, 1.044, 1.9791],
         [1.9814, 1.0432, 1.9712, 1.0432, 1.9814], [1.0415, 1.9774, 1.9774, 1.0415, 1.9606, 1.041, 1.9606]]
seeds = []
for w in SEEDW:
    ext = np.tile(w, 8)
    for s in range(len(w)): seeds.append(ext[s:s + 7].copy())
out = {}
for d in (0.0025, 0.005, 0.01, 0.02, 0.04):
    lim = c * (1 + d); res = {}
    cons = [{'type': 'ineq', 'fun': lambda g: lim - Fwin(g)}]
    def extreme(fun, sgn, seed, bnds):
        r = minimize(lambda g: sgn * fun(g), seed, method='SLSQP', bounds=bnds, constraints=cons, options={'maxiter': 300})
        return sgn * r.fun if (r.success and Fwin(r.x) <= lim * (1 + 1e-9)) else None
    for seed in seeds:
        if Fwin(seed) > lim: continue
        cls = ['a' if x < 1.5 else 'b' for x in seed]
        bnds = [(0.5, 1.5) if ch == 'a' else (1.5, 2.8) for ch in cls]
        for i in range(7):
            key = cls[i]
            for sgn in (1, -1):
                v = extreme(lambda g, i=i: g[i], sgn, seed, bnds)
                if v is not None:
                    lo, hi = res.get(key, (np.inf, -np.inf)); res[key] = (min(lo, v), max(hi, v))
        for i in range(6):
            key = ''.join(sorted(cls[i] + cls[i + 1]))
            for sgn in (1, -1):
                v = extreme(lambda g, i=i: g[i] + g[i + 1], sgn, seed, bnds)
                if v is not None:
                    lo, hi = res.get(key, (np.inf, -np.inf)); res[key] = (min(lo, v), max(hi, v))
    out[d] = {k: [float(v[0]), float(v[1])] for k, v in res.items()}
    print('delta %.2f%%: ' % (100 * d) + '  '.join('%s [%.4f, %.4f]' % (k, *v) for k, v in sorted(res.items())), flush=True)
json.dump({str(k): v for k, v in out.items()}, open('tl_ranges.json', 'w'), indent=1)
