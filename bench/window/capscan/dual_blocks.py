"""structured long words for the dual hull: cyclic concatenations of the two base blocks [a, b] (period 3) and
[a, a, b] (period 4) found by dual.py (a ~ 1.03, b ~ 1.96), refined by SLSQP at fixed integer period"""
import sys, json, math, time, itertools
import numpy as np
from scipy.optimize import minimize
from dual import *
src, hullf = sys.argv[1], sys.argv[2]
c = window_from_cnum(json.load(open(src))['cnum']); H = H_of(c); T = QFTable(make_qf(c))
hull = [tuple(h) for h in json.load(open(hullf))['hull']]
pts = [(h[0], h[1], h[2], h[3]) for h in hull]
t0 = time.time()
def refine(g0):
    g0 = np.asarray(g0, float); L = float(round(g0.sum())); g0 = g0 * L / g0.sum(); q = len(g0)
    cons = ({'type': 'eq', 'fun': lambda g: g.sum() - L, 'jac': lambda g: np.ones_like(g)},)
    r = minimize(lambda g: Ef_word(g, T), g0, method='SLSQP', bounds=[(0, L)] * q, constraints=cons,
                 options={'maxiter': 500, 'ftol': 1e-14})
    return float(r.fun), r.x, L / q
B2 = [1.038, 1.962]; B3 = [1.028, 1.028, 1.944]
for n3 in range(1, 4):
    for n2 in range(1, 40):
        # spread the n3 blocks of type B3 as evenly as possible among the n2 blocks of type B2
        word = []
        pos = set(int(round((k + 0.5) * (n2 + n3) / n3)) for k in range(n3))
        i2 = i3 = 0
        for slot in range(n2 + n3):
            if slot in pos and i3 < n3: word += B3; i3 += 1
            elif i2 < n2: word += B2; i2 += 1
            else: word += B3; i3 += 1
        e, g, d = refine(word)
        pts.append((d, e, len(g), [round(float(x), 6) for x in g]))
    hl = lower_hull(pts); r = ceiling_from_hull(H, hl)
    e, (x1, x2, t) = envelope_at(hl, 1 / r)
    used = [h for h in hl if h[0] in (x1, x2)]
    print('n3 <= %d: tightened ceiling %.10f (d = %.5f between %.5f and %.5f) (%.0fs)' % (n3, r, 1 / r, x1, x2, time.time() - t0), flush=True)
    for h in used: print('    word d=%.5f q=%d Ef=%.9f' % (h[0], h[2], h[1]), flush=True)
json.dump(dict(window=src, H=H, ceiling=r, hull=[list(h) for h in hl]), open(hullf.replace('.json', '_blocks.json'), 'w'), indent=1)
