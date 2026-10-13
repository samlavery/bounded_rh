"""extend a dual hull (dual.py output) with longer words: q in [q1, q2], mean gaps L/q (L integer) in [dlo, dhi]"""
import sys, json, math, time
import numpy as np
from dual import *
src, hullf, q1, q2 = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
dlo, dhi = float(sys.argv[5]), float(sys.argv[6])
c = window_from_cnum(json.load(open(src))['cnum']); H = H_of(c); T = QFTable(make_qf(c))
hull = [tuple(h) for h in json.load(open(hullf))['hull']]
pts = [(h[0], h[1], h[2], h[3]) for h in hull]
rng = np.random.default_rng(11); t0 = time.time()
for q in range(q1, q2 + 1):
    for L in range(int(math.ceil(dlo * q)), int(math.floor(dhi * q)) + 1):
        d = L / q
        e, g = min_word(T, q, d, starts=16, rng=rng)
        pts.append((d, e, q, [round(float(x), 6) for x in g]))
    hl = lower_hull(pts); r = ceiling_from_hull(H, hl)
    e, (x1, x2, t) = envelope_at(hl, 1 / r)
    used = [h for h in hl if h[0] in (x1, x2)]
    print('q <= %d: tightened ceiling %.10f  (d = %.5f between %.4f and %.4f) (%.0fs)' % (q, r, 1 / r, x1, x2, time.time() - t0), flush=True)
    for h in used: print('    word d=%.4f q=%d Ef=%.9f gaps=%s' % (h[0], h[2], h[1], h[3]), flush=True)
json.dump(dict(window=src, H=H, ceiling=r, hull=[list(h) for h in hl]), open(hullf.replace('.json', '_ext%d.json' % q2), 'w'), indent=1)
