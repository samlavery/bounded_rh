"""Hessian-PSD basins on the AM landscape: for each near-minimal minimum, the largest cube q ± h (q = grid point near
the minimiser) on which M = sum_t a_t l_t e_t e_t^T is PSD, l_t = min w'' on the term's range; the box is then decided by
G(g) >= G(q) + grad G(q).(g - q) (+ 1/2 d^T M d >= 0).  Float l_t (dense grid) and integer-cell l_t (amk.cellK order 2)."""
import os, sys, time, math, itertools, numpy as np
AMG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "window", "amg"); sys.path.insert(0, AMG)
import amk
SC = 32768; Q = 6; n = 7
PAIRS = [(i, j) for i in range(n) for j in range(i + 1, n)]; NP = len(PAIRS)
INC = np.zeros((NP, Q))
for t, (i, j) in enumerate(PAIRS): INC[t, i:j] = 1.0
d = np.load(os.path.join(AMG, 'wAM.npz')); aN = np.array([int(x) for x in d['aN']]); bN = np.array([int(x) for x in d['bN']])
a = aN / 1e8; b = bN / 1e8; gmin = float(d['vals'][0])
TAU = float(sys.argv[1]) if len(sys.argv) > 1 else 0.03; delta = float(sys.argv[2]) if len(sys.argv) > 2 else 0.002
c = gmin * (1 - delta)
XS = np.arange(0, 20 * SC + 2) / SC; W2 = amk.w2(XS)
def l_float(lo, hi): return float(W2[lo:hi + 1].min())
def l_int(lo, hi, ncell=16):
    """lower bound of w'' on [lo, hi] from integer cell enclosures (cells of ~(hi-lo)/ncell, cut at half-integers)"""
    cuts = sorted(set([lo, hi] + [x for x in range((lo // 16384 + 1) * 16384, hi, 16384)]))
    best = None
    for a0, b0 in zip(cuts, cuts[1:]):
        step = max(1, (b0 - a0) // ncell); x = a0
        while x < b0:
            y = min(b0, x + step); ok, K = amk.cellK(x, y, 2)
            if not ok: return None
            k0, k1, k2 = K; s = max(0, k1[0], -k1[1])
            v = 2 * (s * s + amk.imul(k0, k2)[0] * amk.DZ) / amk.DZ ** 2 / 1.0
            best = v if best is None else min(best, v); x = y
    return best
def G(g): s = INC @ g; return float(b @ g + a @ amk.w(s))
def grad(g): s = INC @ g; return b + INC.T @ (a * amk.w1(s))
rows = []; QS = []; HS = []
for v, x in zip(d['vals'], d['mins']):
    if v > gmin * (1 + TAU): break
    q = np.round(x * SC).astype(int)
    best = None
    for dq in itertools.product((-1, 0, 1), repeat=Q):
        qq = q + np.array(dq); gn = float(np.abs(grad(qq / SC)).sum())
        if best is None or gn < best[0]: best = (gn, qq)
    q = best[1]; gq = grad(q / SC); Gq = G(q / SC)
    def psd_ok(h, lfun):
        ls = []
        for (i, j) in PAIRS:
            lo = int(q[i:j].sum()) - (j - i) * h; hi = int(q[i:j].sum()) + (j - i) * h
            l_ = lfun(lo, hi)
            if l_ is None: return False, None
            ls.append(l_)
        M = INC.T @ np.diag(a * np.array(ls)) @ INC
        return float(np.linalg.eigvalsh(M)[0]) >= 0, ls
    hmax = {}
    for name, lf in (('float', l_float), ('int', l_int)):
        lo_h, hi_h = 0, 12000
        while hi_h - lo_h > 32:
            m = (lo_h + hi_h) // 2
            if psd_ok(m, lf)[0]: lo_h = m
            else: hi_h = m
        hmax[name] = lo_h
    h = hmax['int']; marg = (Gq - c - float(np.abs(gq).sum()) * h / SC) / c
    rows.append((v, hmax['float'], hmax['int'], marg)); QS.append(q); HS.append(hmax['int'])
    print(f"min {v*1e8:.0f}: PSD half-width float {hmax['float']/SC:.4f}, integer cells {hmax['int']/SC:.4f}; "
          f"tangent margin at that size {marg*100:+.3f}% of c", flush=True)
hs = np.array([r[2] for r in rows]) / SC
print(f"{len(rows)} minima: integer PSD half-width pct 10/50/90 {np.round(np.percentile(hs, [10, 50, 90]), 4)}; "
      f"negative tangent margins {sum(r[3] < 0 for r in rows)}")
np.savez(os.environ.get("OUT", "psd_basins.npz"), q=np.array(QS), h=np.array(HS))
