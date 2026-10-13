"""float check: does the second-order per-term test (negative curvature charged, positive dropped) certify the basin
boxes with the expansion point at the minimizer?"""
import sys, numpy as np
sys.path.insert(0, '.')
import os
os.environ.setdefault('QQ', '6')
from sevenw import Fun, w, w1, w2, PAIRS, Q, INC
SC = 32768
d = np.load('w40.npz'); aN = np.array(d['aN'], float); bN = np.array(d['bN'], float); a = aN / 1e8; b = bN / 1e8
mins = d['mins']; vals = d['vals']; gmin = vals[0]
delta = float(sys.argv[1]); c = gmin * (1 - delta)
xs = np.arange(0, 40 * SC + 2) / SC
W2g = w2(xs)
def minw2(lo, hi): return float(W2g[max(lo, 0):hi + 1].min())
def Ubound(box, q, greedy=True):
    lo = np.array([x[0] / SC for x in box]) - q; hi = np.array([x[1] / SC for x in box]) - q
    iv = [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
    l2 = np.array([minw2(l, h) for l, h in iv]); w0 = np.array([float(w(np.arange(l, h + 1) / SC).min()) for l, h in iv])
    sq = INC @ q; wq = w(sq); w1q = w1(sq); dl = INC @ lo; dh = INC @ hi
    pen = np.where(l2 < 0, 0.5 * l2 * np.maximum(dl * dl, dh * dh), 0.0)
    use = np.ones(len(PAIRS), bool)
    def total(use):
        g = b + INC.T @ (a * w1q * use)
        return float(b @ q + np.minimum(g * lo, g * hi).sum() + (a * np.where(use, wq + pen, w0)).sum())
    cur = total(use)
    if greedy:
        imp = True
        while imp:
            imp = False
            for t in np.argsort(pen):
                if not use[t]: continue
                use[t] = False; v = total(use)
                if v > cur: cur = v; imp = True
                else: use[t] = True
    return cur, int((l2 < 0).sum())
for k, (v, x) in enumerate(zip(vals, mins)):
    if v > gmin * 1.05: break
    q = np.round(x * SC / 16) * 16 / SC
    for hw in [737, 1475, 2212, 2950]:
        box = [(int(round(xi * SC)) - hw, int(round(xi * SC)) + hw) for xi in x]
        u, nneg = Ubound(box, q)
        print(f"min {k} excess {100*(v/gmin-1):.2f}% hw {hw}: U - c = {(u - c)*1e8:+.0f} (x1e-8)  negative-curvature terms {nneg}")
