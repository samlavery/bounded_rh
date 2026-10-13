import sys, os, numpy as np
sys.path.insert(0, '.')
from sevenw import Fun, w, w1, PAIRS, Q, INC
SC = 32768
d = np.load('w40.npz'); a = np.array(d['aN'], float) / 1e8; b = np.array(d['bN'], float) / 1e8
mins = d['mins']; vals = d['vals']; gmin = vals[0]; c = gmin * (1 - float(sys.argv[1]))
xs = np.arange(0, 80 * SC + 2) / SC; W1g = w1(xs)
def w1lo(lo, hi): return float(W1g[lo:hi + 1].min())
def w1hi(lo, hi): return float(W1g[lo:hi + 1].max())
def Sbound(box, qi):
    q = qi / SC
    lo = np.array([x[0] for x in box]) / SC - q; hi = np.array([x[1] for x in box]) / SC - q
    iv = [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
    sq = INC @ q; wq = w(sq); w1q = w1(sq)
    pen = np.zeros(len(PAIRS))
    for t, (i, j) in enumerate(PAIRS):
        l_, h_ = iv[t]; qt = int(qi[i:j].sum())
        up = max(0.0, w1q[t] - w1lo(qt, h_)) * (h_ - qt) / SC
        dn = max(0.0, w1hi(l_, qt) - w1q[t]) * (qt - l_) / SC
        pen[t] = max(up, dn)
    g = b + INC.T @ (a * w1q)
    return float(b @ q + np.minimum(g * lo, g * hi).sum() + (a * (wq - pen)).sum())
for k, (v, x) in enumerate(zip(vals, mins)):
    if v > gmin * 1.03: break
    qi = np.round(x * SC).astype(int)
    out = []
    for hw in [737, 900, 1100, 1300, 1475]:
        box = [(qi[r] - hw, qi[r] + hw) for r in range(Q)]
        out.append(f"{hw}:{(Sbound(box, qi) - c) * 1e8:+.0f}")
    print(k, f"{100*(v/gmin-1):.2f}%", " ".join(out))
