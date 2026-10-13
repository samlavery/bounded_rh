"""leaf provenance for the eight-point sizing: for a sample of leaves, the parent box (which failed every test):
(a) true min of G - c over the parent (sampling + local descent), (b) zero-order shortfall split by span,
(c) gaps whose derivative interval straddles 0, and term-range widths."""
import sys, pickle, random, numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '.')
from sevenw import Fun, w as wf, w1 as w1f, PAIRS, NP, Q, INC
from size7s import frq, SC
d = np.load('w40.npz'); aN = np.array([int(x) for x in d['aN']], float); bN = np.array([int(x) for x in d['bN']], float)
a = aN / 1e8; b = bN / 1e8; F = Fun(a, b)
gmin = float(d['vals'][0]); delta = float(sys.argv[2]); c = gmin * (1 - delta)
L = pickle.load(open(sys.argv[1], 'rb'))
random.seed(5); S = random.sample([x for x in L if x[2] is not None], min(2000, len(L)))
TS = [[t for t, (i, j) in enumerate(PAIRS) if i <= r < j] for r in range(Q)]
span = np.array([j - i for (i, j) in PAIRS])
rows = []
for box, kind, par in S:
    lo = np.array([p[0] for p in par]) / SC; hi = np.array([p[1] for p in par]) / SC
    bnds = list(zip(lo, hi))
    X = lo + (hi - lo) * np.random.default_rng(len(rows)).random((400, Q))
    X = np.vstack([X, (lo + hi) / 2])
    v = F.val(X); best = X[np.argmin(v)]
    r_ = minimize(F.vg, best, jac=True, method='L-BFGS-B', bounds=bnds)
    tmin = min(float(v.min()), float(r_.fun)); xs = r_.x if r_.fun <= v.min() else best
    I = [(sum(par[k][0] for k in range(i, j)), sum(par[k][1] for k in range(i, j))) for (i, j) in PAIRS]
    wmin = np.array([frq('w', l_, h_) for l_, h_ in I])
    z = float(b @ lo + a @ wmin)
    loss = a * (wf(INC @ xs) - wmin)   # zero-order loss per term at the minimiser
    w1lo = np.array([frq('lo', l_, h_) for l_, h_ in I]); w1hi = np.array([frq('hi', l_, h_) for l_, h_ in I])
    Dlo = b + INC.T @ np.where(a > 0, a * w1lo, 0); Dhi = b + INC.T @ np.where(a > 0, a * w1hi, 0)
    strad = int(((Dlo < 0) & (Dhi > 0)).sum())
    width = np.array([h_ - l_ for l_, h_ in I]) / SC
    rows.append(dict(kind=kind, tmin=(tmin - c) / c, zshort=(c - z) / c, loss_long=float(loss[span >= 3].sum()) / c,
                     loss_short=float(loss[span < 3].sum()) / c, strad=strad, wmax=float(width.max()), w1=float(width[span == 1].max()),
                     pw=float((hi - lo).max())))
import collections
tm = np.array([r['tmin'] for r in rows]); zs = np.array([r['zshort'] for r in rows])
print(f"sample {len(rows)} leaves (kinds {collections.Counter(r['kind'] for r in rows)})")
print("(a) true min of (G - c)/c over the parent: pct 10/25/50/75/90:", np.round(np.percentile(tm, [10, 25, 50, 75, 90]), 4))
print("    fraction of parents with true margin > 1% / > 5% / > 20%:", [round(float((tm > x).mean()), 3) for x in (0.01, 0.05, 0.2)])
print("(b) zero-order shortfall (c - zlow)/c: pct 10/50/90:", np.round(np.percentile(zs, [10, 50, 90]), 4))
ll = np.array([r['loss_long'] for r in rows]); ls = np.array([r['loss_short'] for r in rows])
print("    zero-order loss at the minimiser / c, long spans (>=3) median", round(float(np.median(ll)), 4), " short spans median", round(float(np.median(ls)), 4),
      " long share of total (median)", round(float(np.median(ll / np.maximum(ll + ls, 1e-12))), 3))
st = collections.Counter(r['strad'] for r in rows)
print("(c) gaps whose dG/dg_r straddles 0 on the parent:", sorted(st.items()))
print("    parent max gap width pct 10/50/90:", np.round(np.percentile([r['pw'] for r in rows], [10, 50, 90]), 4),
      " max single-gap term width med", round(float(np.median([r['w1'] for r in rows])), 4), " max term width med", round(float(np.median([r['wmax'] for r in rows])), 3))
for k in (1, 2):
    sub = [r for r in rows if r['kind'] == k]
    if sub: print(f"  kind {k}: n {len(sub)}, true margin median {np.median([r['tmin'] for r in sub]):.4f}, straddle median {np.median([r['strad'] for r in sub])}")
