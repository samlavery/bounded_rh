"""on sampled parents: the LP bound with only CERTIFIABLE per-term minorants: the constant min w on the range, and for p on
a grid of the range the lines through (p, w(p)) with slope dL = max w' on [lo, p] or dR = min w' on [p, hi] whenever
dL <= dR (mean value theorem on each side); fraction of parents certified, for grids of NPTS points per term"""
import sys, pickle, random, numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '.')
from sevenw import w as wf, w1 as w1f, PAIRS, NP, Q
SC = 32768
d = np.load('w40.npz'); a = np.array([int(x) for x in d['aN']], float) / 1e8; b = np.array([int(x) for x in d['bN']], float) / 1e8
gmin = float(d['vals'][0]); delta = float(sys.argv[2]); c = gmin * (1 - delta)
L = pickle.load(open(sys.argv[1], 'rb')); random.seed(5)
S = random.sample([x for x in L if x[2] is not None], int(sys.argv[3]))
NPTS = int(sys.argv[4])
def minorants(lt, ht):
    xs = np.linspace(lt, ht, 600); ys = wf(xs); d1 = w1f(xs)
    out = [(float(ys.min()), 0.0, 0.0)]
    if ht <= lt: return out
    cm = np.maximum.accumulate(d1); cmin_r = np.minimum.accumulate(d1[::-1])[::-1]
    for p in np.linspace(lt, ht, NPTS):
        k = int(round((p - lt) / (ht - lt) * 599)); dL = cm[k]; dR = cmin_r[k]
        if dL <= dR:
            for dd in (dL, dR): out.append((float(ys[k]), float(dd), float(xs[k])))
    return out
for which in ('parent',):
    okc = 0; vals = []
    for box, kind, par in S:
        lo = np.array([p_[0] for p_ in par]) / SC; hi = np.array([p_[1] for p_ in par]) / SC
        A_ub = []; b_ub = []
        for t, (i, j) in enumerate(PAIRS):
            for (wp, dd, p) in minorants(lo[i:j].sum(), hi[i:j].sum()):
                row = np.zeros(Q + NP); row[i:j] = dd; row[Q + t] = -1.0; A_ub.append(row); b_ub.append(-(wp - dd * p))
        r = linprog(np.concatenate([b, a]), A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=list(zip(lo, hi)) + [(None, None)] * NP, method='highs')
        v = (r.fun - c) / c; vals.append(v); okc += v >= 0
    print(f"NPTS {NPTS}: {okc}/{len(S)} parents certified by certifiable minorants; (bound-c)/c pct 10/50/90 {np.round(np.percentile(vals, [10, 50, 90]), 4)}")
