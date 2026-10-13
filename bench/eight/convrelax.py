"""on sampled parent boxes: the convex-relaxation bound min_box b.g + sum_t a_t conv_t(s_t) (conv_t = convex envelope of
w on the term's range) = the best bound by per-term affine minorants with independent slopes; fraction of parents it certifies"""
import sys, pickle, random, numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '.')
from sevenw import w as wf, PAIRS, NP, Q, INC
SC = 32768
d = np.load('w40.npz'); a = np.array([int(x) for x in d['aN']], float) / 1e8; b = np.array([int(x) for x in d['bN']], float) / 1e8
gmin = float(d['vals'][0]); delta = float(sys.argv[2]); c = gmin * (1 - delta)
L = pickle.load(open(sys.argv[1], 'rb')); random.seed(5)
S = random.sample([x for x in L if x[2] is not None], int(sys.argv[3]) if len(sys.argv) > 3 else 600)
def hull(lo, hi, n=400):
    xs = np.linspace(lo, hi, n); ys = wf(xs); H = []
    for x, y in zip(xs, ys):
        while len(H) >= 2 and (H[-1][1] - H[-2][1]) * (x - H[-1][0]) >= (y - H[-1][1]) * (H[-1][0] - H[-2][0]): H.pop()
        H.append((x, y))
    return [(H[k][1] - H[k + 1][1] * 0 - (H[k + 1][1] - H[k][1]) / (H[k + 1][0] - H[k][0]) * H[k][0], (H[k + 1][1] - H[k][1]) / (H[k + 1][0] - H[k][0])) for k in range(len(H) - 1)] or [(H[0][1], 0.0)]
res = []; resbox = []
for box, kind, par in S:
    for which, bx in (('parent', par), ('leaf', box)):
        lo = np.array([p[0] for p in bx]) / SC; hi = np.array([p[1] for p in bx]) / SC
        A_ub = []; b_ub = []
        for t, (i, j) in enumerate(PAIRS):
            lt, ht = lo[i:j].sum(), hi[i:j].sum()
            for (al, dl) in hull(lt, ht) if ht > lt else [(float(wf(lt)), 0.0)]:
                row = np.zeros(Q + NP); row[i:j] = dl; row[Q + t] = -1.0; A_ub.append(row); b_ub.append(-al)
        cost = np.concatenate([b, a])
        r = linprog(cost, A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=list(zip(lo, hi)) + [(None, None)] * NP, method='highs')
        (res if which == 'parent' else resbox).append(((r.fun - c) / c) if r.status == 0 else np.nan)
res = np.array(res); resbox = np.array(resbox)
print(f"{len(res)} parents: convex-relaxation bound passes c on {np.mean(res >= 0):.3f}; (bound - c)/c pct 10/50/90 {np.round(np.nanpercentile(res, [10, 50, 90]), 4)}")
print(f"the leaves themselves: passes on {np.mean(resbox >= 0):.3f}")
