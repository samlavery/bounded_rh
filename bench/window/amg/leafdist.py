import pickle, numpy as np, sys
sys.path.insert(0, '.')
import amk
d = np.load('wAM.npz'); aN = np.array([int(x) for x in d['aN']], float); bN = np.array([int(x) for x in d['bN']], float)
Q = 6; PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]; SC = 32768
gmin = float(d['vals'][0]) * 1e8
for f in sys.argv[1:]:
    r = pickle.load(open(f, 'rb')); L = r['leaves']
    C = np.array([[(b[0] + b[1]) / 2 / SC for b in box] for _, box, kind, pay in L])
    W = np.array([max(b[1] - b[0] for b in box) for _, box, kind, pay in L])
    K = np.array([kind for _, box, kind, pay in L])
    S = np.stack([C[:, i:j].sum(1) for (i, j) in PAIRS], 1)
    k, _, _ = amk.kders(S.ravel()); w = (k * k).reshape(S.shape)
    G = C @ bN + w @ aN
    m = (G - gmin) / gmin
    print(f, 'leaves', len(L), 'cN', r['cN'])
    edges = [-1, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1, 1e9]
    h = np.histogram(m, edges)[0]
    for a, b, n in zip(edges[:-1], edges[1:], h):
        sel = (m >= a) & (m < b)
        print(f"  margin [{a:g},{b:g}): {n:6d} leaves  (Z {int((K[sel]==1).sum())}, S {int((K[sel]==2).sum())})  median width {np.median(W[sel]) if n else 0:.0f}")
    # where: the minimal gap coordinate and largest
    print('  gmin coordinate bins of leaves with margin<0.05:', np.histogram(C[m < 0.05].min(1), [0, 0.5, 0.9, 1.1, 1.5, 2.1, 9])[0])
