import sys, time, numpy as np, collections, pickle
sys.path.insert(0, '.')
import size7
from size7 import run, Q, PAIRS
from sevenw import Fun
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
mins = d['mins']; vals = d['vals']; gmin = vals[0] * 1e8
delta = float(sys.argv[1]); tau = float(sys.argv[2]); hw = int(sys.argv[3])
cN = int(gmin * (1 - delta))
basins = []
for v, x in zip(vals, mins):
    if v * 1e8 > gmin * (1 + tau): break
    for y in (x, x[::-1]):
        c = [int(round(xi * 32768)) for xi in y]
        bx = tuple((ci - hw, ci + hw) for ci in c)
        if bx[0][0] <= bx[Q - 1][1] and bx not in basins: basins.append(bx)
r = run(cN, aN=aN, bN=bN, JC=4, corner='lean', dmin=5, PED=4, basins=basins, verbose=False, max_leaves=3 * 10**6)
F = Fun(np.array(aN) / 1e8, np.array(bN) / 1e8)
L = [(b, k) for b, k in r['leaves'] if k in (1, 2)]
C = np.array([[(x[0] + x[1]) / 2 / 32768 for x in b] for b, k in L])
W = np.array([max(x[1] - x[0] for x in b) for b, k in L])
G = F.val(C) * 1e8
rel = (G - cN) / cN
print("leaves", len(L))
for lo, hi in [(0, .01), (.01, .02), (.02, .05), (.05, .1), (.1, .2), (.2, .5), (.5, 1), (1, 1e9)]:
    sel = (rel >= lo) & (rel < hi)
    print(f"slack {lo:.2f}-{hi:.2f}: {sel.sum():7d} leaves, median width {np.median(W[sel]) if sel.any() else 0:.0f}")
ws = collections.Counter(int(x).bit_length() for x in W)
print("max-width bit lengths", sorted(ws.items()))
pickle.dump(dict(L=L, rel=rel, W=W), open(f"stats_{delta}_{tau}_{hw}.pkl", "wb"))
