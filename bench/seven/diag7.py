"""diagnostic: float vs integer zero-order bounds on the float sizer's Z leaves"""
import sys, os, pickle, random, numpy as np
from functools import lru_cache
sys.path.insert(0, '.'); sys.path.insert(0, '../pyr'); sys.path.insert(0, '../mvt')
from size7s import Q, PAIRS, NP, SC, U, frq
from pyr_table import Pyr
from wz import WZ, SW
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; cN = int(gmin * (1 - 0.0003)); CSU = cN * SC * U
L = pickle.load(open('leaves_ZS_0.0003_0.03_1475.pkl', 'rb'))
Z = [b for k, b in L if k == 'Z']; random.seed(1); Z = random.sample(Z, 1500)
P = Pyr(PE=5, PB=10, MAXA=4, U=U, FUEL=14)
@lru_cache(maxsize=None)
def E(l, i):
    if l <= 13: return min(WZ(i << l, (i + 1) << l) * U // SW, P.EM)
    return min(E(l - 1, 2 * i), E(l - 1, 2 * i + 1))
def lbE(lo, hi):
    cv = P.cover(lo, hi)
    if not cv or cv[-1] is None: return 0
    return min(E(l, i) for (l, i) in cv)
def iv(box): return [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
fails = 0; gaps = []; terms = np.zeros(NP)
for box in Z:
    I = iv(box)
    fz = sum(bN[r] * box[r][0] for r in range(Q)) * U + SC * sum(aN[t] * frq('w', l, h) * U for t, (l, h) in enumerate(I))
    iz = sum(bN[r] * box[r][0] for r in range(Q)) * U + SC * sum(aN[t] * lbE(l, h) for t, (l, h) in enumerate(I))
    if iz < CSU: fails += 1
    gaps.append((fz - iz) / (SC * U))
    for t, (l, h) in enumerate(I): terms[t] += aN[t] * (frq('w', l, h) * U - lbE(l, h)) / U
print("Z leaves failing integer:", fails, "/", len(Z), " mean loss (1e-8 units):", np.mean(gaps), "median", np.median(gaps))
print("per-term mean loss:", np.round(terms / len(Z), 1))
w = [max(x[1] - x[0] for x in b) for b in Z]; print("median max width", np.median(w))
