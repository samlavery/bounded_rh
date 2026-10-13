"""diagnostic: zero-order loss with the three-piece read min(lb[lo,lo+a], lb[lo+a,hi-a], lb[hi-a,hi]), a = w >> S"""
import sys, os, pickle, random, numpy as np
from functools import lru_cache
sys.path.insert(0, '.'); sys.path.insert(0, '../pyr'); sys.path.insert(0, '../mvt')
from size7s import Q, PAIRS, NP, SC, U, frq
from pyr_table import Pyr
from wz import WZ, SW
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; cN = int(gmin * (1 - 0.0003)); CSU = cN * SC * U
L = pickle.load(open('leaves_ZS_0.0003_0.03_1475.pkl', 'rb'))
Z = [b for k, b in L if k == 'Z']; random.seed(1); Z = random.sample(Z, 600)
P = Pyr(PE=5, PB=10, MAXA=4, U=U, FUEL=14)
@lru_cache(maxsize=None)
def W0(l, i): return min(WZ(i << l, (i + 1) << l) * U // SW, P.EM)
def mkE(R):
    @lru_cache(maxsize=None)
    def E(l, i):
        if l <= R: return W0(l, i)
        return min(E(l - 1, 2 * i), E(l - 1, 2 * i + 1))
    return E
def iv(box): return [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
for R, SH, MINW in [(13, 0, 0), (13, 4, 4096), (8, 4, 4096), (6, 4, 4096), (8, 3, 2048), (6, 3, 1024), (8, 4, 1024)]:
    E = mkE(R)
    def lb1(lo, hi):
        cv = P.cover(lo, hi)
        if not cv or cv[-1] is None: return 0
        return min(E(l, i) for (l, i) in cv)
    lev = []
    def lb3(lo, hi):
        w = hi - lo
        if SH == 0 or w < MINW: return lb1(lo, hi)
        a = w >> SH
        for x in ((lo, lo + a), (hi - a, hi)): lev.append(max(0, (a).bit_length() - 5))
        return min(lb1(lo, lo + a), lb1(lo + a, hi - a), lb1(hi - a, hi))
    fails = 0; gaps = []
    for box in Z:
        I = iv(box)
        fz = sum(bN[r] * box[r][0] for r in range(Q)) * U + SC * sum(aN[t] * frq('w', l, h) * U for t, (l, h) in enumerate(I))
        iz = sum(bN[r] * box[r][0] for r in range(Q)) * U + SC * sum(aN[t] * lb3(l, h) for t, (l, h) in enumerate(I))
        if iz < CSU: fails += 1
        gaps.append((fz - iz) / (SC * U))
    print(f"R={R} SH={SH} MINW={MINW}: failing {fails}/{len(Z)}  mean loss {np.mean(gaps):.0f}  median {np.median(gaps):.0f}  min end level {min(lev) if lev else '-'}", flush=True)
