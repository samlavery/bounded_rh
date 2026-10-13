"""diagnostic: slope pass rate with hybrid derivative tables (dense level R below XD, direct cells above) and cover PE / three-piece reads"""
import sys, pickle, random, numpy as np
from functools import lru_cache
sys.path.insert(0, '.'); sys.path.insert(0, '../pyr')
from size7s import run, Q, PAIRS, NP, SC, U, U1
from pyr_table import Pyr
from w1cell import fP, fM
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; cN = int(gmin * (1 - 0.0003)); CSU = cN * SC * U
L = pickle.load(open('leaves_ZS_0.0003_0.03_1475.pkl', 'rb'))
S = [b for k, b in L if k == 'S']; random.seed(2); S = random.sample(S, 150)
R0 = run(cN, aN, bN, probe=True)
est, sint, scands = R0['est'], R0['sint'], R0['scands']
lbw, _, _, pw, pd = est
XD = int(2.5 * SC)
CANDS = [(4, 5, 0), (6, 5, 0), (7, 5, 0), (4, 5, 3), (5, 5, 3), (6, 4, 0), (7, 4, 0), (5, 4, 3)]
for PE, R, TH in CANDS:
    X = Pyr(PE=PE, PB=10, MAXA=4, U=U1, FUEL=14)
    def mk(f):
        @lru_cache(maxsize=None)
        def E(l, i):
            if l < R: return E(R, i >> (R - l))
            if l == R or (i << l) >= XD: return min(f(i << l, (i + 1) << l), X.EM)
            return min(E(l - 1, 2 * i), E(l - 1, 2 * i + 1))
        def lb1(lo, hi):
            cv = X.cover(lo, hi)
            if not cv or cv[-1] is None: return 0
            return min(E(l, i) for (l, i) in cv)
        def lb(lo, hi):
            w = hi - lo
            if TH == 0 or w < 256: return lb1(lo, hi)
            a = w >> TH
            return min(lb1(lo, lo + a), lb1(lo + a, hi - a), lb1(hi - a, hi))
        return lb
    fp, fm = mk(fP), mk(fM)
    ok = 0; ls = []
    for box in S:
        cs = scands(box)
        best = max(sint(box, q, T, lbw, fp, fm, pw, pd) for v, modes, q, T in cs)
        fv = max(v for v, *_ in cs)
        ok += best >= CSU; ls.append(fv * 1e8 - best / (SC * U))
    print(f"PE={PE} dense R={R} below 2.5, three-piece shift {TH}: passes {ok}/150, loss mean {np.mean(ls):.0f} median {np.median(ls):.0f}", flush=True)
