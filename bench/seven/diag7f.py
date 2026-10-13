"""diagnostic: slope test pass rate on float S leaves vs derivative read variants (cover shift PE, finest level DMIN)"""
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
R = run(cN, aN, bN, probe=True)
est, sint, scands = R['est'], R['sint'], R['scands']
lbw, _, _, pw, pd = est
for PE, DM in [(4, 5), (5, 5), (6, 5), (6, 4), (7, 4), (5, 4)]:
    X = Pyr(PE=PE, PB=10, MAXA=4, U=U1, FUEL=14)
    reads = set()
    def mk(f):
        @lru_cache(maxsize=None)
        def E(l, i):
            if l < DM: return E(DM, i >> (DM - l))
            return min(f(i << l, (i + 1) << l), X.EM)
        def lb(lo, hi):
            cv = X.cover(lo, hi)
            if not cv or cv[-1] is None: return 0
            for c in cv: reads.add(c)
            return min(E(l, i) for (l, i) in cv)
        return lb
    fp, fm = mk(fP), mk(fM)
    ok = 0; ls = []; nfail = 0
    for box in S:
        cs = scands(box)
        best = max(sint(box, q, T, lbw, fp, fm, pw, pd) for v, modes, q, T in cs)
        fv = max(v for v, *_ in cs)
        ok += best >= CSU; ls.append(fv * 1e8 - best / (SC * U))
    res = {}
    for (l, i) in reads:
        l2 = max(l, DM)
        if l2 <= 10:
            j = i >> (10 - l) if l <= 10 else None
            res[j] = min(res.get(j, 10), l2)
    print(f"PE={PE} DMIN={DM}: passes {ok}/150, loss mean {np.mean(ls):.0f} median {np.median(ls):.0f}; blocks {len(res)} finest cells (these leaves) {sum(1 << (10 - r) for r in res.values())}", flush=True)
