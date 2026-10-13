"""diagnostic: integer slope test (ideal tables) on the float sizer's S leaves"""
import sys, pickle, random, numpy as np
sys.path.insert(0, '.')
from size7s import run, Q, PAIRS, NP, SC, U, U1
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; cN = int(gmin * (1 - 0.0003)); CSU = cN * SC * U
L = pickle.load(open('leaves_ZS_0.0003_0.03_1475.pkl', 'rb'))
S = [b for k, b in L if k == 'S']; random.seed(2); S = random.sample(S, 400)
R = run(cN, aN, bN, probe=True)
est, sint, scands = R['est'], R['sint'], R['scands']
ok = 0; losses = []
for box in S:
    cs = scands(box)
    best = max(sint(box, q, T, *est) for v, modes, q, T in cs)
    fv = max(v for v, *_ in cs)
    if best >= CSU: ok += 1
    losses.append(fv * 1e8 - best / (SC * U))
print(f"integer S passes {ok}/{len(S)}; float-vs-integer loss mean {np.mean(losses):.0f} median {np.median(losses):.0f} (1e-8 units)")
# decomposition of the loss for a few boxes: charges with exact w' vs derivative pyramid
from size7s import frq, KU1
from functools import lru_cache
from w1cell import fP, fM
lbw, lbP, lbM, pw, pd = est
def exP(lo, hi): return int((frq('lo', lo, hi) + 2) * U1)
def exM(lo, hi): return int((2 - frq('hi', lo, hi)) * U1)
from pyr_table import Pyr
PPy = Pyr(PE=4, PB=10, MAXA=4, U=U1, FUEL=14)
def mkD(f, R):
    @lru_cache(maxsize=None)
    def E(l, i):
        if l < R: return E(R, i >> (R - l))
        if l == R: return min(f(i << l, (i + 1) << l), PPy.EM)
        return min(E(l - 1, 2 * i), E(l - 1, 2 * i + 1))
    def lb(lo, hi):
        cv = PPy.cover(lo, hi)
        if not cv or cv[-1] is None: return 0
        return min(E(l, i) for (l, i) in cv)
    return lb
variants = {'ideal-as-built': (lbP, lbM), 'exact': (exP, exM)}
for R_ in (5, 3):
    variants[f'dense{R_}'] = (mkD(fP, R_), mkD(fM, R_))
for name, (fp, fm) in variants.items():
    ok = 0; ls = []
    for box in S[:150]:
        cs = scands(box)
        best = max(sint(box, q, T, lbw, fp, fm, pw, pd) for v, modes, q, T in cs)
        fv = max(v for v, *_ in cs)
        ok += best >= CSU; ls.append(fv * 1e8 - best / (SC * U))
    print(f"{name}: passes {ok}/150, loss mean {np.mean(ls):.0f} median {np.median(ls):.0f}", flush=True)
