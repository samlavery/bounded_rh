"""Float sizing of the EIGHT-point weighted MT certificate (7 gaps): zero-order leaf test, widest-axis bisection,
no half-space reflection (the weights are not reversal-symmetric). For each margin delta below the LP floor:
leaf count and the board constant kappa(c) = max_m (m H - B (m-7)) / (m - c (m-7)), B = 93/23000."""
import sys, os, math, itertools, time, json
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission")); sys.setrecursionlimit(100000)
import gen_w
d = json.load(open(os.path.expanduser("~/work/zeta-lab/hunts/amtopa_eight_point/artifacts/cand_mt8_verified.json")))
Q = 7
A = {(i, j): Fr(v, 10**9) for i, j, v in d['pair_weights']['entries']}
Bv = [Fr(v, 46*10**9) for v in d['position_pressure']['numerators']]
a = {k: float(v) for k, v in A.items()}; b = [float(v) for v in Bv]
H0 = 0.67250070367941172655; Btot = 93/23000
def kappa(c): return max((m*H0 - Btot*(m-7))/(m - c*(m-7)) for m in range(16, 4000))
S2 = math.sqrt(2.0); GAM = (1/S2)*math.cos(1/S2)/math.sin(1/S2)
H = 2e-6; X = np.arange(0, 40, H); B_ = math.pi*X
with np.errstate(divide='ignore', invalid='ignore'):
    W = ((np.cos(B_) - 2*GAM*B_*np.sin(B_))/(1 - 2*B_*B_))**2
sing = ~np.isfinite(W) | (np.abs(1 - 2*B_*B_) < 1e-6); W[sing] = np.interp(X[sing], X[~sing], W[~sing])
tab = [W]; k = 1
while (1 << k) <= len(W):
    p = tab[-1]; tab.append(np.minimum(p[:-(1 << (k-1))], p[(1 << (k-1)):])); k += 1
LIPW = np.max(np.abs(np.gradient(W, H)[X > 0.4]))
def wmin(lo, hi):
    i = max(0, int(lo/H)); j = min(len(W) - 1, int(math.ceil(hi/H))); k = (j - i + 1).bit_length() - 1
    return min(tab[k][i], tab[k][j - (1 << k) + 1]) - LIPW*H
terms = [(a[(i, j)], tuple(range(i, j))) for i in range(Q+1) for j in range(i+1, Q+1) if a[(i, j)] != 0]
def run(c, cap):
    adj = [A[(r, r+1)] for r in range(Q)]
    S = [Fr(-(-(4*c)//Bv[r]), 4) for r in range(Q)]
    bads = []
    for r in range(Q):
        _, bad = gen_w.G.phase1(c/adj[r], S[r]); bads.append([(float(l), float(u)) for l, u in bad])
    cf = float(c); cnt = [0]
    def low(box):
        tot = sum(b[r]*box[r][0] for r in range(Q))
        for coef, idx in terms: tot += coef*wmin(sum(box[i][0] for i in idx), sum(box[i][1] for i in idx))
        return tot
    def sub(box, dd=0):
        if low(box) >= cf: cnt[0] += 1; return True
        if dd > 90 or cnt[0] > cap: return False
        w = [hi - lo for lo, hi in box]; k = w.index(max(w)); mid = (box[k][0] + box[k][1])/2
        l1 = list(box); l1[k] = (box[k][0], mid); l2 = list(box); l2[k] = (mid, box[k][1])
        return sub(tuple(l1), dd+1) and sub(tuple(l2), dd+1)
    ok = True; ntup = 1
    for bd in bads: ntup *= len(bd)
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        if not sub(tuple(bads[r][tup[r]] for r in range(Q))): ok = False; break
    return ok, cnt[0], [len(x) for x in bads]
floor = 0.0071016
for delta in [float(x) for x in sys.argv[1:]]:
    c = Fr(int(floor*(1 - delta)*10**8), 10**8); t = time.time()
    ok, n, sizes = run(c, 3_000_000)
    print(f"delta {delta:.3f} c={float(c):.8f} kappa={kappa(float(c)):.7f}: {'OK ' if ok else 'CAP'} leaves {n:9d} per-gap bad {sizes} ({time.time()-t:.0f}s)", flush=True)
