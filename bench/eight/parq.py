"""on sampled parent boxes: does the slope test at the (quantised) box minimiser certify them?"""
import sys, pickle, random, numpy as np
sys.path.insert(0, '.')
from size7s import run, Q, SC, U, PAIRS
from w2cell import conv_ok
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; delta = float(sys.argv[2]); cN = int(gmin * (1 - delta)); CSU = cN * SC * U
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
R = run(cN, aN, bN, probe=True, PED=6, DFUEL=14, DLO=6, DHI=7, WMIN=7, regions=REGS, QOPT=True)
sint, sfloat, est = R['sint'], R['sfloat'], R['est']
from scipy.optimize import minimize
from sevenw import Fun
F = Fun(np.array(aN) / 1e8, np.array(bN) / 1e8)
L = pickle.load(open(sys.argv[1], 'rb')); random.seed(5)
S = random.sample([x for x in L if x[2] is not None], int(sys.argv[3]) if len(sys.argv) > 3 else 600)
ok = okf = 0; okgp = 0
for box, kind, par in S:
    lo = np.array([p[0] for p in par]) / SC; hi = np.array([p[1] for p in par]) / SC
    r_ = minimize(F.vg, (lo + hi) / 2, jac=True, method='L-BFGS-B', bounds=list(zip(lo, hi)))
    q = []
    for k in range(Q):
        x_ = int(round(r_.x[k] * SC)); x_ = min(max(x_, par[k][0]), par[k][1]); xa = (x_ >> 4) << 4
        q.append(xa if xa >= par[k][0] else x_)
    v, T = sfloat(par, q, passes=3)
    okf += v >= cN / 1e8
    ok += sint(par, q, T, *est[:5]) >= CSU
print(f"{len(S)} parents: slope test at the box minimiser certifies {ok} (float {okf})")
