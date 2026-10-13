"""Cell-bound control for the AM n = 8 bulk: the AM sizer (size8am) with the integer AM cells ('int') or with ideal cell
bounds ('ideal': w, w' over each cell from 129 float samples), on the SAME sampled root tiles (the per-gap covers
computed once with the integer cells), R8 weights, delta below the AM minimum; per-tile leaf counts.
Usage: AMWIN=../rwin8.json TWOGRID=1 GSH=5 WMIN=9 DLO=8 DHI=9 ctl8ideal.py MODE NTILES OUT.pkl"""
import os, sys, time, pickle, random, itertools, types, numpy as np
os.environ["NOS"] = "1"; os.environ["MREG"] = "3"
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import size8am, amk
from size8am import run, Q, SC, U1, KU1
MODE, NT, OUT = sys.argv[1], int(sys.argv[2]), sys.argv[3]
d = np.load(os.path.join(HERE, "wR8.npz")); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
cN = int(os.environ["CNOVR"]) if os.environ.get("CNOVR") else int(float(d["vals"][0]) * 1e8 * 0.999)
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [amk.conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
# the per-gap covers with the integer cells, shared by both modes
_ph = size8am.phase1; COV = {}
def phase1_fixed(cN_, a_, S_):
    if (a_, S_) not in COV: COV[(a_, S_)] = _ph(cN_, a_, S_)
    return COV[(a_, S_)]
size8am.phase1 = phase1_fixed
if MODE == "ideal":
    EM = amk.EM if hasattr(amk, "EM") else (1 << 32) - 1
    def _ws(L, U):
        xs = np.linspace(L / SC, U / SC, 129); k, k1, _ = amk.kders(xs); return k * k, 2 * k * k1
    def WZi(L, U, sc=SC):
        if L == U or amk.WZ(L, U) == 0: return amk.WZ(L, U)
        w, _ = _ws(L, U); return int(max(0.0, float(w.min()) * (1 - 1e-9)) * amk.SW)
    def fPi(L, U):
        if L == U: return amk.fP(L, U)
        _, w1 = _ws(L, U); return min(max(KU1 + int(np.floor(float(w1.min()) * U1)), 0), EM)
    def fMi(L, U):
        if L == U: return amk.fM(L, U)
        _, w1 = _ws(L, U); return min(max(KU1 - int(np.ceil(float(w1.max()) * U1)), 0), EM)
    size8am.WZ = WZi; size8am.fP = fPi; size8am.fM = fMi
_orig = itertools.product; TILES = []
def _sampled(*a, **k):
    L = list(_orig(*a, **k)); random.seed(7); S = random.sample(L, min(NT, len(L))); TILES.extend(S); return S
size8am.itertools = types.SimpleNamespace(product=_sampled, **{n: getattr(itertools, n) for n in dir(itertools) if not n.startswith('_') and n != 'product'})
D = []; t0 = time.time()
r = run(cN, aN, bN, JCQ=8, basins=(), WMIN=int(os.environ["WMIN"]), PED=6, DFUEL=14, DLO=int(os.environ["DLO"]), DHI=int(os.environ["DHI"]),
        centers=(), CRAD=0, MTEST=3, regions=REGS, DUMP=D, verbose=False)
bads = [COV[k][1] for k in sorted(COV, key=lambda kk: list(COV).index(kk))]
print(f"{MODE}: cN {cN}, tiles {TILES}, leaves {len(D)} ({time.time()-t0:.0f}s)", flush=True)
pickle.dump(dict(D=D, TILES=TILES, COV=COV, cN=cN), open(os.path.join(HERE, OUT), 'wb'))
