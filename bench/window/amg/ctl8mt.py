"""Kernel-swap control for the n = 8 bulk: the MT kernel (bench/eight/size7s.py, mvt-engine's sizer, unchanged) with the
R8 try1 weights, cN at delta below the MT functional's own minimum; sizing only (DUMP, early return).
Usage: TWOGRID=1 GSH=5 WMIN=9 DLO=8 DHI=9 ctl8mt.py wR8_mt.npz DELTA OUT.pkl"""
import os, sys, time, pickle, numpy as np
os.environ["NOS"] = "1"; os.environ["MREG"] = "3"
HERE = os.path.dirname(os.path.abspath(__file__)); E = os.path.join(HERE, "..", "..", "eight")
sys.path.insert(0, os.path.join(HERE, "..", "..", "mvt")); sys.path.insert(0, E)
import size7s
from size7s import run, SC
from w2cell import conv_ok, chain
d = np.load(os.path.join(HERE, sys.argv[1])); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
cN = int(float(d['vals'][0]) * 1e8 * (1 - float(sys.argv[2])))
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
D = []; t0 = time.time()
print(f"MT kernel, R8 weights: cN {cN}, B {sum(bN)}, regions {len(REGS)}", flush=True)
r = run(cN, aN, bN, JCQ=8, basins=(), WMIN=int(os.environ["WMIN"]), PED=6, DFUEL=14, DLO=int(os.environ["DLO"]), DHI=int(os.environ["DHI"]),
        centers=(), CRAD=0, MTEST=3, regions=REGS, DUMP=D)
print("RESULT", {k: r[k] for k in r if k.startswith('n')} if r else None, f"({time.time()-t0:.0f}s)", flush=True)
pickle.dump(dict(D=D, cN=cN, aN=aN, bN=bN), open(os.path.join(HERE, sys.argv[3]), 'wb'))
