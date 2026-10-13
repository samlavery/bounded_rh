"""Leaf census of the AM n-point minorant sizing on a random sample of root tiles (diagnostic; no emission).
Usage: AMWIN=... GSH=5 WMIN=9 DLO=8 DHI=9 census8.py WEIGHTS.npz DELTA NTILES OUT.pkl"""
import os, sys, time, pickle, random, itertools, types, numpy as np
os.environ["NOS"] = "1"; os.environ["MREG"] = "3"
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import size8am
from size8am import run, Q, PAIRS, SC
from amk import conv_ok, chain
d = np.load(os.path.join(HERE, sys.argv[1])); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; cN = int(gmin * (1 - float(sys.argv[2]))); NT = int(sys.argv[3])
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
_orig = itertools.product
ntiles = [0]
def _sampled(*a, **k):
    L = list(_orig(*a, **k)); ntiles[0] = len(L)
    random.seed(1); return random.sample(L, min(NT, len(L)))
size8am.itertools = types.SimpleNamespace(product=_sampled, **{n: getattr(itertools, n) for n in dir(itertools) if not n.startswith('_') and n != 'product'})
D = []; t0 = time.time()
r = run(cN, aN, bN, JCQ=8, basins=(), WMIN=int(os.environ["WMIN"]), PED=6, DFUEL=14, DLO=int(os.environ["DLO"]), DHI=int(os.environ["DHI"]),
        centers=(), CRAD=0, MTEST=3, regions=REGS, DUMP=D, verbose=False)
print(f"tiles {ntiles[0]} sampled {min(NT, ntiles[0])}: leaves {len(D)} ({time.time()-t0:.0f}s) -> est total {len(D) * ntiles[0] / min(NT, ntiles[0]):.0f}")
pickle.dump(dict(D=D, ntiles=ntiles[0], cN=cN, aN=aN, bN=bN), open(sys.argv[4], 'wb'))
