#!/usr/bin/env python3
"""Sizing only (no emission) of the AM n = 8 certificate with the eight-point recipe: zero-order + minorant leaves,
no slope leaves, no basins; tables and grid from env (WMIN DLO DHI GSH TWOGRID); kernel from env AMWIN.
Usage: run8am.py WEIGHTS.npz DELTA"""
import os, sys, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); AMG = os.path.join(HERE, "..", "..", "window", "amg")
sys.path.insert(0, HERE)
os.environ["NOS"] = "1"; os.environ["MREG"] = "3"
S = __import__(os.environ.get("SZMOD", "size8amz"))
from amk import conv_ok, chain as w2chain
if sys.argv[1].endswith(".json"):
    # a window-scope LP file directly: weights from it, gmin = its eps_strong (sizing only)
    import json
    J = json.load(open(sys.argv[1])); n_ = J["n"]
    aN = [int(J["aN"][f"{i},{j}"]) for i in range(n_) for j in range(i + 1, n_)]; bN = [int(x) for x in J["bN"]]
    gmin = float(J["eps_strong"]) * 1e8
else:
    d = np.load(os.path.join(AMG, sys.argv[1])); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
    gmin = float(d['vals'][0]) * 1e8
delta = float(sys.argv[2]); cN = int(gmin * (1 - delta))
SC = S.SC
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
print(f"delta={delta} cN={cN} regions={len(REGS)} env " + " ".join(f"{k}={os.environ.get(k)}" for k in ("AMWIN", "GSH", "TWOGRID", "WMIN", "DLO", "DHI")), flush=True)
t0 = time.time()
r = S.run(cN, aN, bN, JCQ=8, basins=(), PED=6, DFUEL=14, DLO=int(os.environ.get("DLO", "5")), DHI=int(os.environ.get("DHI", "6")),
          regions=REGS, centers=(), CRAD=0, WMIN=int(os.environ.get("WMIN", "6")), MTEST=int(os.environ.get("MTEST", "3")), NPT=9, max_leaves=int(os.environ.get("MAXL", "4000000")))
if r:
    nT = sum(1 for _, box, kind, pay in r['leaves'] if box[0][0] > box[S.Q - 1][1])
    print(f"leaves {r['nleaves']} Z {r['nZ']} M {sum(1 for _, b_, k_, p_ in r['leaves'] if k_ == 6)} reflected {nT} w {r['stats']['w']['finest']} d {r['stats']['d']['finest']} "
          f"pts {r['stats']['points']} ptc {r['stats']['ptcells']} bad {r['bad']} ({time.time()-t0:.0f}s)", flush=True)
    if os.environ.get("SAVE"):
        import pickle
        pickle.dump([(box, kind, pay) if os.environ.get("SAVEPAY") else (box, kind) for _, box, kind, pay in r['leaves']], open(os.environ["SAVE"], "wb"))
        print("saved", os.environ["SAVE"], flush=True)
