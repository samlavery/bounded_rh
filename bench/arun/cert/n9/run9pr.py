#!/usr/bin/env python3
"""Sizing driver for size8pz (pair-distance cells): weights from a window json (gmin = eps_strong), env as run8am
(AMWIN, TWOGRID, GSH, JSH, WMIN, DLO, DHI, MINR, MAXD, ROOTSEL, QB, SPLIT, PFK).  Usage: run8pz.py W.json DELTA"""
import os, sys, time, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
os.environ["NOS"] = "1"; os.environ["MREG"] = "3"
J = json.load(open(sys.argv[1])); n_ = J["n"]
os.environ["SQ"] = str(n_ - 1)   # the sizer's gap count Q = n - 1 (size8pz reads it at import)
import size9pr as S   # (bridge-port 2026-10-11: run9pr.py = run9pz.py on size9pr, the RCUT root-partition hook)
from amk import conv_ok
aN = [int(J["aN"][f"{i},{j}"]) for i in range(n_) for j in range(i + 1, n_)]; bN = [int(x) for x in J["bN"]]
gmin = float(J["eps_strong"]) * 1e8; delta = float(sys.argv[2]); cN = int(gmin * (1 - delta))
SC = S.SC
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
print(f"delta={delta} cN={cN} env " + " ".join(f"{k}={os.environ.get(k)}" for k in ("GSH", "TWOGRID", "JSH", "WMIN", "MINR", "PLO", "YFRAC", "SPLIT", "PFK", "NR", "LPEMPTY", "NOZ", "LSC", "ROOTSEL")), flush=True)
t0 = time.time()
r = S.run(cN, aN, bN, JCQ=8, basins=(), PED=6, DFUEL=14, DLO=int(os.environ.get("DLO", "5")), DHI=int(os.environ.get("DHI", "6")),
          regions=REGS, centers=(), CRAD=0, WMIN=int(os.environ.get("WMIN", "6")), MTEST=3, NPT=9,
          max_leaves=int(os.environ.get("MAXL", "4000000")))
if r:
    nl = r['nleaves']
    print(f"leaves {nl} kinds {r['kinds']} (0 refl, 1 Z, 6 M, 7 empty by tightening, 8 LP-infeasible); splits {r['nsplit']} (pair {r['nsplit_pair']}); "
          f"walk bits {r['bits']} ({r['bits'] / nl:.1f} per leaf; multipliers {r['nY']} x {r['YW']} bits); M nonzero multipliers {sorted(r['nzY'].items())}; "
          f"constraints per M cell {sorted(r['ncons'].items())}; w {r['stats']['w']['finest']} d {r['stats']['d']['finest']} "
          f"pts {r['stats']['points']} ptc {r['stats']['ptcells']} bad {r['bad']} MSTAT lp {r['MSTAT']['lp']} ({time.time()-t0:.0f}s)", flush=True)
    nc = r['NODEC']; tot = sum(nc.values()); mean = sum(k * v for k, v in nc.items()) / tot
    print(f"nodes visited {tot} (leaves {nl} + splits {r['nsplit']}); explicit constraints per node: mean {mean:.2f}, dist {sorted(nc.items())}", flush=True)
    if r.get('VDIAG'): print("exactly valid candidates by faithful-tchk outcome:", r['VDIAG'], flush=True)
    B_ = r['bits']; print(f"walk: {B_} bits = {B_ / 4 / 1e6:.3f} MB hex, {B_ / 6 / 1e6:.3f} MB base64 (roots run); x8.73: {B_ * 8.73 / 4 / 1e6:.2f} MB hex, {B_ * 8.73 / 6 / 1e6:.2f} MB base64", flush=True)
    if os.environ.get("SAVE"):
        import pickle
        def tr(nd):
            if nd[0] == 'leaf': return ('leaf', tuple(nd[1]), dict(nd[1].cons), nd[2], nd[3])
            return ('split', tuple(nd[1]), dict(nd[1].cons), nd[2], tr(nd[4]), tr(nd[5]), nd[3] or 0)   # [6]: BSPLIT mode
        pickle.dump(dict(leaves=[(tuple(c), c.cons, k, p) for _, c, k, p in r['leaves']],
                         trees=[tr(nd) for nd in r['nodes'].values()], nroots=len(r['nodes'])), open(os.environ["SAVE"], "wb"))
