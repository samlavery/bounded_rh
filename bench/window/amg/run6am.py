"""Integer-faithful sizing of the AM seven-point certificate (driver after seven/run7c.py + make7.py basins).
Usage: run7am.py DELTA [TAU] [HW]   (env: CRAD, JCQ, DLO, DHI, WMIN, DDENSE, PED)"""
import sys, os, time, pickle, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import size6am as size7am
from size6am import run, Q, PAIRS, SC
from amk import conv_ok, chain
d = np.load(os.path.join(HERE, 'wAM6.npz')); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8
delta = float(sys.argv[1]); TAU = float(sys.argv[2]) if len(sys.argv) > 2 else 0.03
HW = int(sys.argv[3]) if len(sys.argv) > 3 else 1475
CRAD = float(os.environ.get("CRAD", "0.25"))
cN = int(gmin * (1 - delta))
t0 = time.time()
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None:
        c_ = chain(_s, x_); assert c_ is not None; REGS.append((_s, x_, c_)); _s = None
print(f"{len(REGS)} convex regions, {sum(len(c) for *_, c in REGS)} chain cells ({time.time()-t0:.0f}s): "
      + " ".join(f"[{a/SC:.3f},{b/SC:.3f}]" for a, b, _ in REGS), flush=True)
def region_of(lo, hi):
    for (a_, b_, _) in REGS:
        if a_ <= lo and hi <= b_: return (a_, b_)
def extents(q):
    hl, hu = HW, HW
    for (i, j) in PAIRS:
        qt = sum(q[i:j]); n = j - i; rg = region_of(qt, qt)
        if rg is None: return 0, 0
        hl = min(hl, (qt - rg[0]) // n); hu = min(hu, (rg[1] - qt) // n)
    return hl, hu
basins = []; cents = []
for v, x in zip(d['vals'], d['mins']):
    if v * 1e8 > gmin * (1 + TAU): break
    q = [int(round(xx * SC)) for xx in x]; hl, hu = extents(q)
    print(f"  minimum {v*1e8:.0f} at {np.round(x, 4)}: extents -{hl} / +{hu}", flush=True)
    for qq in (q, q[::-1]):
        bx = tuple((qk - hl, qk + hu) for qk in qq)
        if hl > 0 and hu > 0 and bx[0][0] <= bx[Q - 1][1] and bx not in basins and len(basins) < int(os.environ.get("MAXB", "16")):
            basins.append(bx); cents.append([((qk + 8) >> 4) << 4 for qk in qq])
print(f"delta={delta} cN={cN} TAU={TAU} CRAD={CRAD} basins={len(basins)}", flush=True)
DD = os.environ.get("DDENSE", "1") == "1"
r = run(cN, aN, bN, JCQ=int(os.environ.get("JCQ", "8")), basins=basins, PED=int(os.environ.get("PED", "6")), DFUEL=14,
        DLO=int(os.environ.get("DLO", "5")) if DD else None, DHI=int(os.environ.get("DHI", "6")) if DD else None,
        regions=[(a_, b_) for (a_, b_, _) in REGS], centers=cents if CRAD > 0 else (), CRAD=CRAD,
        WMIN=int(os.environ.get("WMIN", "6")))
if r:
    nC = sum(1 for _, box, kind, pay in r['leaves'] if kind == 2 and pay[0][0] == 'C')
    st = r['stats']
    print(f"RESULT delta={delta} cN={cN} leaves {r['nleaves']} Z {r['nZ']} S {r['nS']} (centre {nC}) B {r['nB']} "
          f"w {st['w']['finest']} d {st['d']['finest']} pts {st['points']} ptc {st['ptcells']} bad {r['bad']} "
          f"chain {sum(len(c) for *_, c in REGS)} ({time.time()-t0:.0f}s)", flush=True)
    print("w stats", st['w'], "d stats", st['d'], flush=True)
    keep = {k: r[k] for k in ('nodes', 'covers', 'bads', 'S', 'leaves', 'cN')}
    keep['basins'] = basins; keep['cents'] = cents; keep['REGS'] = REGS
    pickle.dump(keep, open(os.path.join(HERE, f'size6_{delta}_{os.environ.get("TAG", "")}.pkl'), 'wb'))
else:
    print("RESULT FAILED", flush=True)
