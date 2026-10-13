import sys, time, os, numpy as np
sys.path.insert(0, '.')
from size7s import run, Q, PAIRS, SC
from w2cell import conv_ok, chain as w2chain
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8
delta = float(sys.argv[1]); CRAD = float(sys.argv[2]); HW = 1475
cN = int(gmin * (1 - delta))
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
def region_of(lo, hi):
    for (a_, b_) in REGS:
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
    if v * 1e8 > gmin * (1 + float(os.environ.get("TAU", "0.03"))): break
    q = [int(round(xx * SC)) for xx in x]; hl, hu = extents(q)
    for qq in (q, q[::-1]):
        bx = tuple((qk - hl, qk + hu) for qk in qq)
        if bx[0][0] <= bx[Q - 1][1] and bx not in basins:
            basins.append(bx); cents.append([((qk + 8) >> 4) << 4 for qk in qq])
print(f"delta={delta} CRAD={CRAD} basins={len(basins)}", flush=True)
t0 = time.time()
DD = os.environ.get("DDENSE", "1") == "1"
r = run(cN, aN, bN, JCQ=int(os.environ.get("JCQ", "8")), basins=basins, PED=6, DFUEL=14, DLO=int(os.environ.get("DLO", "5")) if DD else None, DHI=int(os.environ.get("DHI", "6")) if DD else None,
        regions=REGS, centers=cents if CRAD > 0 else (), CRAD=CRAD, WMIN=int(os.environ.get("WMIN", "6")))
if r:
    nC = sum(1 for _, box, kind, pay in r['leaves'] if kind == 2 and pay[0][0] == 'C')
    print(f"leaves {r['nleaves']} Z {r['nZ']} S {r['nS']} (centre {nC}) B {r['nB']} w {r['stats']['w']['finest']} d {r['stats']['d']['finest']} pts {r['stats']['points']} ptc {r['stats']['ptcells']} bad {r['bad']} ({time.time()-t0:.0f}s)")
