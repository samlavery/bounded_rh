"""best integer basin margins over grid points near each minimizer (region-aware slope test, ideal dense tables)"""
import sys, itertools, numpy as np
sys.path.insert(0, '.')
from size7s import run, Q, PAIRS, SC, U, NP
from w2cell import conv_ok, chain as w2chain
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; cN = int(gmin * (1 - 0.003)); CSU = cN * SC * U; HW = 1475
REGS = []; _lo, _hi, _st = 16384, 16 * SC, 64
_ok = [conv_ok(x, x + _st) for x in range(_lo, _hi, _st)]; _s = None
for k_, v_ in enumerate(_ok + [False]):
    x_ = _lo + k_ * _st
    if v_ and _s is None: _s = x_
    if not v_ and _s is not None: REGS.append((_s, x_)); _s = None
R = run(cN, aN, bN, probe=True, PED=6, DFUEL=14, DLO=6, DHI=7, WMIN=7, regions=REGS)
sint, est = R['sint'], R['est']
def region_of(lo, hi):
    for (a_, b_) in REGS:
        if a_ <= lo and hi <= b_: return (a_, b_)
FULL = (1 << NP) - 1
scale = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
worst = None
for v, x in zip(d['vals'], d['mins']):
    if v * 1e8 > gmin * 1.03: break
    xs = [xx * SC for xx in x]; q0 = [int(round(t)) for t in xs]
    def extents(q):
        hl, hu = HW, HW
        for (i, j) in PAIRS:
            qt = sum(q[i:j]); n = j - i; rg = region_of(qt, qt)
            hl = min(hl, (qt - rg[0]) // n); hu = min(hu, (rg[1] - qt) // n)
        return int(hl * scale), int(hu * scale)
    best = None
    for dq in itertools.product(range(-2, 3), repeat=Q):
        q = [q0[k] + dq[k] for k in range(Q)]
        hl, hu = extents(q)
        box = tuple((qk - hl, qk + hu) for qk in q)
        m = (sint(box, q, FULL, *est[:5]) - CSU) / (SC * U)
        if best is None or m > best[0]: best = (m, dq)
    base = (sint(tuple((qk - extents(q0)[0], qk + extents(q0)[1]) for qk in q0), q0, FULL, *est[:5]) - CSU) / (SC * U)
    print(f"min {v*1e8:.0f}: margin at rounded q {base:+.0f}, best {best[0]:+.0f} at {best[1]}", flush=True)
    worst = best[0] if worst is None else min(worst, best[0])
print("worst best margin", worst, "-> largest cN", cN + int(worst))
