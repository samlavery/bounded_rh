import sys, time, numpy as np
sys.path.insert(0, '.')
import size7
from size7 import run, Q, PAIRS
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
mins = d['mins']; vals = d['vals']
gmin = vals[0] * 1e8
delta = float(sys.argv[1]); tau = float(sys.argv[2]); hw = int(sys.argv[3])
cN = int(gmin * (1 - delta))
basins = []
for v, x in zip(vals, mins):
    if v * 1e8 > gmin * (1 + tau): break
    for y in (x, x[::-1]):
        c = [int(round(xi * 32768)) for xi in y]
        bx = tuple((ci - hw, ci + hw) for ci in c)
        if bx[0][0] <= bx[Q - 1][1] and bx not in basins: basins.append(bx)
print(f"delta={delta} cN={cN} basins={len(basins)} halfwidth={hw}", flush=True)
t0 = time.time()
r = run(cN, aN=aN, bN=bN, JC=4, corner='lean', dmin=5, PED=4, basins=basins, verbose=True, max_leaves=3 * 10**6)
if r: print(f"leaves {r['nleaves']} Z {r['nZ']} M {r['nM']} basin-leaves {r['nB']} d-cells {r['stats']['dP']['finest']} w-cells {r['stats']['w']['finest']} pts {r['stats']['points']} bad {r['bad_leaves']} ({time.time()-t0:.0f}s)")
