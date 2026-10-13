import sys, time, os, numpy as np
sys.path.insert(0, '.')
from size7s import run, Q
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
mins = d['mins']; vals = d['vals']; gmin = vals[0] * 1e8
delta = float(sys.argv[1]); PED = int(sys.argv[2]); DLO = int(sys.argv[3]); DHI = int(sys.argv[4]); DFUEL = int(sys.argv[5])
cN = int(gmin * (1 - delta))
basins = []
for v, x in zip(vals, mins):
    if v * 1e8 > gmin * 1.03: break
    for y in (x, x[::-1]):
        c = [int(round(xi * 32768)) for xi in y]
        bx = tuple((ci - 1475, ci + 1475) for ci in c)
        if bx[0][0] <= bx[Q - 1][1] and bx not in basins: basins.append(bx)
print(f"delta={delta} cN={cN} PED={PED} DLO={DLO} DHI={DHI} DFUEL={DFUEL} basins={len(basins)}", flush=True)
t0 = time.time()
r = run(cN, aN, bN, JCQ=8, basins=basins, PED=PED, DLO=DLO, DHI=DHI, DFUEL=DFUEL)
if r:
    print(f"leaves {r['nleaves']} Z {r['nZ']} S {r['nS']} B {r['nB']} w {r['stats']['w']['finest']} d {r['stats']['d']['finest']} pts {r['stats']['points']} ptc {r['stats']['ptcells']} bad {r['bad']} ({time.time()-t0:.0f}s)")
