import sys, time, numpy as np, pickle
sys.path.insert(0, '.')
from size7s import run, Q
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
mins = d['mins']; vals = d['vals']; gmin = vals[0] * 1e8
delta = float(sys.argv[1]); tau = float(sys.argv[2]); hw = int(sys.argv[3]); JCQ = int(sys.argv[4]) if len(sys.argv) > 4 else 8
cN = int(gmin * (1 - delta))
basins = []
for v, x in zip(vals, mins):
    if v * 1e8 > gmin * (1 + tau): break
    for y in (x, x[::-1]):
        c = [int(round(xi * 32768)) for xi in y]
        bx = tuple((ci - hw, ci + hw) for ci in c)
        if bx[0][0] <= bx[Q - 1][1] and bx not in basins: basins.append(bx)
print(f"delta={delta} cN={cN} basins={len(basins)} hw={hw} JCQ={JCQ}", flush=True)
t0 = time.time()
import os
r = run(cN, aN, bN, JCQ=JCQ, basins=basins, WMIN=int(os.environ.get("WMIN", "6")), SH=int(os.environ.get("SH", "4")), MINW=int(os.environ.get("MINW", "1024")))
if r:
    print(f"leaves {r['nleaves']} Z {r['nZ']} S {r['nS']} B {r['nB']} w {r['stats']['w']['finest']} d {r['stats']['d']['finest']} pts {r['stats']['points']} ptc {r['stats']['ptcells']} bad {r['bad']} ({time.time()-t0:.0f}s)")
