"""float basin margins (exact w' ranges, expansion set by greedy steering) vs half-width, at the near-minimal minima"""
import sys, numpy as np
sys.path.insert(0, '.')
from size7s import run, Q, SC
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; delta = float(sys.argv[1]); cN = int(gmin * (1 - delta))
R = run(cN, aN, bN, probe=True); sfloat = R['sfloat']
for k, (v, x) in enumerate(zip(d['vals'], d['mins'])):
    if v * 1e8 > gmin * 1.03: break
    qi = [int(round(xx * SC)) for xx in x]
    out = []
    for hw in [1475, 2048, 3072, 4096, 6144]:
        box = tuple((q - hw, q + hw) for q in qi)
        val, T = sfloat(box, qi, passes=3)
        out.append(f"{hw}:{val * 1e8 - cN:+.0f}")
    print(k, f"{100 * (v * 1e8 / gmin - 1):.2f}%", " ".join(out), flush=True)
