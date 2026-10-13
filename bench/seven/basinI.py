"""integer basin margins (dense derivative tables, cover shift DPE) vs half-width"""
import sys, numpy as np
sys.path.insert(0, '.')
from size7s import run, Q, SC, U, NP
d = np.load('w40.npz'); aN = [int(x) for x in d['aN']]; bN = [int(x) for x in d['bN']]
gmin = float(d['vals'][0]) * 1e8; delta = float(sys.argv[1]); cN = int(gmin * (1 - delta)); CSU = cN * SC * U
DPE = int(sys.argv[2]) if len(sys.argv) > 2 else 6
R = run(cN, aN, bN, probe=True, PED=DPE, DFUEL=14 if DPE <= 6 else 16, DLO=5, DHI=6)
sfloat, sint, est = R['sfloat'], R['sint'], R['est']
FULL = (1 << NP) - 1
for k, (v, x) in enumerate(zip(d['vals'], d['mins'])):
    if v * 1e8 > gmin * 1.03: break
    q = [int(round(xx * SC)) for xx in x]
    out = []
    for hw in [1475, 1024, 737, 512, 368]:
        box = tuple((qq - hw, qq + hw) for qq in q)
        fv, T = sfloat(box, q, passes=3)
        iv1 = (sint(box, q, T, *est) - CSU) / (SC * U)
        iv2 = (sint(box, q, FULL, *est) - CSU) / (SC * U)
        out.append(f"{hw}:{iv1:+.0f}/{iv2:+.0f}")
    print(k, " ".join(out), flush=True)
