import json, sys, time
from fractions import Fraction as F
from qcheck import *
J = json.load(open(sys.argv[1])); E = int(J['E']); Y = [int(v) for v in J['Y']]; N = 32
y = lambda k: F(Y[k], E) if k < len(Y) else F(0)
print("n", len(Y), "y_31", float(y(31)), "32 y31", float(32 * y(31)), "Y[32]", Y[32], "max Y beyond", max(Y[33:]) if len(Y) > 33 else None)
t0 = time.time(); S = []; tot = 0
for k in range(N - 1):
    s = 1
    while True:
        ok, w = knot(N, s, k, y(k), y(k + 1))
        if ok: break
        s += 1
        if s > 64: print("FAIL at k", k); sys.exit(1)
    S.append(s); tot += s
    print(f"k={k:2d} s={s:2d} worst slack {float(w):.2e}", flush=True)
print("S", S, "cells", tot, f"({time.time()-t0:.0f}s)")
for sN in (8, 16):
    best = min(vI(vloC(N, sN, m))[0] - F(7, 2) * F(1, 2 * N * sN) for m in range(sN))
    vlo = F(math.floor(best * 10 ** 6), 10 ** 6)
    print("sN", sN, "vlo", float(vlo), "vloOk", vloOk(N, sN, vlo), "edgeOk", edgeOk(N, y(N - 1), vlo), "N y ZI2", float(N * y(N - 1) * ZI[1]), "vlo^2", float(vlo ** 2))
