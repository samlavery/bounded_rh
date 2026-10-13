"""Replica of a planned integer enclosure of w'' on a cell (scale DZ, interval products rounded outward):
w'' = 2 pi^2 P2 / D^4,  P2 = M^2 + N (N2 D^2 + 4 N D + 8 b M),  N2 = -(1 + 4 gam) cos b + 2 gam b sin b,
with N, M, D, b as in the derivative cells.  W2LO bounds w'' below in units 1/U2."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "mvt"))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "pyr"))
from functools import lru_cache
from w1cell import base, imulD, imulP, imulPP, GAMI, G1I
from wz import DZ, PLN, PUN, SC, ndiv, ndivc, imulZZ, iaddZ, isubZ
U2 = 10**9
KU2 = 8 * U2
P20 = 10**20
G2I = (DZ + 2 * GAMI[0], DZ + 2 * GAMI[1])

@lru_cache(maxsize=None)
def w2cell(LN, UN, sc=SC):
    okC, CX, SX, BLZ, BUZ = base(LN, UN, sc)
    BI = (BLZ, BUZ)
    PI2 = imulPP(GAMI, BI)
    NI = isubZ(CX, imulP(PI2, SX))
    NbI = isubZ((0, 0), iaddZ(imulP(G1I, SX), imulP(PI2, CX)))
    DI = isubZ((DZ, DZ), imulZZ(2, imulPP(BI, BI)))
    MI = iaddZ(imulD(NbI, DI), imulP(imulZZ(4, BI), NI))
    N2I = isubZ(imulP(PI2, SX), imulP(G2I, CX))
    inner = iaddZ(iaddZ(imulD(N2I, imulD(DI, DI)), imulZZ(4, imulD(NI, DI))), imulP(imulZZ(8, BI), MI))
    P2I = iaddZ(imulD(MI, MI), imulD(NI, inner))
    ok = okC and DI[1] < 0
    if not ok: return False, 0
    E1 = -DI[1]; E2 = -DI[0]   # |D| in [E1, E2]
    p1 = P2I[0]
    if p1 >= 0: lo = ndiv(2 * PLN * PLN * p1 * DZ**3 * U2, P20 * P20 * E2**4)
    else: lo = -ndivc(2 * PUN * PUN * (-p1) * DZ**3 * U2, P20 * P20 * E1**4)
    return True, lo
EM = (1 << 32) - 1
def fW2(LN, UN):
    ok, lo = w2cell(LN, UN)
    return min(max(KU2 + lo, 0), EM) if ok else 0

if __name__ == "__main__":
    import numpy as np
    sys.path.insert(0, '.')
    from sevenw import w1
    def w2n(x, h=1e-6): return (w1(x + h) - w1(x - h)) / (2 * h)
    for x0 in [0.6, 0.9, 1.03, 1.2, 1.7, 2.06, 2.5, 3.0, 4.0, 6.0]:
        i0 = int(x0 * SC); out = []
        for l in [0, 3, 5, 7, 9]:
            a = (i0 >> l) << l; b = a + (1 << l)
            xs = np.linspace(a / SC, b / SC, 100); t = w2n(xs)
            ok, lo = w2cell(a, b)
            out.append(f"l{l}: var {t.max() - t.min():.1e} min {t.min():+.3f} loose {t.min() - lo / U2:.1e}")
        print(x0, " | ".join(out))

KB = 1 << 20
def conv_ok(a, b):
    """the Lean `chainOk` cell test on [a, b] / SC: a <= b < KB, okD and P2I.1 >= 0"""
    if not (a <= b and b + 1 <= KB): return False
    okC, CX, SX, BLZ, BUZ = base(a, b, SC)
    BI = (BLZ, BUZ)
    PI2 = imulPP(GAMI, BI)
    NI = isubZ(CX, imulP(PI2, SX))
    NbI = isubZ((0, 0), iaddZ(imulP(G1I, SX), imulP(PI2, CX)))
    DI = isubZ((DZ, DZ), imulZZ(2, imulPP(BI, BI)))
    if not (okC and DI[1] < 0): return False
    MI = iaddZ(imulD(NbI, DI), imulP(imulZZ(4, BI), NI))
    N2I = isubZ(imulP(PI2, SX), imulP(G2I, CX))
    inner = iaddZ(iaddZ(imulD(N2I, imulD(DI, DI)), imulZZ(4, imulD(NI, DI))), imulP(imulZZ(8, BI), MI))
    P2I = iaddZ(imulD(MI, MI), imulD(NI, inner))
    return P2I[0] >= 0
def chain(lo, hi, minw=8):
    """a chain lo = c0 < c1 < ... < ck = hi of cells passing conv_ok (cut at the half-integers, where the cells'
    trigonometric anchors change, then dyadic splitting), or None"""
    cuts = [x for x in range((lo // 16384 + 1) * 16384, hi, 16384)]
    if cuts:
        out = []; a = lo
        for b in cuts + [hi]:
            c = chain1(a, b, minw)
            if c is None: return None
            out += c; a = b
        return out
    return chain1(lo, hi, minw)
def chain1(lo, hi, minw=8):
    if conv_ok(lo, hi): return [hi]
    if hi - lo <= minw: return None
    m = (lo + hi) // 2
    A = chain1(lo, m, minw)
    if A is None: return None
    B = chain1(m, hi, minw)
    if B is None: return None
    return A + B
assert G2I == (4309997162800000, 4309997207200000)
