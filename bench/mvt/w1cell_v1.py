"""Exact replica of the planned Lean derivative-cell pipeline `CellN.okD` / `CellN.W1LO` / `CellN.W1HI`
(new code, mean-value leaf test), on top of the integer cell pipeline `wz.pipeline` (CXZ, SXZ, BLZ, BUZ, okC).

w(x) = N^2 / D^2 with b = pi x, N = cos b - 2 gam b sin b, D = 1 - 2 b^2, and
w'(x) = 2 pi N M / D^3,  M = Nb D + 4 b N,  Nb = -(1 + 2 gam) sin b - 2 gam b cos b.
All intervals are pairs of integers at scale DZ = 10^15; `imulD` is the interval product rounded outward.
W1LO / W1HI bound w' on the cell in units 1/U1 (U1 = 10^9)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "pyr"))
from functools import lru_cache
from wz import DZ, PLN, PUN, GLN, GUN, SC, ndiv, ndivc, zfdiv, zcdiv, imulZZ, iaddZ, isubZ, kside, csA, nsub
from wz import cosLo, cosHi, sinLo, sinHi, cosP, cosN, sinP, sinN, ERRD

U1 = 10**9
KU1 = 2 * U1
P20 = 10**20; P10 = 10**10

def imin4(a, b, c, d): return min(min(a, b), min(c, d))
def imax4(a, b, c, d): return max(max(a, b), max(c, d))
def imulD(I, J):
    p = (I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1])
    return (zfdiv(imin4(*p)), zcdiv(imax4(*p)))
GAMI = (2 * GLN * 100000, 2 * GUN * 100000)
G1I = (DZ + 2 * GLN * 100000, DZ + 2 * GUN * 100000)

@lru_cache(maxsize=None)
def base(LN, UN, sc=SC):
    """CXZ, SXZ, BLZ, BUZ, okC exactly as wz.pipeline computes them"""
    k, side = kside(LN, UN, sc)
    LLO = ndiv(LN * DZ, sc); UHI = ndivc(UN * DZ, sc); AD = k * (DZ // 2)
    RLO = nsub(LLO, AD) if side else nsub(AD, UHI)
    RHI = nsub(UHI, AD) if side else nsub(AD, LLO)
    TLZ = ndiv(PLN * RLO, P20); TUZ = ndivc(PUN * RHI, P20)
    CLZ = cosLo(TUZ) - ERRD; CUZ = cosHi(TLZ) + ERRD; SLZ = sinLo(TLZ) - ERRD; SUZ = sinHi(TUZ) + ERRD
    cA, sA = csA(k)
    if side:
        CXZ = isubZ(imulZZ(cA, (CLZ, CUZ)), imulZZ(sA, (SLZ, SUZ))); SXZ = iaddZ(imulZZ(sA, (CLZ, CUZ)), imulZZ(cA, (SLZ, SUZ)))
    else:
        CXZ = iaddZ(imulZZ(cA, (CLZ, CUZ)), imulZZ(sA, (SLZ, SUZ))); SXZ = isubZ(imulZZ(sA, (CLZ, CUZ)), imulZZ(cA, (SLZ, SUZ)))
    BLZ = ndiv(PLN * LLO, P20); BUZ = ndivc(PUN * UHI, P20)
    P2LZ = ndiv(2 * GLN * BLZ, P10); P2UZ = ndivc(2 * GUN * BUZ, P10)
    DHIZ = ndivc(2 * BUZ * BUZ, DZ) - DZ
    okC = (LN <= UN and TUZ <= DZ and (k * sc <= 2 * LN if side else 2 * UN <= k * sc) and cosN(TUZ) <= cosP(TUZ)
           and cosN(TLZ) <= cosP(TLZ) and sinN(TLZ) <= sinP(TLZ) and sinN(TUZ) <= sinP(TUZ)
           and DZ * DZ < 2 * BLZ * BLZ and 0 < DHIZ)
    return okC, CXZ, SXZ, BLZ, BUZ

@lru_cache(maxsize=None)
def w1cell(LN, UN, sc=SC):
    """(okD, W1LO, W1HI): integer bounds of w' * U1 on the cell [LN, UN] / sc"""
    okC, CX, SX, BLZ, BUZ = base(LN, UN, sc)
    BI = (BLZ, BUZ)
    PI2 = imulD(GAMI, BI)
    NI = isubZ(CX, imulD(PI2, SX))
    NbI = isubZ((0, 0), iaddZ(imulD(G1I, SX), imulD(PI2, CX)))
    DI = isubZ((DZ, DZ), imulZZ(2, imulD(BI, BI)))
    MI = iaddZ(imulD(NbI, DI), imulD(imulZZ(4, BI), NI))
    QI = imulD(NI, MI)
    okD = okC and DI[1] < 0
    if not okD: return False, 0, 0
    E1 = -DI[1]; E2 = -DI[0]
    q2 = QI[1]
    if q2 <= 0: lo = ndiv(2 * PLN * (-q2) * DZ**2 * U1, P20 * E2**3)
    else: lo = -ndivc(2 * PUN * q2 * DZ**2 * U1, P20 * E1**3)
    q1 = QI[0]
    if 0 <= q1: hi = -ndiv(2 * PLN * q1 * DZ**2 * U1, P20 * E2**3)
    else: hi = ndivc(2 * PUN * (-q1) * DZ**2 * U1, P20 * E1**3)
    return True, lo, hi

EM = (1 << 32) - 1
def fP(LN, UN):
    """the stored lower bound of (w' + 2) U1 on the cell (0 = no information)"""
    ok, lo, hi = w1cell(LN, UN)
    return min(max(KU1 + lo, 0), EM) if ok else 0
def fM(LN, UN):
    """the stored lower bound of (2 - w') U1 on the cell"""
    ok, lo, hi = w1cell(LN, UN)
    return min(max(KU1 - hi, 0), EM) if ok else 0

if __name__ == "__main__":
    import math
    g = (1 / math.sqrt(2)) * math.cos(1 / math.sqrt(2)) / math.sin(1 / math.sqrt(2))
    def w1(x):
        b = math.pi * x; N = math.cos(b) - 2 * g * b * math.sin(b); D = 1 - 2 * b * b
        Nb = -(1 + 2 * g) * math.sin(b) - 2 * g * b * math.cos(b); M = Nb * D + 4 * b * N
        return 2 * math.pi * N * M / D**3
    for (L, w) in [(16384, 0), (16384, 1), (16384, 32), (32768, 0), (32768, 64), (40000, 1024), (100000, 16), (300000, 256)]:
        ok, lo, hi = w1cell(L, L + w)
        xs = [(L + w * i / 50) / SC for i in range(51)]
        tl = min(w1(x) for x in xs); th = max(w1(x) for x in xs)
        print(L, w, ok, lo / U1, hi / U1, "true", tl, th, "loss", tl - lo / U1, hi / U1 - th)
