"""Exact replica (Fractions) of the rational cell enclosures of the convex-basin layer (typh, Apache-2.0):
`Cell` (the four-point rational checker's cos/sin/θ enclosures), `Riemann.Encl.enc` (kfun, w', w'' on a cell),
`Riemann.BasinC.segCell` (cells on the 2^-32 grid), `okD`, `negD`, `cellOk`."""
from fractions import Fraction as F
from functools import lru_cache
import math

E12 = 10**12
def floorD(x): return F(math.floor(x * E12), E12)
def ceilD(x): return F(math.ceil(x * E12), E12)
PLO = F(314159265358979323846, 10**20); PHI = F(314159265358979323847, 10**20)
GLO = F(8274992907, 10**10); GHI = F(8274993018, 10**10)
ERR = F(13, 5748019200)
def tcos(t):
    s = t * t
    return 1 + s * (F(-1, 2) + s * (F(1, 24) + s * (F(-1, 720) + s * (F(1, 40320) + s * F(-1, 3628800)))))
def tsin(t):
    s = t * t
    return t * (1 + s * (F(-1, 6) + s * (F(1, 120) + s * (F(-1, 5040) + s * (F(1, 362880) + s * F(-1, 39916800))))))
def csA(k):
    c, s = 1, 0
    for _ in range(k % 4): c, s = -s, c
    return c, s
def imulZ(e, I): return (e * I[0], e * I[1]) if e >= 0 else (e * I[1], e * I[0])
def iadd(I, J): return (I[0] + J[0], I[1] + J[1])
def isub(I, J): return (I[0] - J[1], I[1] - J[0])
def ineg(I): return (-I[1], -I[0])
def cst(q): return (q, q)
def iscale(q, I): return (q * I[0], q * I[1]) if q >= 0 else (q * I[1], q * I[0])
def imul(I, J):
    p = (I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1])
    return (floorD(min(min(p[0], p[1]), min(p[2], p[3]))), ceilD(max(max(p[0], p[1]), max(p[2], p[3]))))
def iinvN(J): return (floorD(1 / J[1]), ceilD(1 / J[0]))

class Cell:
    def __init__(self, L, U, k, side):
        self.L, self.U, self.k, self.side = L, U, k, side
        self.A = F(k, 2)
        self.rlo = (L - self.A) if side else (self.A - U)
        self.rhi = (U - self.A) if side else (self.A - L)
        self.TL = floorD(PLO * self.rlo); self.TU = ceilD(PHI * self.rhi)
        self.CI = (floorD(tcos(self.TU) - ERR), ceilD(tcos(self.TL) + ERR))
        self.SI = (floorD(tsin(self.TL) - ERR), ceilD(tsin(self.TU) + ERR))
        cA, sA = csA(k)
        if side:
            self.CX = isub(imulZ(cA, self.CI), imulZ(sA, self.SI)); self.SX = iadd(imulZ(sA, self.CI), imulZ(cA, self.SI))
        else:
            self.CX = iadd(imulZ(cA, self.CI), imulZ(sA, self.SI)); self.SX = isub(imulZ(sA, self.CI), imulZ(cA, self.SI))
        self.BL = floorD(PLO * L); self.BU = ceilD(PHI * U)
    def okD(self):
        return (F(1, 2) <= self.L and self.L <= self.U and 0 <= self.rlo and self.TU <= 1 and 0 <= self.TL and 0 <= self.BL)

Gq = (GLO, GHI); Pq = (PLO, PHI)
def enc(C, S, T):
    G2T = iscale(2, imul(Gq, T))
    N = isub(C, imul(G2T, S))
    N1 = isub(imul(ineg(iadd(cst(1), iscale(2, Gq))), S), imul(G2T, C))
    N2 = iadd(imul(ineg(iadd(cst(1), iscale(4, Gq))), C), imul(G2T, S))
    T2 = imul(T, T)
    iD = iinvN(isub(cst(1), iscale(2, T2)))
    iD2 = imul(iD, iD)
    K = imul(N, iD)
    K1 = iadd(imul(N1, iD), imul(iscale(4, imul(T, N)), iD2))
    K2 = iadd(iadd(iadd(imul(N2, iD), imul(iscale(8, imul(T, N1)), iD2)), imul(iscale(4, N), iD2)),
              imul(iscale(32, imul(T2, N)), imul(iD2, iD)))
    return K, iscale(2, imul(Pq, imul(K, K1))), iscale(2, imul(imul(Pq, Pq), iadd(imul(K1, K1), imul(K, K2))))
def negD(T): return isub(cst(1), iscale(2, imul(T, T)))[1] < 0

DQ = 4294967296
@lru_cache(maxsize=None)
def segCell(a, b):
    k = (a + b + 2147483648) // DQ
    return Cell(F(a, DQ), F(b, DQ), k, k * DQ <= 2 * a)
@lru_cache(maxsize=None)
def cellOk(a, b):
    c = segCell(a, b)
    return c.okD() and negD((c.BL, c.BU))
@lru_cache(maxsize=None)
def cellEnc(a, b):
    c = segCell(a, b)
    return enc(c.CX, c.SX, (c.BL, c.BU))
def wloK(K):
    if K[0] >= 0: return K[0] * K[0]
    if K[1] <= 0: return K[1] * K[1]
    return F(0)

if __name__ == "__main__":
    import numpy as np, sys
    sys.path.insert(0, '.')
    from sevenw import w, w1, w2
    for x in [0.6, 1.03, 1.5, 1.98, 2.96, 4.0, 7.5]:
        a = int(x * DQ)
        K, W1, W2 = cellEnc(a, a)
        print(x, cellOk(a, a), float(K[0]), float(K[1]), float(W1[0]), float(W1[1]), w1(x), float(W2[0]), float(W2[1]), w2(x))
        b = a + (1 << 22)
        K, W1, W2 = cellEnc(a, b)
        print('   cell 2^-10:', float(W2[0]), float(W2[1]), 'true range', min(w2(x), w2(x + 2**-10)), max(w2(x), w2(x + 2**-10)))
