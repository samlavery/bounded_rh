"""Exact replica (Fractions) of the Lean checks in AMW/DEQfCells.lean + AMW/DEQfH.lean (cellOk, knotOk, vloOk,
edgeOk, certHOk), with Trig.sinPiI.  Used to size the cells; the Lean `decide` is the proof."""
from fractions import Fraction as F
import math
from qrep import (rdn, rup, rnd, pt, add, sub, neg, mul, isum, tCosQ, tSinQ, errQ, sin01, cos01, s2I, cAM, wI,
                  qA0, qB0, qC0, ZI)
def dA(A, B, C, D, i): return add(mul(B[i], wI(i)), C[i])
def dB(A, B, C, D, i): return add(neg(mul(A[i], wI(i))), D[i])
def dC(A, B, C, D, i): return mul(D[i], wI(i))
def dD(A, B, C, D, i): return neg(mul(C[i], wI(i)))
qD0 = [pt(0)] * 13
L1 = [[f(qA0, qB0, qC0, qD0, i) for i in range(13)] for f in (dA, dB, dC, dD)]
# Trig.lean (rounding 1e-10, pi to 1e-6)
def tfl(x): return F(math.floor(x * 10 ** 10), 10 ** 10)
def tcl(x): return F(math.ceil(x * 10 ** 10), 10 ** 10)
piLo, piHi = F(3141592, 10 ** 6), F(3141593, 10 ** 6)
def TLo(a): return tfl(piLo * a)
def THi(a): return tcl(piHi * a)
def cosI(a): return (tfl(tCosQ(THi(a)) - errQ), tcl(tCosQ(TLo(a)) + errQ))
def sinI(a): return (tfl(tSinQ(TLo(a)) - errQ), tcl(tSinQ(THi(a)) + errQ))
def csA(k):
    c, s = 1, 0
    for _ in range(k): c, s = -s, c
    return c, s
def imulZ(e, I): return (e * I[0], e * I[1]) if e >= 0 else (e * I[1], e * I[0])
def kOf(t): return max(0, math.floor(2 * t + F(1, 2)))
def rOf(t): return t - F(kOf(t), 2)
def sinPiI(t):
    k = kOf(t); r = rOf(t); c, s = csA(k)
    if r >= 0: return add(imulZ(s, cosI(r)), imulZ(c, sinI(r)))
    return sub(imulZ(s, cosI(-r)), imulZ(c, sinI(-r)))
def sinPiOk(t): r = abs(rOf(t)); return 0 <= TLo(r) and THi(r) <= 1
def hX(c): return mul(s2I, pt(c / 2))
def ok01(X): return 0 <= X[0] and X[1] <= 1
def cosPt(i, c):
    if i == 0:
        X = hX(c); return sub(mul(cos01(X), cos01(X)), mul(sin01(X), sin01(X)))
    return sinPiI(2 * i * c + F(1, 2))
def sinPt(i, c):
    if i == 0:
        X = hX(c); return mul(pt(2), mul(sin01(X), cos01(X)))
    return sinPiI(2 * i * c)
def ptOk(i, c): return ok01(hX(c)) if i == 0 else (sinPiOk(2 * i * c) and sinPiOk(2 * i * c + F(1, 2)))
def evOk(c): return all(ptOk(i, c) for i in range(13))
def evI(A, B, C, D, c):
    return isum(lambda i: add(add(add(mul(A[i], cosPt(i, c)), mul(B[i], sinPt(i, c))), mul(mul(C[i], pt(c)), cosPt(i, c))),
                              mul(mul(D[i], pt(c)), sinPt(i, c))), 13)
M2 = F(9)
def cell(a, b, ya, yb, M=M2):
    """returns (ok, slack_a, slack_b)"""
    c = (a + b) / 2; h = (b - a) / 2
    Q0 = evI(qA0, qB0, qC0, qD0, c); Q1 = evI(*L1, c)
    ra = Q0[0] - Q1[1] * h - M / 2 * h ** 2 - ya; rb = Q0[0] + Q1[0] * h - M / 2 * h ** 2 - yb
    ok = 0 <= a < b <= 1 and evOk(c) and ra >= 0 and rb >= 0
    return ok, ra, rb
def knot(N, s, k, y0, y1):
    worst = None
    for m in range(s):
        a = F(k, N) + F(m, N * s); b = F(k, N) + F(m + 1, N * s)
        ok, ra, rb = cell(a, b, y0 + (y1 - y0) * m / s, y0 + (y1 - y0) * (m + 1) / s)
        if not ok: return False, min(ra, rb)
        w = min(ra, rb); worst = w if worst is None else min(worst, w)
    return True, worst
def vI(c): return isum(lambda j: mul(pt(cAM[j]), cosPt(j, c)), 13)
def vloC(N, s, m): return F(1, 2) - F(1, N) + F(2 * m + 1, 2 * N * s)
def vloOk(N, s, vlo):
    if not vlo > 0: return False
    return all(evOk(vloC(N, s, m)) and vlo <= vI(vloC(N, s, m))[0] - F(7, 2) * F(1, 2 * N * s) for m in range(s))
def edgeOk(N, y, vlo): return ZI[0] > 0 and N * y * ZI[1] <= vlo ** 2
