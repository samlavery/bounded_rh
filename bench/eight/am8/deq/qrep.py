"""Exact replica (Fractions) of the Lean interval pipeline in AMW/DEQfIv.lean: produces the coefficient tables."""
from fractions import Fraction as F
import math
SCL = F(10) ** 15
def rdn(x): return F(math.floor(x * SCL)) / SCL
def rup(x): return F(math.ceil(x * SCL)) / SCL
def rnd(X): return (rdn(X[0]), rup(X[1]))
def pt(q): q = F(q); return (q, q)
def add(X, Y): return (X[0] + Y[0], X[1] + Y[1])
def sub(X, Y): return (X[0] - Y[1], X[1] - Y[0])
def neg(X): return (-X[1], -X[0])
def mul(X, Y):
    a, b, c, d = X[0] * Y[0], X[0] * Y[1], X[1] * Y[0], X[1] * Y[1]
    return rnd((min(min(a, b), min(c, d)), max(max(a, b), max(c, d))))
def inv(Y):
    assert Y[0] > 0 or Y[1] < 0
    return rnd((1 / Y[1], 1 / Y[0]))
def div(X, Y): return mul(X, inv(Y))
def isum(Fn, n):
    acc = (F(0), F(0))
    for i in range(n): acc = add(acc, Fn(i))
    return acc
def tCosQ(t):
    s = t * t
    return 1 + s * (F(-1, 2) + s * (F(1, 24) + s * (F(-1, 720) + s * (F(1, 40320) + s * F(-1, 3628800)))))
def tSinQ(t):
    s = t * t
    return t * (1 + s * (F(-1, 6) + s * (F(1, 120) + s * (F(-1, 5040) + s * (F(1, 362880) + s * F(-1, 39916800))))))
errQ = F(13, 5748019200)
def sin01(X): assert 0 <= X[0] and X[1] <= 1; return (rdn(tSinQ(X[0]) - errQ), rup(tSinQ(X[1]) + errQ))
def cos01(X): assert 0 <= X[0] and X[1] <= 1; return (rdn(tCosQ(X[1]) - errQ), rup(tCosQ(X[0]) + errQ))
piI = (F(314159265358979323846, 10 ** 20), F(314159265358979323847, 10 ** 20))
s2I = (F(14142135623730950488, 10 ** 19), F(14142135623730950489, 10 ** 19))
t0I = mul(s2I, pt(F(1, 2)))
sthI = sin01(t0I); cthI = cos01(t0I)
CN = [1000000000, 12310798, -15041681, 3867664, 6489926, -992327, 5580097, -6846472, 3781297, -5670353, 3355089, -450523, -218483]
cAM = [F(x, 10 ** 9) for x in CN]
def wI(k): return s2I if k == 0 else mul(pt(2 * k), piI)
def haS(j): return sthI if j == 0 else pt(0)
def haC(j): return cthI if j == 0 else pt((-1) ** j)
def sinHm(j, k): return sub(mul(haS(j), haC(k)), mul(haC(j), haS(k)))
def cosHm(j, k): return add(mul(haC(j), haC(k)), mul(haS(j), haS(k)))
def sinHp(j, k): return add(mul(haS(j), haC(k)), mul(haC(j), haS(k)))
def cosHp(j, k): return sub(mul(haC(j), haC(k)), mul(haS(j), haS(k)))
def sinW(k): return mul(pt(2), mul(haS(k), haC(k)))
def cosW(k): return sub(mul(haC(k), haC(k)), mul(haS(k), haS(k)))
def dm(j, k): return mul(pt(2), sub(wI(j), wI(k)))
def dp(j, k): return mul(pt(2), add(wI(j), wI(k)))
def dw(k): return mul(pt(2), wI(k))
def axq(j, k): return add(pt(F(1, 2)), div(sinW(k), dw(k))) if j == k else add(div(sinHm(j, k), dm(j, k)), div(sinHp(j, k), dp(j, k)))
def bxq(j, k): return neg(div(cosW(k), dw(k))) if j == k else sub(neg(div(cosHm(j, k), dm(j, k))), div(cosHp(j, k), dp(j, k)))
def cxq(j, k): return pt(F(-1, 2)) if j == k else pt(0)
def ayq(j, k): return pt(0) if j == k else add(div(sinHm(j, k), dm(j, k)), div(sinHp(j, k), dp(j, k)))
def byq(j, k): return pt(0) if j == k else sub(div(cosHm(j, k), dm(j, k)), div(cosHp(j, k), dp(j, k)))
def AqI(i): return add(isum(lambda k: mul(pt(cAM[i] * cAM[k]), axq(i, k)), 13), isum(lambda j: mul(pt(cAM[j] * cAM[i]), ayq(j, i)), 13))
def BqI(i): return add(isum(lambda k: mul(pt(cAM[i] * cAM[k]), bxq(i, k)), 13), isum(lambda j: mul(pt(cAM[j] * cAM[i]), byq(j, i)), 13))
def CqI(i): return isum(lambda k: mul(pt(cAM[i] * cAM[k]), cxq(i, k)), 13)
ZI = mul(pt(2), mul(sthI, sthI))
qA0 = [div(AqI(i), ZI) for i in range(13)]
qB0 = [div(BqI(i), ZI) for i in range(13)]
qC0 = [div(CqI(i), ZI) for i in range(13)]
if __name__ == "__main__":
    for i in range(13): print(i, float(qA0[i][0]), float(qA0[i][1] - qA0[i][0]), float(qB0[i][0]), float(qB0[i][1] - qB0[i][0]), float(qC0[i][0]))
    print("ZI", [float(z) for z in ZI], "sth", [float(z) for z in sthI])
