"""AM-window kernel (AMTOPA's first 13 window terms) for the stage-G certificate.

k(x) = K(x)/K(0),  K(x) = int_{-1/2}^{1/2} v(t) cos(2 pi x t) dt,  v(t) = sum_{j<13} c_j cos(w_j t),  w_0 = sqrt2, w_j = 2 pi j.
Closed form (x real, D = 1 - 2 b^2 != 0, b = pi x):
  k(x) = N/D + rho * sum_{j=1}^{12} c_j (sinc(pi(x-j)) + sinc(pi(x+j)))/2,
  N = cos b - 2 gam b sin b,  gam = a cot a,  rho = a / sin a,  a = sqrt2/2   (c_0 = 1).
Derivatives: sinc' = s1, s1' = s2 with s1(t) = (t cos t - sin t)/t^2, s2(t) = (-t^2 sin t - 2 t cos t + 2 sin t)/t^3.
w = k^2, w' = 2 k k', w'' = 2 (k'^2 + k k'').

Integer cell pipeline (exact replica of the planned Lean evaluator; intervals of integers at scale DZ = 10^15):
the MT trigonometric base of `wz.pipeline` (cos, sin of pi x on the cell by Taylor polynomials at the nearest
half-integer anchor), N, D, M, N2 as in the MT cells, the far sinc terms through the reciprocal powers of x -+ j
(monotone on the cell), the near term (anchor k = 2 j0) through Taylor polynomials of sinc, s1, s2 at t = pi |x - j0|.
"""
import math, os, sys
from functools import lru_cache
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "pyr"))
from wz import (DZ, PLN, PUN, GLN, GUN, ERRD, SC, SW, ndiv, ndivc, nsub, cosP, cosN, sinP, sinN, cosLo, cosHi, sinLo,
                sinHi, imulZZ, iaddZ, isubZ, csA, kside)

CN = [1000000000, 12378982, -12602495, 4164033, 5741405, -1724025, 6219280, -8047828, 6321519, -5241981, -892658,
      560544, -431207]
if os.environ.get("AMWIN"):          # a re-optimised window (window-scope's rwin*.json): only the numerators change
    import json as _json
    CN = [int(c) for c in _json.load(open(os.environ["AMWIN"]))["cnum"]]
    assert len(CN) == 13 and CN[0] == 1000000000
NJ = len(CN) - 1
CF = np.array(CN, float) / 1e9

# ------------------------------------------------------------------ float model (steering only)
A_ = math.sqrt(2) / 2
GAM = A_ * math.cos(A_) / math.sin(A_)
RHO = A_ / math.sin(A_)

def _sinc(t): return np.sinc(np.asarray(t, float) / np.pi)
def _s1(t):
    t = np.asarray(t, float); out = np.empty_like(t); sm = np.abs(t) < 1e-3; z = t[sm]
    out[sm] = -z / 3 + z ** 3 / 30 - z ** 5 / 840
    z = t[~sm]; out[~sm] = (z * np.cos(z) - np.sin(z)) / z ** 2
    return out
def _s2(t):
    t = np.asarray(t, float); out = np.empty_like(t); sm = np.abs(t) < 1e-2; z = t[sm]
    out[sm] = -1 / 3 + z ** 2 / 10 - z ** 4 / 168 + z ** 6 / 6480
    z = t[~sm]; out[~sm] = (-z ** 2 * np.sin(z) - 2 * z * np.cos(z) + 2 * np.sin(z)) / z ** 3
    return out

def kders(x):
    """k, k', k'' (float, vectorised)"""
    x = np.atleast_1d(np.asarray(x, float)); b = np.pi * x
    N = np.cos(b) - 2 * GAM * b * np.sin(b); D = 1 - 2 * b * b
    Nb = -(1 + 2 * GAM) * np.sin(b) - 2 * GAM * b * np.cos(b); M = Nb * D + 4 * b * N
    N2 = -(1 + 4 * GAM) * np.cos(b) + 2 * GAM * b * np.sin(b)
    k = N / D; k1 = np.pi * M / D ** 2; k2 = np.pi ** 2 * (N2 * D ** 2 + 4 * N * D + 8 * b * M) / D ** 3
    for j in range(1, NJ + 1):
        tm = np.pi * (x - j); tp = np.pi * (x + j); c = CF[j] * RHO / 2
        k = k + c * (_sinc(tm) + _sinc(tp)); k1 = k1 + c * np.pi * (_s1(tm) + _s1(tp))
        k2 = k2 + c * np.pi ** 2 * (_s2(tm) + _s2(tp))
    return k, k1, k2
def w_exact(x): return kders(x)[0] ** 2
def w1_exact(x): k, k1, _ = kders(x); return 2 * k * k1
def w2(x): k, k1, k2 = kders(x); return 2 * (k1 * k1 + k * k2)
# steering: tabulated on the grid i / (4 SC), linear interpolation (x < 80); exact beyond
_TX = np.arange(0, 80 * SC * 4 + 2) / (4.0 * SC)
_TK = None
def _tab():
    global _TK
    if _TK is None:
        k, k1, _ = kders(_TX); _TK = (k * k, 2 * k * k1)
    return _TK
def w(x):
    x = np.asarray(x, float); T = _tab()
    return np.interp(np.abs(x), _TX, T[0])
def w1(x):
    x = np.asarray(x, float); T = _tab()
    return np.sign(x) * np.interp(np.abs(x), _TX, T[1])

# ------------------------------------------------------------------ integer interval arithmetic (scale DZ)
def fl(a, b): return a // b                    # floor, b > 0 (Lean: Int.ediv / Int.fdiv agree for b > 0)
def ce(a, b): return -((-a) // b)              # ceiling, b > 0
def iadd(I, J): return (I[0] + J[0], I[1] + J[1])
def isub(I, J): return (I[0] - J[1], I[1] - J[0])
def ineg(I): return (-I[1], -I[0])
def imul(I, J):
    p = (I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1])
    return (fl(min(p), DZ), ce(max(p), DZ))
def iscl(e, I):
    """integer multiple, no rounding"""
    return (e * I[0], e * I[1]) if e >= 0 else (e * I[1], e * I[0])
def idivn(I, n):
    """division by a positive integer n, rounded outward"""
    return (fl(I[0], n), ce(I[1], n))
def idivp(I, E):
    """I / E for an interval E = [E0, E1] with E0 > 0 (both at scale DZ)"""
    lo = fl(I[0] * DZ, E[1]) if I[0] >= 0 else fl(I[0] * DZ, E[0])
    hi = ce(I[1] * DZ, E[0]) if I[1] >= 0 else ce(I[1] * DZ, E[1])
    return (lo, hi)

# constants at scale DZ (floor, ceil); the Lean side proves each enclosure
PIC = (3141592653589793, 3141592653589794)
GAMI2 = (2 * GLN * 100000, 2 * GUN * 100000)            # 2 gam  (the MT GAMI)
G1I = (DZ + GAMI2[0], DZ + GAMI2[1])                   # 1 + 2 gam
G2I = (DZ + 2 * GAMI2[0], DZ + 2 * GAMI2[1])           # 1 + 4 gam
# rho = a / sin a, sigma = rho / pi, tau = rho pi; from 6496369368e-10 <= sin a <= 6496369414e-10 (MT bounds)
_SL, _SU = 6496369368, 6496369414
_AL, _AU = 7071067811865475244, 7071067811865475245     # a * 10^19
RHOI = (fl(_AL * 10 ** 6, _SU), ce(_AU * 10 ** 6, _SL))
SIGI = (fl(RHOI[0] * DZ, PIC[1]), ce(RHOI[1] * DZ, PIC[0]))
TAUI = (fl(RHOI[0] * PIC[0], DZ), ce(RHOI[1] * PIC[1], DZ))
PI2I = (fl(PIC[0] * PIC[0], DZ), ce(PIC[1] * PIC[1], DZ))

def check_consts():
    assert PIC[0] / DZ <= math.pi <= PIC[1] / DZ
    for I, v in ((RHOI, RHO), (SIGI, RHO / math.pi), (TAUI, RHO * math.pi), (G1I, 1 + 2 * GAM), (G2I, 1 + 4 * GAM)):
        assert I[0] / DZ <= v <= I[1] / DZ, (I, v)
        assert (I[1] - I[0]) / DZ < 1e-7

# Taylor polynomials at scale DZ, as positive / negative parts (each increasing in T >= 0)
def sincP(T): return 39916800 * DZ ** 10 + 332640 * T ** 4 * DZ ** 6 + 110 * T ** 8 * DZ ** 2
def sincN(T): return 6652800 * T ** 2 * DZ ** 8 + 7920 * T ** 6 * DZ ** 4 + T ** 10
SINCD = 39916800 * DZ ** 9
# s1 = -t/3 + t^3/30 - t^5/840 + t^7/45360 - t^9/3991680 ; common denominator 3991680
def s1P(T): return 133056 * T ** 3 * DZ ** 6 + 88 * T ** 7 * DZ ** 2
def s1N(T): return 1330560 * T * DZ ** 8 + 4752 * T ** 5 * DZ ** 4 + T ** 9
S1D = 3991680 * DZ ** 8
# s2 = -1/3 + t^2/10 - t^4/168 + t^6/6480 - t^8/443520 + t^10/39916800 ; denominator 39916800
def s2P(T): return 3991680 * T ** 2 * DZ ** 8 + 6160 * T ** 6 * DZ ** 4 + T ** 10
def s2N(T): return 13305600 * DZ ** 10 + 237600 * T ** 4 * DZ ** 6 + 90 * T ** 8 * DZ ** 2
S2D = 39916800 * DZ ** 9

@lru_cache(maxsize=None)
def base(LN, UN):
    """the MT trigonometric base of the cell [LN, UN] / SC (as `wz.pipeline`) plus the bookkeeping the AM cell needs"""
    sc = SC
    k, side = kside(LN, UN, sc)
    LLO = ndiv(LN * DZ, sc); UHI = ndivc(UN * DZ, sc); AD = k * (DZ // 2)
    RLO = nsub(LLO, AD) if side else nsub(AD, UHI)
    RHI = nsub(UHI, AD) if side else nsub(AD, LLO)
    TLZ = ndiv(PLN * RLO, 10 ** 20); TUZ = ndivc(PUN * RHI, 10 ** 20)
    CLZ = cosLo(TUZ) - ERRD; CUZ = cosHi(TLZ) + ERRD; SLZ = sinLo(TLZ) - ERRD; SUZ = sinHi(TUZ) + ERRD
    cA, sA = csA(k)
    if side:
        CX = isubZ(imulZZ(cA, (CLZ, CUZ)), imulZZ(sA, (SLZ, SUZ))); SX = iaddZ(imulZZ(sA, (CLZ, CUZ)), imulZZ(cA, (SLZ, SUZ)))
    else:
        CX = iaddZ(imulZZ(cA, (CLZ, CUZ)), imulZZ(sA, (SLZ, SUZ))); SX = isubZ(imulZZ(sA, (CLZ, CUZ)), imulZZ(cA, (SLZ, SUZ)))
    BLZ = ndiv(PLN * LLO, 10 ** 20); BUZ = ndivc(PUN * UHI, 10 ** 20)
    ok = (LN <= UN and TUZ <= DZ and (k * sc <= 2 * LN if side else 2 * UN <= k * sc) and cosN(TUZ) <= cosP(TUZ)
          and cosN(TLZ) <= cosP(TLZ) and sinN(TLZ) <= sinP(TLZ) and sinN(TUZ) <= sinP(TUZ) and DZ * DZ < 2 * BLZ * BLZ)
    return ok, k, side, LLO, UHI, TLZ, TUZ, CX, SX, (BLZ, BUZ)

def recips(Y0, Y1, n):
    """[DZ^(n+1) / Y1^n, DZ^(n+1) / Y0^n]: the enclosure of 1/y^n for y in [Y0, Y1] / DZ, Y0 > 0"""
    return (fl(DZ ** (n + 1), Y1 ** n), ce(DZ ** (n + 1), Y0 ** n))

def farsums(k, LLO, UHI, order):
    """A_n = sum over far (j, +-) of c_j s_j / 2 * y^-(n+1), y = x -+ j, n <= order; None if a far y is not separated"""
    acc = [[0, 0] for _ in range(order + 1)]
    for j in range(1, NJ + 1):
        e = CN[j] if j % 2 == 0 else -CN[j]                      # c_j (-1)^j, scale 1e9
        ys = [(LLO + j * DZ, UHI + j * DZ, 1)]
        if 2 * j < k: ys.append((LLO - j * DZ, UHI - j * DZ, 1))
        elif 2 * j > k: ys.append((j * DZ - UHI, j * DZ - LLO, -1))
        for (Y0, Y1, sg) in ys:
            if Y0 <= 0: return None
            for n in range(order + 1):
                r = recips(Y0, Y1, n + 1)
                if sg < 0 and n % 2 == 0: r = (-r[1], -r[0])     # odd power of a negative y
                lo, hi = iscl(e, r)
                acc[n][0] += lo; acc[n][1] += hi
    return [idivn((a[0], a[1]), 2 * 10 ** 9) for a in acc]

def near(k, side, TLZ, TUZ, order):
    """B_n = c_j0 / 2 * pi^n * s_n(theta), theta = pi (x - j0), for the anchor k = 2 j0 (else zeros)"""
    j0 = k // 2
    if k % 2 or not (1 <= j0 <= NJ): return [(0, 0)] * (order + 1)
    S0 = (fl(sincP(TLZ) - sincN(TUZ), SINCD) - ERRD, ce(sincP(TUZ) - sincN(TLZ), SINCD) + ERRD)
    out = [S0]
    if order >= 1:
        G1 = (fl(s1P(TLZ) - s1N(TUZ), S1D) - 2 * ERRD, ce(s1P(TUZ) - s1N(TLZ), S1D) + 2 * ERRD)
        if not side: G1 = ineg(G1)
        out.append(imul(PIC, G1))
    if order >= 2:
        G2 = (fl(s2P(TLZ) - s2N(TUZ), S2D) - 5 * ERRD, ce(s2P(TUZ) - s2N(TLZ), S2D) + 5 * ERRD)
        out.append(imul(PI2I, G2))
    return [idivn(iscl(CN[j0], I), 2 * 10 ** 9) for I in out]

@lru_cache(maxsize=None)
def cellK(LN, UN, order):
    """(ok, [k, k', k''][:order+1]) enclosures on the cell [LN, UN] / SC"""
    ok, k, side, LLO, UHI, TLZ, TUZ, CX, SX, BI = base(LN, UN)
    if not ok: return False, None
    A = farsums(k, LLO, UHI, order)
    if A is None: return False, None
    B = near(k, side, TLZ, TUZ, order)
    PGI = (fl(GAMI2[0] * BI[0], DZ), ce(GAMI2[1] * BI[1], DZ))                 # 2 gam b
    NI = isub(CX, imul(PGI, SX))
    EI = (fl(2 * BI[0] * BI[0], DZ) - DZ, ce(2 * BI[1] * BI[1], DZ) - DZ)        # -D = 2 b^2 - 1
    if EI[0] <= 0: return False, None
    SA0 = imul(SX, A[0])
    K0 = iadd(idivp(ineg(NI), EI), iadd(imul(SIGI, SA0), imul(RHOI, B[0])))
    out = [K0]
    if order >= 1:
        DI = ineg(EI)
        NbI = ineg(iadd(imul(G1I, SX), imul(PGI, CX)))
        MI = iadd(imul(NbI, DI), imul(iscl(4, BI), NI))
        E2 = imul(EI, EI)
        CA0 = imul(CX, A[0]); SA1 = imul(SX, A[1])
        K1 = iadd(imul(PIC, idivp(MI, E2)), iadd(isub(imul(RHOI, CA0), imul(SIGI, SA1)), imul(RHOI, B[1])))
        out.append(K1)
    if order >= 2:
        N2I = isub(imul(PGI, SX), imul(G2I, CX))
        E3 = imul(E2, EI)
        P2 = iadd(isub(imul(N2I, E2), iscl(4, imul(NI, EI))), iscl(8, imul(BI, MI)))
        KM2 = ineg(imul(PI2I, idivp(P2, E3)))
        CA1 = imul(CX, A[1]); SA2 = imul(SX, A[2])
        F2 = iadd(iadd(ineg(imul(TAUI, SA0)), ineg(iscl(2, imul(RHOI, CA1)))), iadd(iscl(2, imul(SIGI, SA2)), imul(RHOI, B[2])))
        out.append(iadd(KM2, F2))
    return True, out

# ------------------------------------------------------------------ the three cell tests
def WZ(LN, UN, sc=SC):
    """w lower bound on the cell, units 1/SW (0 = no information)"""
    ok, K = cellK(LN, UN, 0)
    if not ok: return 0
    a = max(0, K[0][0], -K[0][1])
    return (a * a * SW) // (DZ * DZ)

U1 = 10 ** 9; KU1 = 2 * U1; EM = (1 << 32) - 1
@lru_cache(maxsize=None)
def w1cell(LN, UN):
    ok, K = cellK(LN, UN, 1)
    if not ok: return False, 0, 0
    W = iscl(2, imul(K[0], K[1]))
    return True, fl(W[0], DZ // U1), ce(W[1], DZ // U1)
def fP(LN, UN):
    ok, lo, hi = w1cell(LN, UN)
    return min(max(KU1 + lo, 0), EM) if ok else 0
def fM(LN, UN):
    ok, lo, hi = w1cell(LN, UN)
    return min(max(KU1 - hi, 0), EM) if ok else 0

KB = 1 << 20
def conv_ok(a, b):
    if not (a <= b and b + 1 <= KB): return False
    ok, K = cellK(a, b, 2)
    if not ok: return False
    k0, k1, k2 = K
    s = max(0, k1[0], -k1[1])
    return s * s + imul(k0, k2)[0] * DZ >= 0
def chain(lo, hi, minw=8):
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

if __name__ == "__main__":
    check_consts()
    sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
    from famq import kernel, frequencies, AMTOPA_C
    c = AMTOPA_C[:13]; wq = frequencies(13); k0 = kernel(0.0, c, wq)[0]
    xs = np.linspace(0.5, 15.9, 20001)
    kr = kernel(xs, c, wq) / k0
    k, k1, k2 = kders(xs)
    print("max |k - famq| =", np.abs(k - kr).max())
    h = 1e-5
    kp = (kders(xs + h)[0] - kders(xs - h)[0]) / (2 * h); kpp = (kders(xs + h)[1] - kders(xs - h)[1]) / (2 * h)
    print("max |k' - fd| =", np.abs(k1 - kp).max(), " max |k'' - fd| =", np.abs(k2 - kpp).max())
    # integer cells vs float truth
    import random
    random.seed(1)
    worst = [0, 0, 0]; nfail = 0
    for _ in range(3000):
        l = random.choice([0, 2, 4, 6, 8]); L = random.randrange(16384, 15 * SC); U_ = L + (1 << l)
        ok, K = cellK(L, U_, 2)
        if not ok: nfail += 1; continue
        xx = np.linspace(L / SC, U_ / SC, 9); kk = kders(xx)
        for n in range(3):
            lo, hi = K[n][0] / DZ, K[n][1] / DZ
            assert lo <= kk[n].min() + 1e-12 and kk[n].max() - 1e-12 <= hi, (L, U_, n, lo, hi, kk[n].min(), kk[n].max())
            worst[n] = max(worst[n], (hi - lo) - (kk[n].max() - kk[n].min()))
    print("cells not ok", nfail, "excess widths", worst)
    for L in (16384, 32768, 34000, 65536, 98304, 120000):
        for l in (0, 4, 6, 8):
            U_ = L + (1 << l); xx = np.linspace(L / SC, U_ / SC, 50)
            print(L, l, "WZ", WZ(L, U_) / SW, "true min w", w(xx).min(), "| w1", w1cell(L, U_), w1(xx).min(), w1(xx).max())

# ------------------------------------------------------------------ v2: monotone far sums F, F', F'' (planned Lean v2)
# F(x) = sum_{j != j0} e_j x/(x^2 - j^2) + [j0] e_j0 / (2 (x + j0)),  e_j = c_j (-1)^j;  F', F'' termwise.
# Each term (and each derivative) is monotone on the cell with a fixed sign; magnitudes are evaluated at the endpoints.
CE2 = [(j, abs(CN[j]), (CN[j] if j % 2 == 0 else -CN[j]) < 0) for j in range(1, NJ + 1)]
def far2(k, XL, XU, n):
    """(lo, hi) of F^(n) at scale DZ"""
    pl = ph = nl = nh = 0
    XL2, XU2 = XL * XL, XU * XU
    for (j, e, sg) in CE2:
        J = j * DZ; J2 = J * J
        if 2 * j == k:
            if n == 0: a0 = DZ ** 2 // (2 * (XU + J)); a1 = ce(DZ ** 2, 2 * (XL + J)); vneg = False
            elif n == 1: a0 = DZ ** 3 // (2 * (XU + J) ** 2); a1 = ce(DZ ** 3, 2 * (XL + J) ** 2); vneg = True
            else: a0 = DZ ** 4 // (XU + J) ** 3; a1 = ce(DZ ** 4, (XL + J) ** 3); vneg = False
        else:
            above = 2 * j < k
            if above: Xa, Xa2, Xb, Xb2 = XU, XU2, XL, XL2          # a0 at XU, a1 at XL
            else: Xa, Xa2, Xb, Xb2 = XL, XL2, XU, XU2
            Da = abs(Xa2 - J2); Db = abs(Xb2 - J2)
            if n == 0: a0 = Xa * DZ ** 2 // Da; a1 = ce(Xb * DZ ** 2, Db); vneg = not above
            elif n == 1: a0 = (Xa2 + J2) * DZ ** 3 // Da ** 2; a1 = ce((Xb2 + J2) * DZ ** 3, Db ** 2); vneg = True
            else: a0 = 2 * Xa * (Xa2 + 3 * J2) * DZ ** 4 // Da ** 3; a1 = ce(2 * Xb * (Xb2 + 3 * J2) * DZ ** 4, Db ** 3); vneg = not above
        if sg != vneg: nl += e * a0; nh += e * a1
        else: pl += e * a0; ph += e * a1
    return idivn((pl - nh, ph - nl), 10 ** 9)

def mulc(C, I):
    """positive constant interval C times I, at scale DZ"""
    lo = C[0] * I[0] if I[0] >= 0 else C[1] * I[0]
    hi = C[1] * I[1] if I[1] >= 0 else C[0] * I[1]
    return (fl(lo, DZ), ce(hi, DZ))

def near2(k, side, TLZ, TUZ, order):
    j0 = k // 2
    if k % 2 or not (1 <= j0 <= NJ): return [(0, 0)] * (order + 1)
    S0 = (fl(sincP(TLZ) - sincN(TUZ), SINCD) - ERRD, ce(sincP(TUZ) - sincN(TLZ), SINCD) + ERRD)
    out = [S0]
    if order >= 1:
        G1 = (fl(s1P(TLZ) - s1N(TUZ), S1D) - 2 * ERRD, ce(s1P(TUZ) - s1N(TLZ), S1D) + 2 * ERRD)
        if not side: G1 = ineg(G1)
        out.append(mulc(PIC, G1))
    if order >= 2:
        G2 = (fl(s2P(TLZ) - s2N(TUZ), S2D) - 5 * ERRD, ce(s2P(TUZ) - s2N(TLZ), S2D) + 5 * ERRD)
        out.append(mulc(PI2I, G2))
    return [idivn(iscl(CN[j0], I), 2 * 10 ** 9) for I in out]

@lru_cache(maxsize=None)
def cellK2(LN, UN, order):
    ok, k, side, LLO, UHI, TLZ, TUZ, CX, SX, BI = base(LN, UN)
    if not ok: return False, None
    for j in range(1, NJ + 1):
        if 2 * j < k and not (j * DZ < LLO): return False, None
        if 2 * j > k and not (UHI < j * DZ): return False, None
    F = [far2(k, LLO, UHI, n) for n in range(order + 1)]
    B = near2(k, side, TLZ, TUZ, order)
    PGI = (fl(GAMI2[0] * BI[0], DZ), ce(GAMI2[1] * BI[1], DZ))
    NI = isub(CX, mulc(PGI, SX))
    EI = (fl(2 * BI[0] * BI[0], DZ) - DZ, ce(2 * BI[1] * BI[1], DZ) - DZ)
    if EI[0] <= 0: return False, None
    SF0 = imul(SX, F[0])
    K0 = iadd(idivp(ineg(NI), EI), iadd(mulc(SIGI, SF0), mulc(RHOI, B[0])))
    out = [K0]
    if order >= 1:
        MI = iadd(mulc(EI, iadd(mulc(G1I, SX), mulc(PGI, CX))), mulc(iscl(4, BI), NI))
        E2 = (fl(EI[0] * EI[0], DZ), ce(EI[1] * EI[1], DZ))
        CF0 = imul(CX, F[0]); SF1 = imul(SX, F[1])
        K1 = iadd(mulc(PIC, idivp(MI, E2)), iadd(iadd(mulc(RHOI, CF0), mulc(SIGI, SF1)), mulc(RHOI, B[1])))
        out.append(K1)
    if order >= 2:
        N2I = isub(mulc(PGI, SX), mulc(G2I, CX))
        E3 = (fl(E2[0] * EI[0], DZ), ce(E2[1] * EI[1], DZ))
        P2 = iadd(isub(mulc(E2, N2I), iscl(4, mulc(EI, NI))), iscl(8, mulc(BI, MI)))
        KM2 = ineg(mulc(PI2I, idivp(P2, E3)))
        CF1 = imul(CX, F[1]); SF2 = imul(SX, F[2])
        F2 = iadd(isub(iscl(2, mulc(RHOI, CF1)), mulc(TAUI, SF0)), iadd(mulc(SIGI, SF2), mulc(RHOI, B[2])))
        out.append(iadd(KM2, F2))
    return True, out

def WZ2(LN, UN, sc=SC):
    ok, K = cellK2(LN, UN, 0)
    if not ok: return 0
    a = max(0, K[0][0], -K[0][1])
    return (a * a * SW) // (DZ * DZ)
@lru_cache(maxsize=None)
def w1cell2(LN, UN):
    ok, K = cellK2(LN, UN, 1)
    if not ok: return False, 0, 0
    W = iscl(2, imul(K[0], K[1]))
    return True, fl(W[0], DZ // U1), ce(W[1], DZ // U1)
def fP2(LN, UN):
    ok, lo, hi = w1cell2(LN, UN)
    return min(max(KU1 + lo, 0), EM) if ok else 0
def fM2(LN, UN):
    ok, lo, hi = w1cell2(LN, UN)
    return min(max(KU1 - hi, 0), EM) if ok else 0
def conv_ok2(a, b):
    if not (a <= b and b + 1 <= KB): return False
    ok, K = cellK2(a, b, 2)
    if not ok: return False
    k0, k1, k2 = K
    s = max(0, k1[0], -k1[1])
    return s * s + imul(k0, k2)[0] * DZ >= 0

# ------------------------------------------------------------------ the evaluator in use (v2 = the Lean AMW/GCell)
if os.environ.get("AMV1", "0") != "1":
    WZ, fP, fM, conv_ok = WZ2, fP2, fM2, conv_ok2
