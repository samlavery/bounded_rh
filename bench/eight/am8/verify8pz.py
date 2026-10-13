#!/usr/bin/env python3
"""Independent replay of the emitted pair-cell certificate (DATA.json) with the kernel's integer semantics.

It reads only DATA.json, tz.py (T1, Z) and the generic table readers (pyr_table.Pyr, the Lean `lb` replica).  For every root
it starts from the root cell and decodes the walk bit by bit:
- at every node, T1 (TZ.md §1), or the exact closure tz.close when the settings say TCLOSE (then also checking the
  kernel's incremental form tz.close_split against it), with an empty cell reading no bits;
- a split: [1][axis 5] at the kernel midpoint;
- a leaf: [0], then reflected (u_6 < l_0) or [kind 0] and the minorant check.
The minorant check is `mcheckP`, at the kernel's scale 1024: weights m = λ·2^(10−LB), SIG = (1024·U1·SA) >> SIGSH, tcheck
with the one-point case, PLO and Z (TZ.md §2), constants lb(L, max(U, L+1)), and charges anchored at the gap sums.
It must end every walk exactly at its bit count with 0 failures.  Usage: verify8pz.py DATA.json"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
for p_ in (os.path.join(HERE, "..", "..", "pyr"), HERE): sys.path.insert(0, p_)
import tz
from pyr_table import Pyr

D = json.load(open(sys.argv[1])); PR = D['params']
Q = len(D['bN']); PAIRS = tz.pairs(Q); NP = len(PAIRS)   # gaps from the data (7 for n = 8; k for a truncated window)
NOREFL = D['settings'].get('NOREFL') == '1'   # no mirror symmetry: no reflected leaves
TCLOSE = D['settings'].get('TCLOSE') == '1'   # node tightening: the exact closure (tz.close) instead of T1
TIGHT = tz.close if TCLOSE else tz.t1
# BSPLIT: a split reads a mode bit after its axis; mode 1 cuts at the region boundary z (params BND, sorted) nearest the
# midpoint with lo + BMARG <= z <= hi - BMARG, the first such z in BND order on a tie (|2z - lo - hi| compared)
BSPLIT = bool(PR.get('BSPLIT', 0)); BMARG = PR.get('BMARG', 64); BND = PR.get('BND', [])
def bcut(lo, hi):
    best = None
    for z in BND:
        if lo + BMARG <= z <= hi - BMARG and (best is None or abs(2 * z - lo - hi) < abs(2 * best - lo - hi)): best = z
    assert best is not None, ("mode-1 split without a region boundary", lo, hi)
    return best
SC, U, U1, KU1, RU = PR['SC'], PR['U'], PR['U1'], PR['KU1'], PR['RU']
SA = D['SA']; cN = D['cN']; aN = D['aN']; bN = D['bN']
LSK = 1024; LB = PR['LB']; MW = 1 << (10 - LB); JSH = PR['JSH']; JB = PR['JB']; GS = PR['GSH']; PLO = PR['PLO']
SIG = (1024 * U1 * SA) >> PR['SIGSH']; QB = PR['QB']; ZN = PR['ZEXT']
NADJ = [t for t, (i, j) in enumerate(PAIRS) if j - i >= 2]
ACT = [t for t in range(NP) if aN[t] > 0]
T = D['tables']
W = Pyr(**{k: v for k, v in PR['w_pyr'].items()}); W.TOPN = int(T['TOP'], 16); W.BKN = {int(j): int(v, 16) for j, v in T['BK'].items()}
DPc = Pyr(**{k: v for k, v in PR['d_pyr'].items()})
TOPD = int(T['TOPD'], 16); BKD = {int(j): int(v, 16) for j, v in T['BKD'].items()}
M32 = (1 << 32) - 1
def entry2(l, i):
    PB, KT = DPc.PB, DPc.KT
    if l > KT: return 0
    if PB < l: return (TOPD >> (64 * ((1 << (KT - l)) + i))) & ((1 << 64) - 1)
    j = i >> (PB - l); X = BKD.get(j, 0); r = X & 31; kk = r if l <= r else l; d = max(0, PB - kk)
    idx = ((1 << d) - 1) + max(0, (i >> (kk - l)) - (j << d))
    return ((X >> 5) >> (64 * idx)) & ((1 << 64) - 1)
_c2 = {}
def lb2(lo, hi):
    k_ = (lo, hi)
    if k_ in _c2: return _c2[k_]
    cv = DPc.cover(lo, hi)
    if not cv or cv[-1] is None: v = (0, 0)
    else:
        es = [entry2(l, i) for (l, i) in cv]; v = (min(e & M32 for e in es), min(e >> 32 for e in es))
    _c2[k_] = v; return v
def lbw(lo, hi): return W.lb(lo, hi)
PT = {int(x): int(v, 16) for x, v in T['points']}
if os.environ.get("PTMERGE"):   # the point function the instance reads: its own points, else the base certificate's table
    _B = {int(x): int(v, 16) for x, v in json.load(open(os.environ["PTMERGE"]))['tables']['points']}
    PT = {**_B, **PT}; print(f"point table merged with {os.environ['PTMERGE']}: {len(PT)} points")
def pw(x): return PT.get(x, 0) & M32
def pd(x): v = PT.get(x, 0); return (v >> 32) & M32, v >> 64
RGK = {int(k): (v[0], v[1]) for k, v in T['REG'].items()}

def gpt(L, Uu, jj):
    if jj == PLO: return L
    gs = GS if (jj >> (JSH + 1)) & 1 else 8; j = jj & ((1 << (JSH + 1)) - 1); gm = (1 << gs) - 1
    ga = ((L + gm) >> gs) << gs; gb = (Uu >> gs) << gs; x = ((L + (((Uu - L) * j) >> JSH)) >> gs) << gs
    r = ga if x <= ga else (gb if gb <= x else x)
    return r if ga <= gb else (r if L <= r <= Uu else None)
def tcheck(L, Uu, p):
    P_, M_ = pd(p)
    if L == Uu == p: return P_ >= 1 and M_ >= 1
    k = (p + 16384) >> 15
    if k >= 16 or k not in RGK: return False
    za, zb = RGK[k]
    if not (za <= p <= zb and L <= p <= Uu): return False
    if P_ < 1 or M_ < 1: return False
    if Uu > zb:
        e = lb2(zb, Uu)[0]
        if (e < 1 or e + M_ < 4 * U1) and not (ZN and tz.zext(zb, Uu, p, pw(p), P_, M_, True, lbw, n=ZN)): return False
    if L < za:
        e = lb2(L, za)[1]
        if (e < 1 or e + P_ < 4 * U1) and not (ZN and tz.zext(L, za, p, pw(p), P_, M_, False, lbw, n=ZN)): return False
    return True
def weights(k, m):
    if k == 1: return 0, LSK, 0
    if k == 2: return LSK - m, m, 0
    if k == 3: return 0, LSK - m, m
    return LSK, 0, 0
def mcheck(l, u, cons, I, terms, Ys):
    lhs = LSK * U * sum(bN[r] * l[r] for r in range(Q)); rhs = LSK * cN * SC * U
    SL = [LSK * U1 * bN[r] for r in range(Q)]; SK = [0] * Q
    for t, (k, j1, j2, lam) in terms:
        i, j = PAIRS[t]; L, Uu = I[(i, j)]; L0 = sum(l[i:j]); m = lam * MW
        if m > LSK: return False
        if L0 > L: stats['anchor'] += 1; return False
        c_, l1, l2 = weights(k, m)
        for lk, jj in ((l1, j1), (l2, j2)):
            if lk == 0: continue
            pk = gpt(L, Uu, jj)
            if pk is None or not tcheck(L, Uu, pk): return False
            P_, M_ = pd(pk); v = pw(pk)
            lhs += SC * aN[t] * lk * v + RU * aN[t] * lk * max(0, M_ - KU1) * (pk - L0)
            rhs += RU * aN[t] * lk * max(0, KU1 - M_) * (pk - L0)
            for r in range(i, j): SL[r] += aN[t] * lk * P_; SK[r] += aN[t] * lk
        if c_: lhs += SC * aN[t] * c_ * lbw(L, max(Uu, L + 1))
    for (t, side), yq in Ys.items():
        Y = yq * SIG; i, j = PAIRS[t]; L0 = sum(l[i:j]); Lb, Ub = cons[(i, j)]
        if L0 > Lb: stats['anchor'] += 1; return False
        if side == 0:
            for r in range(i, j): SL[r] -= Y
            lhs -= RU * Y * (L0 - Lb)
        else:
            for r in range(i, j): SL[r] += Y
            lhs -= RU * Y * (Ub - L0)
    for r in range(Q): rhs += RU * (u[r] - l[r]) * max(0, KU1 * SK[r] - SL[r])
    return lhs >= rhs

stats = dict(split=0, empty=0, refl=0, M=0, fail=0, anchor=0)
for wk in D['walks']:
    W_ = int(wk['hex'], 16); nb = wk['nbits']; pos = 0
    def get(n):
        global pos
        v = (W_ >> pos) & ((1 << n) - 1); pos += n; return v
    stack = [([c[0] for c in wk['cell']], [c[1] for c in wk['cell']], {}, None)]
    while stack:
        l, u, cons, inc = stack.pop()
        r_ = TIGHT(l, u, cons, Q)
        if r_ is None: stats['empty'] += 1; continue
        l, u, cons, I = r_
        if inc is not None:   # the kernel's incremental closure (tz.close_split) must equal the closure from scratch
            assert inc == I, "close_split differs from close"; stats['inc'] = stats.get('inc', 0) + 1
        if get(1):
            ax = get(5); stats['split'] += 1
            md = get(1) if BSPLIT else 0
            if md: stats['bsplit'] = stats.get('bsplit', 0) + 1
            if ax < Q:
                m = bcut(l[ax], u[ax]) if md else (l[ax] + u[ax]) >> 1; uA = list(u); uA[ax] = m; lB = list(l); lB[ax] = m
                A = (l, uA, dict(cons)); B = (lB, u, dict(cons)); pr = (ax, ax + 1)
            else:
                pr = PAIRS[NADJ[ax - Q]]; lo, hi = cons[pr]; m = bcut(lo, hi) if md else (lo + hi) >> 1
                cA = dict(cons); cA[pr] = (lo, m); cB = dict(cons); cB[pr] = (m, hi)
                A = (l, u, cA); B = (l, u, cB)
            # the kernel's form (skip=True: 43 candidates per child), checked against all 56
            iA = tz.close_split(I, pr[0], pr[1], m, 0, Q, skip=True) if TCLOSE else None
            iB = tz.close_split(I, pr[0], pr[1], m, 1, Q, skip=True) if TCLOSE else None
            if TCLOSE:
                assert iA == tz.close_split(I, pr[0], pr[1], m, 0, Q) and iB == tz.close_split(I, pr[0], pr[1], m, 1, Q)
            stack.append(B + (iB,)); stack.append(A + (iA,)); continue
        if u[Q - 1] < l[0] and not NOREFL: stats['refl'] += 1; continue
        kind = get(1); assert kind == 0, "Farkas leaves are not expected"
        terms = []
        for t in ACT:
            k = get(2); j1 = get(JB) if k >= 1 else 0; j2 = get(JB) if k == 3 else 0; lam = get(LB) if k >= 2 else 0
            terms.append((t, (k, j1, j2, lam)))
        Ys = {}
        while get(1):
            c = get(5); side = get(1); Ys[(NADJ[c], side)] = get(QB)
        stats['M'] += 1
        if not mcheck(l, u, cons, I, terms, Ys): stats['fail'] += 1
    assert pos == nb, ("walk length", pos, nb)
print(f"replayed {len(D['walks'])} walks: {stats}; every walk ends at its bit count")
assert stats['fail'] == 0
print("VERIFIED: 0 failures")
