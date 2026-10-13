#!/usr/bin/env python3
"""How many LP-infeasible (Farkas) cells of a dump would a stronger propagation find empty: Gauss-Seidel tightening
(8 rounds), the reflection constraint g0 <= g6, and one pass of pair-sum triples s_(i,j) = s_(i,k) + s_(k,j).
Usage: farkprop.py DUMP.pkl"""
import sys, pickle, itertools
Q = 7; PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]; IDX = {p: t for t, p in enumerate(PAIRS)}
d = pickle.load(open(sys.argv[1], "rb")); leaves = d["leaves"] if isinstance(d, dict) else d
def gs(l, u, cons, rounds=8):
    l = list(l); u = list(u)
    for _ in range(rounds):
        ch = False
        for t in sorted(cons):
            Lb, Ub = cons[t]; i, j = PAIRS[t]
            for r in range(i, j):
                sl = sum(l[i:j]); su = sum(u[i:j])
                Le = sl if Lb is None else max(sl, Lb); Ue = su if Ub is None else min(su, Ub)
                if Le > Ue: return None
                nu = Ue - (sl - l[r]); nl = Le - (su - u[r])
                if nu < u[r]: u[r] = nu; ch = True
                if nl > l[r]: l[r] = nl; ch = True
                if l[r] > u[r]: return None
        if not ch: break
    return l, u
def refl(l, u):
    l = list(l); u = list(u); u[0] = min(u[0], u[Q - 1]); l[Q - 1] = max(l[Q - 1], l[0])
    return None if l[0] > u[0] or l[Q - 1] > u[Q - 1] else (l, u)
def triples(l, u, cons):
    """intervals for every pair sum from the box and the constraints, then one pass over s_(i,j) = s_(i,k) + s_(k,j)"""
    I = {}
    for t, (i, j) in enumerate(PAIRS):
        lo, hi = sum(l[i:j]), sum(u[i:j])
        if t in cons:
            Lb, Ub = cons[t]
            if Lb is not None: lo = max(lo, Lb)
            if Ub is not None: hi = min(hi, Ub)
        if lo > hi: return None
        I[(i, j)] = [lo, hi]
    for i in range(Q + 1):
        for j in range(i + 2, Q + 1):
            for k in range(i + 1, j):
                a, b, c = I[(i, k)], I[(k, j)], I[(i, j)]
                c[0] = max(c[0], a[0] + b[0]); c[1] = min(c[1], a[1] + b[1])
                a[0] = max(a[0], c[0] - b[1]); a[1] = min(a[1], c[1] - b[0])
                b[0] = max(b[0], c[0] - a[1]); b[1] = min(b[1], c[1] - a[0])
                if a[0] > a[1] or b[0] > b[1] or c[0] > c[1]: return None
    return I
n = 0; c_gs = c_refl = c_tri = c_all = 0
for box, cons, kind, pay in leaves:
    if kind != 8: continue
    n += 1; l = [x[0] for x in box]; u = [x[1] for x in box]
    g = gs(l, u, cons); c_gs += g is None
    r = refl(l, u); rr = None if r is None else gs(r[0], r[1], cons); c_refl += rr is None
    c_tri += triples(l, u, cons) is None
    x = refl(l, u)
    if x is not None: x = gs(x[0], x[1], cons)
    if x is not None: x = triples(x[0], x[1], cons)
    c_all += x is None
print(f"{n} LP-infeasible cells: caught by Gauss-Seidel x8 {c_gs}; + reflection g0<=g6 {c_refl}; pair-sum triples (one pass) {c_tri}; all three {c_all}")
