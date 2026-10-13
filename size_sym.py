#!/usr/bin/env python3
"""Leaf count with SYMMETRISED pair weights and the half-space g_0 <= g_{Q-1} only (boxes inside g_0 > g_{Q-1}
are covered by reflection).  Usage: size_sym.py Q npz cN"""
import sys, os, time, itertools
sys.set_int_max_str_digits(0); sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
from fractions import Fraction as Fr
import gen_w
from gen_w import G
Q = int(sys.argv[1]); npz = os.path.expanduser(sys.argv[2]); c = Fr(int(sys.argv[3]), 10**8)
pairs, A, Bv = gen_w.load_weights(npz, Q)
n = Q + 1
As = {(i, j): (A[(i, j)] + A[(n - 1 - j, n - 1 - i)]) / 2 for (i, j) in pairs}
Bs = [(Bv[r] + Bv[Q - 1 - r]) / 2 for r in range(Q)]
print("asymmetry of the LP weights: max |a - a_rev| =", float(max(abs(A[p] - As[p]) for p in pairs)), " max |b - b_rev| =", float(max(abs(Bv[r] - Bs[r]) for r in range(Q))))
adj = [As[(r, r+1)] for r in range(Q)]
S = [Fr(-(-(4 * c) // Bs[r]), 4) for r in range(Q)]
covers = [G.phase1(c / adj[r], S[r]) for r in range(Q)]
bads = [cv[1] for cv in covers]
terms = [(As[(i, j)], tuple(range(i, j))) for (i, j) in pairs]
def lower(box):
    tot = sum(Bs[r] * box[r][0] for r in range(Q))
    for coef, idxs in terms:
        lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
        tot += coef * G.Wmulti(lo, hi)
    return tot
count = [0]; skipped = [0]
def children(box, k):
    m = (box[k][0] + box[k][1]) / 2
    a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
    return tuple(a), tuple(b2)
def subdivide(box, depth=0, half=True):
    if half and box[0][0] >= box[Q - 1][1]: skipped[0] += 1; return True     # entirely in g_0 > g_{Q-1}: by reflection
    if sum(Bs[r] * box[r][0] for r in range(Q)) >= c: count[0] += 1; return True
    if lower(box) >= c: count[0] += 1; return True
    if depth > 80 or count[0] > 3 * 10**6: return False
    w = [b[1] - b[0] for b in box]; best = None
    for kk in range(Q):
        if w[kk] == 0: continue
        a, b2 = children(box, kk); la, lb = lower(a), lower(b2)
        both = la >= c and lb >= c
        if w[kk] * 4 < max(w) and not both: continue
        score = ((la >= c) + (lb >= c), la + lb)
        if best is None or score > best[0]: best = (score, kk)
    a, b2 = children(box, best[1])
    return subdivide(a, depth + 1, half) and subdivide(b2, depth + 1, half)
for half in (False, True):
    count[0] = 0; skipped[0] = 0; t = time.time(); ok = True
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        if not subdivide(box, 0, half): ok = False; break
    print(f"symmetrised weights, half-space={'on' if half else 'off'} c={float(c):.8f}: {'OK' if ok else 'FAIL'} leaves={count[0]} reflected-away boxes={skipped[0]} tuples={len(list(itertools.product(*[range(len(bd)) for bd in bads])))} ({time.time()-t:.0f}s)", flush=True)
