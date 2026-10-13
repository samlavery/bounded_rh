#!/usr/bin/env python3
"""Leaf count of the bisection certificate under alternative split rules (same `lower` as gen_w.size).
Usage: size_greedy.py Q npz cN rule   rule ∈ {widest, greedy, greedy2}"""
import sys, os, time, itertools
sys.set_int_max_str_digits(0); sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
from fractions import Fraction as Fr
import gen_w
from gen_w import G
Q = int(sys.argv[1]); npz = os.path.expanduser(sys.argv[2]); c = Fr(int(sys.argv[3]), 10**8); rule = sys.argv[4]
pairs, A, Bv = gen_w.load_weights(npz, Q)
adj = [A[(r, r+1)] for r in range(Q)]
S = [Fr(-(-(4 * c) // Bv[r]), 4) for r in range(Q)]
covers = [G.phase1(c / adj[r], S[r]) for r in range(Q)]
bads = [cv[1] for cv in covers]
terms = [(A[(i, j)], tuple(range(i, j))) for (i, j) in pairs]
def lower(box):
    tot = sum(Bv[r] * box[r][0] for r in range(Q))
    for coef, idxs in terms:
        if coef == 0: continue
        lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
        tot += coef * G.Wmulti(lo, hi)
    return tot
count = [0]; nodes = [0]
def children(box, k):
    m = (box[k][0] + box[k][1]) / 2
    a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
    return tuple(a), tuple(b2)
def subdivide(box, depth=0):
    if sum(Bv[r] * box[r][0] for r in range(Q)) >= c: count[0] += 1; return True
    if lower(box) >= c: count[0] += 1; return True
    if depth > 80 or count[0] > 3 * 10**6: return False
    nodes[0] += 1
    w = [b[1] - b[0] for b in box]
    if rule == "widest":
        k = w.index(max(w))
    else:
        best = None
        for kk in range(Q):
            if w[kk] == 0: continue
            a, b2 = children(box, kk)
            la, lb = lower(a), lower(b2)
            if rule == "greedy": score = min(la, lb)
            elif rule == "greedy2": score = (la >= c) + (lb >= c) + 0 * min(la, lb) if (la >= c or lb >= c) else min(la, lb) - c
            elif rule in ("balanced", "passfirst"):
                if w[kk] * 2 < max(w) and not (rule == "passfirst" and la >= c and lb >= c): continue
                score = ((la >= c) + (lb >= c), min(la, lb))
            elif rule == "balanced4":
                if w[kk] * 4 < max(w): continue
                score = ((la >= c) + (lb >= c), min(la, lb))
            elif rule == "passfirst_sum":
                if w[kk] * 2 < max(w) and not (la >= c and lb >= c): continue
                score = ((la >= c) + (lb >= c), la + lb)
            elif rule == "passfirst_sum4":
                if w[kk] * 4 < max(w) and not (la >= c and lb >= c): continue
                score = ((la >= c) + (lb >= c), la + lb)
            elif rule == "passfirst_sum8":
                if w[kk] * 8 < max(w) and not (la >= c and lb >= c): continue
                score = ((la >= c) + (lb >= c), la + lb)
            elif rule == "passfirst_gain4":
                if w[kk] * 4 < max(w) and not (la >= c and lb >= c): continue
                score = ((la >= c) + (lb >= c), min(la, lb) + (la + lb) / 4)
            elif rule == "lookahead2":
                if w[kk] * 2 < max(w) and not (la >= c and lb >= c): continue
                def best_child_score(bx, lbx):
                    if lbx >= c: return (2, 2 * c)
                    wb = [u - l for l, u in bx]; bs = None
                    for k2 in range(Q):
                        if wb[k2] == 0 or wb[k2] * 2 < max(wb): continue
                        a2, b22 = children(bx, k2); l1, l2 = lower(a2), lower(b22)
                        sc = ((l1 >= c) + (l2 >= c), l1 + l2)
                        if bs is None or sc > bs: bs = sc
                    return bs
                sa, sb = best_child_score(a, la), best_child_score(b2, lb)
                score = ((la >= c) + (lb >= c), sa[0] + sb[0], sa[1] + sb[1])
            if best is None or score > best[0]: best = (score, kk)
        k = best[1]
    a, b2 = children(box, k)
    return subdivide(a, depth + 1) and subdivide(b2, depth + 1)
t = time.time(); ok = True
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    box = tuple(bads[r][tup[r]] for r in range(Q))
    if sum(Bv[r] * box[r][0] for r in range(Q)) >= c: count[0] += 1; continue
    if not subdivide(box): ok = False; break
print(f"rule={rule} c={float(c):.8f}: {'OK' if ok else 'FAIL'} leaves={count[0]} internal={nodes[0]} ({time.time()-t:.0f}s)", flush=True)
