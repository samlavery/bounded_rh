#!/usr/bin/env python3
"""Generic n-point sizing: fixed coefficients 2/(n-s), cover level c(n-1)/2, (n-1)-D bisection
(largest side first, midpoint).  Prints leaves and the constant for (n, c, p)."""
import sys, os, itertools, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/zeta-lab/hunts/ainta_seven_point"))
import three_point_gen as G, four_point_gen as G4
G4.extend_anchors(24)
sys.setrecursionlimit(1000000)

def coeffs(n):
    return [(Fr(2, n - (j - i)), tuple(range(i, j))) for i in range(n) for j in range(i+1, n)]

def run(n, cn, p, max_leaves):
    c = Fr(cn, 10**6); S = c * p; level = Fr(n-1, 2) * c
    CO = coeffs(n)
    clear, bad = G.phase1(level, S)
    nb = len(bad)
    def lower(box):
        tot = Fr(sum(b[0] for b in box), 1) / p
        for coef, idxs in CO:
            lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
            tot += coef * G.Wmulti(lo, hi)
        return tot
    count = [0]
    def subdivide(box, depth=0):
        if sum(b[0] for b in box) >= S: count[0] += 1; return True
        if lower(box) >= c: count[0] += 1; return True
        if depth > 80 or count[0] > max_leaves: return False
        w = [b[1]-b[0] for b in box]; k = w.index(max(w)); m = (box[k][0]+box[k][1])/2
        a = list(box); a[k] = (box[k][0], m); b = list(box); b[k] = (m, box[k][1])
        return subdivide(tuple(a), depth+1) and subdivide(tuple(b), depth+1)
    t = time.time(); seen = {}; ok = True
    for tup in itertools.product(range(nb), repeat=n-1):
        box = tuple(bad[i] for i in tup)
        if sum(b[0] for b in box) >= S: count[0] += 1; continue
        key = min(tup, tuple(reversed(tup)))
        if key in seen: count[0] += seen[key]; continue
        before = count[0]
        if not subdivide(box): ok = False; break
        seen[key] = count[0] - before
    m = (n - 1) + int(1/c); H_lo = Fr(3,2) - Fr(8274993018, 10**10); B = Fr(n-1, p)
    phi = (H_lo - B*(m-(n-1))/m) / (1 - c*(m-(n-1))/m)
    print(f"n={n} c={cn} p={p}: {'OK' if ok else 'FAIL/limit'} leaves={count[0]} nb={nb} bad={bad} Phi={float(phi):.7f} ({time.time()-t:.0f}s)", flush=True)

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 10**7)
