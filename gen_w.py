#!/usr/bin/env python3
"""Weighted n-point certificate: per-gap pressures b_r, pair weights a_ij (exact rationals),
per-gap cutoffs S_r = c/b_r, per-gap 1-D cover at level c/a_{r,r+1}, (n-1)-D bisection over
products of per-gap bad intervals.  Sizing mode prints leaves; emit mode (later) writes data."""
import sys, os, itertools, time, pickle
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, os.path.expanduser("~/work/zeta-lab/hunts/ainta_seven_point"))
import three_point_gen as G, four_point_gen as G4
G4.extend_anchors(24)
sys.setrecursionlimit(1000000)

def load_weights(npz, Q, da=10**6, db=10**8):
    d = np.load(npz); a, b = d['a'], d['b']
    pairs = [(i, j) for i in range(Q+1) for j in range(i+1, Q+1)]
    A = {pq: Fr(int(np.floor(v * da)), da) for pq, v in zip(pairs, a)}   # rounded DOWN: capacity <= 2 kept
    Bv = [Fr(int(np.floor(v * db)), db) for v in b]
    for s in range(1, Q+1):
        assert sum(v for (i, j), v in A.items() if j - i == s) <= 2
    return pairs, A, Bv

RULE = os.environ.get("RULE", "widest")   # bisection axis rule: widest | passfirst | balanced | passfirst_sum
WFRAC = int(os.environ.get("WFRAC", "2"))  # candidate axes: width ≥ max width / WFRAC
HALF = os.environ.get("HALF") == "1"      # certify only boxes meeting g_0 ≤ g_{Q-1}; the rest by reflection (symmetric weights)
def half_skip(box, Q): return HALF and box[0][0] > box[Q - 1][1]
XFAR = Fr(os.environ.get("XFAR", "0"))       # pieces starting at or beyond XFAR are rounded outward to the 1/FARG grid
FARG = int(os.environ.get("FARG", "0"))
def pieces_far(lo, hi):
    """quarter pieces of [lo, hi]; pieces at or beyond XFAR rounded outward to the 1/FARG grid (0 = no rounding)"""
    out = []
    for (a, b) in G.quarter_pieces(lo, hi):
        if FARG and a >= XFAR:
            g = Fr(1, FARG); a = (a // g) * g; b = -((-b) // g) * g
        out.append((a, b))
    return out
def Wmulti(lo, hi):
    if not FARG: return G.Wmulti(lo, hi)
    return min(G.W_of(*pc)[0] for pc in pieces_far(lo, hi))

def choose_axis(box, lower, c, Q):
    """The axis to bisect. `widest`: first index of maximal width. `passfirst`/`balanced`: among axes of width
    ≥ half the maximum (or any axis whose two children both pass), the one with most passing children, then the
    best worse child."""
    w = [b[1] - b[0] for b in box]
    if RULE == "widest": return w.index(max(w))
    best = None
    for k in range(Q):
        if w[k] == 0: continue
        m = (box[k][0] + box[k][1]) / 2
        a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
        la, lb = lower(tuple(a)), lower(tuple(b2))
        both = la >= c and lb >= c
        if w[k] * WFRAC < max(w) and not (RULE in ("passfirst", "passfirst_sum") and both): continue
        score = ((la >= c) + (lb >= c), (la + lb) if RULE == "passfirst_sum" else min(la, lb))
        if best is None or score > best[0]: best = (score, k)
    return best[1]

def size(Q, pairs, A, Bv, c, max_leaves=5*10**6, verbose=True):
    """Return (ok, leaves, per-gap bad lists, clear lists) for certificate level c (Fraction)."""
    n = Q + 1
    adj = [A[(r, r+1)] for r in range(Q)]
    S = [Fr(-(-(4 * c) // Bv[r]), 4) for r in range(Q)]   # per-gap cutoffs, rounded UP to a quarter (dyadic)
    covers = []
    for r in range(Q):
        level = c / adj[r]
        clear, bad = G.phase1(level, S[r])
        covers.append((level, clear, bad))
    terms = [(A[(i, j)], tuple(range(i, j))) for (i, j) in pairs]
    def lower(box):
        tot = sum(Bv[r] * box[r][0] for r in range(Q))
        for coef, idxs in terms:
            if coef == 0: continue
            lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
            tot += coef * Wmulti(lo, hi)
        return tot
    count = [0]
    def subdivide(box, depth=0):
        if half_skip(box, Q): count[0] += 1; return True
        if sum(Bv[r] * box[r][0] for r in range(Q)) >= c: count[0] += 1; return True
        if lower(box) >= c: count[0] += 1; return True
        if depth > 80 or count[0] > max_leaves: return False
        k = choose_axis(box, lower, c, Q); m = (box[k][0]+box[k][1])/2
        a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
        return subdivide(tuple(a), depth+1) and subdivide(tuple(b2), depth+1)
    t = time.time(); ok = True
    bads = [cv[2] for cv in covers]
    ntup = 1
    for bd in bads: ntup *= len(bd)
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        if sum(Bv[r] * box[r][0] for r in range(Q)) >= c: count[0] += 1; continue
        if not subdivide(box): ok = False; break
    if verbose:
        print(f"Q={Q} c={float(c):.8f}: {'OK' if ok else 'FAIL/limit'} leaves={count[0]} tuples={ntup} bad-sizes={[len(b) for b in bads]} ({time.time()-t:.0f}s)", flush=True)
    return ok, count[0], covers

if __name__ == "__main__":
    Q = int(sys.argv[1]); npz = sys.argv[2]; floor = float(sys.argv[3])
    pairs, A, Bv = load_weights(npz, Q)
    for delta in [float(x) for x in sys.argv[4:]] or [0.03, 0.02, 0.01]:
        c = Fr(int(floor * (1 - delta) * 10**8), 10**8)
        size(Q, pairs, A, Bv, c, max_leaves=3*10**6)
