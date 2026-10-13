#!/usr/bin/env python3
"""(bridge-port) A synthetic nine-point (Q = 8) certificate in mvt-engine's DATA layout, to test the Q-generic Lean
generators (genpcellQ.py, makepcQ.py) end to end: symmetric weights, a tiny cN (the linear part alone carries every
leaf), empty tables, one root (a single bad segment per gap), and a random closure split tree (tz.close) with
all-constant minorant leaves (and reflected ones where u_7 < l_0).  Usage: [Q=7|8] syn9data.py OUT.json [NODES] [SEED]"""
import sys, os, json, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "eight", "am8"))
import tz
OUT = sys.argv[1]; TARGET = int(sys.argv[2]) if len(sys.argv) > 2 else 600; random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
Q = int(os.environ.get("Q", "8")); PAIRS = tz.pairs(Q); SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]; NC = len(SUMS)
BW = {8: [30000, 55000, 70000, 80000, 80000, 70000, 55000, 30000], 7: [30000, 55000, 70000, 80000, 70000, 55000, 30000]}[Q]
AW = {(i, j): (16000000 if j - i == 1 else (0 if (i, j) in ((0, 2), (Q - 2, Q)) else 20000000 + 1000000 * (j - i))) for (i, j) in PAIRS}
ACT = [t for t in PAIRS if AW[t] > 0]
AXB = (Q + NC - 1).bit_length()
S = [32768] * Q
bits = []
def put(v, n):
    for k in range(n): bits.append((v >> k) & 1)
stats = dict(split=0, leaf=0, refl=0)
budget = [TARGET]
def node(l, u, cons, depth):
    r_ = tz.close(l, u, dict(cons), Q); assert r_ is not None
    l2, u2, cons2, I = r_
    budget[0] -= 1
    cands = [ax for ax in range(Q + NC)
             if (I[(ax, ax + 1)][1] - I[(ax, ax + 1)][0] if ax < Q else I[SUMS[ax - Q]][1] - I[SUMS[ax - Q]][0]) >= 2]
    if budget[0] > 0 and depth < 14 and cands and random.random() < 0.85:
        ax = random.choice(cands); put(1, 1); put(ax, AXB); stats['split'] += 1
        if ax < Q:
            m = (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
            node(l2, uA, cons2, depth + 1); node(lB, u2, cons2, depth + 1)
        else:
            t = SUMS[ax - Q]; lo, hi = cons2[t]; m = (lo + hi) >> 1
            cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
            node(l2, u2, cA, depth + 1); node(l2, u2, cB, depth + 1)
        return
    put(0, 1)
    if u2[Q - 1] < l2[0]: stats['refl'] += 1; return
    put(0, 1)
    for _ in ACT: put(0, 2)
    put(0, 1); stats['leaf'] += 1
box = [(16384, S[r]) for r in range(Q)]
node([b[0] for b in box], [b[1] for b in box], {}, 0)
D = dict(name="synthetic nine-point test", window="synthetic", delta=0, cN=1000, SA=100000000,
         pairs=[f"{i},{j}" for (i, j) in PAIRS], aN=[AW[t] for t in PAIRS], bN=BW,
         settings=dict(TCLOSE="1", NR="0"),
         params=dict(SC=32768, LB=8, JSH=5, JB=7, GSH=5, PLO=33, SIGSH=14, QB=12, ZEXT=8),
         S=S, covers=[[[16384, S[r], False]] for r in range(Q)],
         walks=[dict(root=[0] * Q, cell=[list(b) for b in box], nbits=len(bits), hex=hex(sum(b << k for k, b in enumerate(bits))))],
         tables=dict(TOP="0x0", BK={}, TOPD="0x0", BKD={}, REG={}, points=[], w_finest=0, d_finest=0),
         counts=dict(leaves=stats['leaf'] + stats['refl'], splits=stats['split'], walk_bits=len(bits)))
json.dump(D, open(OUT, "w"))
print(OUT, stats, "bits", len(bits), "axis bits", AXB)
