#!/usr/bin/env python3
"""Repeat rate of the minorant-leaf payload in walk order, and the walk bits under the current per-term code and under a
'same as the previous M leaf' code.  Usage: payrep.py PAY.pkl WEIGHTS.json [CH]   (pickle of (box, kind, pay) in walk order;
CH = leaves per walk chunk, at which the previous-choice state resets; default 1500)"""
import sys, json, pickle, collections
L = pickle.load(open(sys.argv[1], "rb")); J = json.load(open(sys.argv[2])); CH = int(sys.argv[3]) if len(sys.argv) > 3 else 1500
n = J["n"]; P = [(i, j) for i in range(n) for j in range(i + 1, n)]
aN = [int(J["aN"][f"{i},{j}"]) for i, j in P]; ACT = [t for t in range(len(P)) if aN[t] > 0]
JB = 5
def code(c):
    k = c[0]; return 2 + (JB if k >= 1 else 0) + (JB if k == 3 else 0) + (10 if k >= 2 else 0)
cur = A = B = 0; nM = 0; same = tot = k0 = 0; kinds = collections.Counter()
prev = None
for idx, (box, kind, pay) in enumerate(L):
    if idx % CH == 0: prev = None
    if kind != 6: continue
    nM += 1
    for t in ACT:
        c = tuple(pay[t]); kinds[c[0]] += 1; tot += 1
        cur += code(c)
        s_ = prev is not None and prev[t] == c
        same += s_
        A += 1 if s_ else 1 + code(c)
        B += 1 if s_ else (2 if c[0] == 0 else 2 + code(c))
    prev = {t: tuple(pay[t]) for t in ACT}
nl = len(L)
print(f"{nl} leaves, {nM} M; active terms {len(ACT)}; kinds {dict(kinds)}; repeat rate {same / tot:.3f}")
print(f"M payload bits per M leaf: current {cur / nM:.1f}, same-bit code {A / nM:.1f} ({cur / A:.2f}x), "
      f"same-bit + short kind-0 {B / nM:.1f} ({cur / B:.2f}x)")
print(f"walk bits per leaf (payload + ~6 structural): current {(cur + 6 * nl) / nl:.1f}, best {(min(A, B) + 6 * nl) / nl:.1f}")
