#!/usr/bin/env python3
"""Which of T1's 56 triples bind?  Replays a DATA file's walks (the verify8pz decoding, leaves skipped unchecked) and at
every node runs the full T1 with a per-triple change log, and the ends-only T1 (k in {i+1, j-1}, 36 triples) on the same
incoming state, comparing the results (intervals and emptiness).  Usage: t1stat.py DATA.json"""
import os, sys, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import tz
D = json.load(open(sys.argv[1])); PR = D['params']; Q = 7; PAIRS = tz.pairs(Q)
NADJ = [t for t, (i, j) in enumerate(PAIRS) if j - i >= 2]; ACT = [t for t in range(len(PAIRS)) if D['aN'][t] > 0]
JB, LB, QB = PR['JB'], PR['LB'], PR['QB']
TRI = [(i, j, k) for i in range(Q + 1) for j in range(i + 2, Q + 1) for k in range(i + 1, j)]
def t1x(l, u, cons, ks, log=None):
    if any(l[r] > u[r] for r in range(Q)): return None
    I = {}
    for (i, j) in PAIRS:
        lo, hi = sum(l[i:j]), sum(u[i:j])
        if (i, j) in cons: lo = max(lo, cons[(i, j)][0]); hi = min(hi, cons[(i, j)][1])
        if lo > hi: return None
        I[(i, j)] = [lo, hi]
    for n_, (i, j, k) in enumerate(TRI):
        if ks == 'ends' and k not in (i + 1, j - 1): continue
        a, b, c = I[(i, k)], I[(k, j)], I[(i, j)]; before = (a[:], b[:], c[:])
        c[0] = max(c[0], a[0] + b[0]); c[1] = min(c[1], a[1] + b[1])
        a[0] = max(a[0], c[0] - b[1]); a[1] = min(a[1], c[1] - b[0])
        b[0] = max(b[0], c[0] - a[1]); b[1] = min(b[1], c[1] - a[0])
        if log is not None and (a, b, c) != before: log[n_] += 1
        if a[0] > a[1] or b[0] > b[1] or c[0] > c[1]: return None
    l2 = [I[(r, r + 1)][0] for r in range(Q)]; u2 = [I[(r, r + 1)][1] for r in range(Q)]
    for (i, j) in PAIRS:
        if j - i < 2: continue
        c = I[(i, j)]; c[0] = max(c[0], sum(l2[i:j])); c[1] = min(c[1], sum(u2[i:j]))
        if c[0] > c[1]: return None
    return l2, u2, {(i, j): tuple(I[(i, j)]) for (i, j) in PAIRS if j - i >= 2}, I
binds = collections.Counter(); nodes = same = diff_empty = 0; anybind = 0
for wk in D['walks']:
    W_ = int(wk['hex'], 16); pos = [0]
    def get(n):
        v = (W_ >> pos[0]) & ((1 << n) - 1); pos[0] += n; return v
    stack = [([c[0] for c in wk['cell']], [c[1] for c in wk['cell']], {})]
    while stack:
        l, u, cons = stack.pop(); nodes += 1
        lg = collections.Counter(); r_ = t1x(l, u, cons, 'all', lg); re_ = t1x(l, u, cons, 'ends')
        assert (r_ is None) == (tz.t1(l, u, cons, Q) is None)
        binds.update(lg); anybind += bool(lg)
        if (r_ is None) != (re_ is None): diff_empty += 1
        elif r_ is None or r_[3] == re_[3]: same += 1
        if r_ is None: continue
        l, u, cons, I = r_
        if get(1):
            ax = get(5)
            if ax < Q:
                m = (l[ax] + u[ax]) >> 1; uA = list(u); uA[ax] = m; lB = list(l); lB[ax] = m
                stack.append((lB, u, dict(cons))); stack.append((l, uA, dict(cons)))
            else:
                pr = PAIRS[NADJ[ax - Q]]; lo, hi = cons[pr]; m = (lo + hi) >> 1
                cA = dict(cons); cA[pr] = (lo, m); cB = dict(cons); cB[pr] = (m, hi)
                stack.append((l, u, cB)); stack.append((l, u, cA))
            continue
        if u[Q - 1] < l[0]: continue
        assert get(1) == 0
        for t in ACT:
            k = get(2); get(JB) if k >= 1 else 0; get(JB) if k == 3 else 0; get(LB) if k >= 2 else 0
        while get(1): get(5); get(1); get(QB)
    assert pos[0] == wk['nbits']
ends = [n for n, (i, j, k) in enumerate(TRI) if k in (i + 1, j - 1)]
print(f"nodes {nodes}; nodes where some triple binds {anybind}; ends-only T1 gives the identical result at {same} nodes, "
      f"different emptiness at {diff_empty}")
print(f"triples that ever bind: {sum(1 for n in range(56) if binds[n])} of 56; bind events: ends {sum(binds[n] for n in ends)}, "
      f"middle {sum(binds[n] for n in range(56) if n not in ends)}")
print("middle triples by binding count:", sorted(((binds[n], TRI[n]) for n in range(56) if n not in ends), reverse=True)[:20])
