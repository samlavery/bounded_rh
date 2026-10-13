#!/usr/bin/env python3
"""Golden vectors for the closure (TZ.md section 5): from a TCLOSE DATA file, the root state of walk 0 (box sums) and
its first NS splits in depth-first order, each with the parent's closed intervals, the split (pair, m, side) and both
children from tz.close_split, checked against tz.close of the child state.  Usage: tzclose_gold.py DATA.json OUT.json [NS]"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import tz
D = json.load(open(sys.argv[1])); OUT = sys.argv[2]; NS = int(sys.argv[3]) if len(sys.argv) > 3 else 10
assert D['settings'].get('TCLOSE') == '1'
PR = D['params']; Q = 7; PAIRS = tz.pairs(Q); NADJ = [t for t, (i, j) in enumerate(PAIRS) if j - i >= 2]
ACT = [t for t in range(len(PAIRS)) if D['aN'][t] > 0]; JB, LB, QB = PR['JB'], PR['LB'], PR['QB']
key = lambda I: {f"{i},{j}": I[(i, j)] for (i, j) in PAIRS}
wk = D['walks'][0]; W_ = int(wk['hex'], 16); pos = [0]
def get(n):
    v = (W_ >> pos[0]) & ((1 << n) - 1); pos[0] += n; return v
l0 = [c[0] for c in wk['cell']]; u0 = [c[1] for c in wk['cell']]
root = tz.close(l0, u0, {}, Q)
assert all(root[3][(i, j)] == [sum(l0[i:j]), sum(u0[i:j])] for (i, j) in PAIRS), "the box is closed"
out = dict(root_cell=[l0, u0], root_intervals=key(root[3]), splits=[])
stack = [(l0, u0, {})]; gapsplits = 0
while stack and len(out['splits']) < NS:
    l, u, cons = stack.pop(); r_ = tz.close(l, u, cons, Q); l, u, cons, I = r_
    if get(1):
        ax = get(5)
        if ax < Q:
            pr = (ax, ax + 1); m = (l[ax] + u[ax]) >> 1; uA = list(u); uA[ax] = m; lB = list(l); lB[ax] = m
            A = (l, uA, dict(cons)); B = (lB, u, dict(cons))
        else:
            pr = PAIRS[NADJ[ax - Q]]; lo, hi = cons[pr]; m = (lo + hi) >> 1
            cA = dict(cons); cA[pr] = (lo, m); cB = dict(cons); cB[pr] = (m, hi); A = (l, u, cA); B = (l, u, cB)
        JA = tz.close_split(I, pr[0], pr[1], m, 0, Q); JB_ = tz.close_split(I, pr[0], pr[1], m, 1, Q)
        assert JA == tz.close(*A, Q)[3] and JB_ == tz.close(*B, Q)[3]
        out['splits'].append(dict(axis=ax, pair=list(pr), m=m, parent=key(I), childA_hi_eq_m=key(JA), childB_lo_eq_m=key(JB_),
                                  changedA=[f"{i},{j}" for (i, j) in PAIRS if JA[(i, j)] != I[(i, j)]],
                                  changedB=[f"{i},{j}" for (i, j) in PAIRS if JB_[(i, j)] != I[(i, j)]]))
        stack.append(B); stack.append(A); continue
    if u[Q - 1] < l[0]: continue
    get(1)
    for t in ACT:
        k = get(2); get(JB) if k >= 1 else 0; get(JB) if k == 3 else 0; get(LB) if k >= 2 else 0
    while get(1): get(5); get(1); get(QB)
out['notes'] = ("root_intervals: the closed root state, every pair [sum l, sum u] of the root box (the kernel's initial A_t, B_t). "
                "splits: depth-first along walk 0; parent = the closed intervals at the split node; childA = close_split side 0 "
                "(hi(pair) := m), childB = side 1 (lo(pair) := m); each child equals tz.close of the child state.")
json.dump(out, open(OUT, "w"), indent=1)
print(f"wrote {OUT}: {len(out['splits'])} splits, axes {[s['axis'] for s in out['splits']]}, "
      f"changed pairs per child {[(len(s['changedA']), len(s['changedB'])) for s in out['splits']]}")
