#!/usr/bin/env python3
"""Golden vectors for TZ.md: replay the first nodes of a dump's root walk with tz.t1 and the split rule, printing each
node's cell before and after T1 (checked against the dump), and the Z checks logged by emit8pz (ZLOGN).
Usage: AMWIN=W.json tzgold.py W.json DELTA DUMP.pkl ZLOG.json OUT.json [ROOT_INDEX] [NNODES]"""
import os, sys, json, pickle, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import tz
import size8amz as S8
WJ, DELTA, DUMP, ZL, OUT = sys.argv[1:6]; RI = int(sys.argv[6]) if len(sys.argv) > 6 else 0; NN = int(sys.argv[7]) if len(sys.argv) > 7 else 10
J = json.load(open(WJ)); Q = 7; PAIRS = tz.pairs(Q)
aN = [int(J["aN"][f"{i},{j}"]) for (i, j) in PAIRS]; bN = [int(x) for x in J["bN"]]
cN = int(float(J["eps_strong"]) * 1e8 * (1 - float(DELTA))); SC = 32768
adj = [aN[PAIRS.index((r, r + 1))] for r in range(Q)]
Sx = [-(-(4 * cN * SC) // (bN[r] * 4 * S8.QUARTER)) * S8.QUARTER for r in range(Q)]
bads = [S8.phase1(cN, adj[r], Sx[r])[1] for r in range(Q)]
roots = list(itertools.product(*[range(len(bd)) for bd in bads]))
trees = pickle.load(open(DUMP, "rb"))["trees"]
tup = roots[RI]; box = [bads[r][tup[r]] for r in range(Q)]
out = []
def go(l, u, cons, t, path):
    if len(out) >= NN: return
    r_ = tz.t1(l, u, cons, Q)
    rec = dict(path=path, before=dict(l=l, u=u, cons={f"{i},{j}": list(v) for (i, j), v in sorted(cons.items())}))
    if r_ is None:
        rec['after'] = 'empty'; assert t[0] == 'leaf' and t[3] == 7; out.append(rec); return
    l2, u2, cons2, I = r_
    rec['after'] = dict(l=l2, u=u2, intervals={f"{i},{j}": I[(i, j)] for (i, j) in PAIRS})
    assert [list(x) for x in t[1]] == [[a, b] for a, b in zip(l2, u2)], "T1 differs from the dump"
    assert {PAIRS[k]: tuple(v) for k, v in t[2].items()} == cons2, "persisted bounds differ from the dump"
    if t[0] == 'leaf':
        rec['node'] = {0: 'leaf: reflected', 6: 'leaf: minorant', 7: 'empty'}.get(t[3], str(t[3])); out.append(rec); return
    ax = t[3]
    if ax < Q:
        m = (l2[ax] + u2[ax]) >> 1; rec['node'] = f"split gap {ax} at {m}"; out.append(rec)
        uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
        go(l2, uA, dict(cons2), t[4], path + 'A'); go(lB, u2, dict(cons2), t[5], path + 'B')
    else:
        pr = PAIRS[ax - Q]; lo, hi = I[pr]; m = (lo + hi) >> 1
        rec['node'] = f"split sum {pr[0]},{pr[1]} at {m}"; out.append(rec)
        cA = dict(cons2); cA[pr] = (cons2[pr][0], m); cB = dict(cons2); cB[pr] = (m, cons2[pr][1])
        go(l2, u2, cA, t[4], path + 'A'); go(l2, u2, cB, t[5], path + 'B')
go([x[0] for x in box], [x[1] for x in box], {}, trees[RI], '')
# step-5 vectors: the first NRC nodes (roots in order, depth first) where the re-clip changes an interval or empties the cell
NRC = int(os.environ.get("NRC", "3")); rc = []
def scan(l, u, cons, t, path):
    if len(rc) >= NRC: return
    r_ = tz.t1(l, u, cons, Q); r0 = tz.t1(l, u, cons, Q, reclip=False)
    if r_ is None and r0 is None: return
    if r_ is None or r0[3] != r_[3]:
        rec = dict(path=path, before=dict(l=l, u=u, cons={f"{i},{j}": list(v) for (i, j), v in sorted(cons.items())}),
                   after_step4=dict(l=r0[0], u=r0[1], intervals={f"{i},{j}": r0[3][(i, j)] for (i, j) in PAIRS}))
        if r_ is None: rec['after'] = 'empty'
        else:
            rec['after'] = dict(l=r_[0], u=r_[1], intervals={f"{i},{j}": r_[3][(i, j)] for (i, j) in PAIRS})
            rec['reclipped'] = [f"{i},{j}" for (i, j) in PAIRS if r0[3][(i, j)] != r_[3][(i, j)]]
        rc.append(rec)
    if r_ is None or t[0] == 'leaf': return
    l2, u2, cons2, I = r_
    ax = t[3]
    if ax < Q:
        m = (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
        scan(l2, uA, dict(cons2), t[4], path + 'A'); scan(lB, u2, dict(cons2), t[5], path + 'B')
    else:
        pr = PAIRS[ax - Q]; m = (I[pr][0] + I[pr][1]) >> 1
        cA = dict(cons2); cA[pr] = (cons2[pr][0], m); cB = dict(cons2); cB[pr] = (m, cons2[pr][1])
        scan(l2, u2, cA, t[4], path + 'A'); scan(l2, u2, cB, t[5], path + 'B')
for ri in range(len(trees)):
    tp = roots[ri]; bx = [bads[r][tp[r]] for r in range(Q)]; n0 = len(rc)
    scan([x[0] for x in bx], [x[1] for x in bx], {}, trees[ri], '')
    for rec in rc[n0:]: rec['root_index'] = ri
    if len(rc) >= NRC: break
Z = json.load(open(ZL))[:5] if os.path.exists(ZL) else []
json.dump(dict(root_index=RI, root=list(tup), t1_nodes=out, reclip_nodes=rc, z_checks=Z), open(OUT, "w"), indent=1)
print(f"wrote {OUT}: {len(out)} T1 nodes, {len(rc)} re-clip nodes, {len(Z)} Z checks")
