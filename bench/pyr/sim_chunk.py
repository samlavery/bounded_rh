"""Distinct oracle queries per leaf (early exit, contribution order) versus walk-chunk size, at delta 2%."""
import sys, collections
from size_pyr import run, PAIRS, Q
r = run(351121, PE=5, PB=10, MAXA=4, verbose=False)
P = r["P"]; aN = r["aN"]; bN = r["bN"]; cN = r["cN"]; SC = 1 << 15; U = P.U
order = [5, 12, 9, 0, 4, 14, 3, 7, 2, 8, 11, 1, 10, 13, 6]
def terms(box): return [(sum(box[q][0] for q in range(i, j)), sum(box[q][1] for q in range(i, j))) for (i, j) in PAIRS]
def nleaf(nd): return 1 if nd[0] == 'leaf' else nleaf(nd[4]) + nleaf(nd[5])
def leaves_of(nd, out):
    if nd[0] == 'leaf': out.append(nd[1])
    else: leaves_of(nd[4], out); leaves_of(nd[5], out)
def chunks(nd, CH, out):
    if nleaf(nd) <= CH: out.append(nd)
    else: chunks(nd[4], CH, out); chunks(nd[5], CH, out)
def ee_queries(chunk_leaves, order):
    S = set(); nt = 0; cells = set()
    for b in chunk_leaves:
        if b[0][0] > b[Q - 1][1]: continue
        tq = terms(b)
        s = sum(bN[q] * b[q][0] for q in range(Q)) * U
        if s >= cN * SC * U: continue
        for t in order:
            S.add(tq[t]); nt += 1
            s += aN[t] * P.lb(*tq[t]) * SC
            if s >= cN * SC * U: break
    for q in S:
        cv = P.cover(*q)
        if cv: cells.update(c for c in cv if c)
    return len(S), nt, len(cells)
tot_leaves = r["nleaves"]
for CH in (1000, 4000, 16000, 64000):
    dq = nt = nc = 0; nch = 0
    for nd in r["nodes"].values():
        cs = []; chunks(nd, CH, cs)
        for c in cs:
            ls = []; leaves_of(c, ls); a, b, cc = ee_queries(ls, order); dq += a; nt += b; nc += cc; nch += 1
    print(f"CH={CH}: chunks {nch}; distinct queries/leaf {dq/tot_leaves:.3f}; terms evaluated/leaf {nt/tot_leaves:.2f}; distinct cells read/leaf {nc/tot_leaves:.3f}", flush=True)
