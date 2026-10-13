"""Distinct oracle queries (in evaluation order, early exit) of the first chunks of root (0,1,0,1,0) at delta 2%."""
import sys, random
from size_pyr import run, PAIRS, Q
r = run(351121, PE=5, PB=10, MAXA=4, verbose=False)
P = r["P"]; aN = r["aN"]; bN = r["bN"]; cN = r["cN"]; SC = 1 << 15; U = P.U
order = [5, 12, 9, 0, 4, 14, 3, 7, 2, 8, 11, 1, 10, 13, 6]
def terms(box): return [(sum(box[q][0] for q in range(i, j)), sum(box[q][1] for q in range(i, j))) for (i, j) in PAIRS]
def leaves_of(nd, out):
    if nd[0] == 'leaf': out.append(nd[1])
    else: leaves_of(nd[4], out); leaves_of(nd[5], out)
ls = []; leaves_of(r["nodes"][(0, 1, 0, 1, 0)], ls)
seen = []; S = set(); reads = 0
for b in ls:
    if b[0][0] > b[Q - 1][1]: continue
    tq = terms(b); s = sum(bN[q] * b[q][0] for q in range(Q)) * U
    if s >= cN * SC * U: continue
    for t in order:
        if tq[t] not in S: S.add(tq[t]); seen.append(tq[t])
        s += aN[t] * P.lb(*tq[t]) * SC
        if s >= cN * SC * U: break
cells = set(); nr = 0
for q in seen:
    cv = P.cover(*q); nr += len(cv); cells.update(cv)
print(f"root leaves {len(ls)}, distinct queries {len(seen)} ({len(seen)/len(ls):.2f}/leaf), reads/query {nr/len(seen):.2f}, distinct cells {len(cells)}")
open("lbq_root.txt", "w").write("\n".join(f"{a} {b}" for a, b in seen[:3000]) + "\n")
