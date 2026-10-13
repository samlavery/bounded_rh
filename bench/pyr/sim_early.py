"""Early-exit analysis on a pyramid certificate: with the running sum tested after each term (fixed term order),
how many distinct oracle queries does each walk chunk evaluate, versus all 15 terms?"""
import sys, collections
from size_pyr import run, PAIRS, Q
r = run(345747, PE=5, PB=10, MAXA=4, verbose=False)
P = r["P"]; aN = r["aN"]; bN = r["bN"]; cN = r["cN"]; SC = 1 << 15; U = P.U
leaves = []
def collect(nd):
    if nd[0] == 'leaf': leaves.append(nd[1])
    else: collect(nd[4]); collect(nd[5])
for nd in r["nodes"].values(): collect(nd)
def terms(box): return [(sum(box[q][0] for q in range(i, j)), sum(box[q][1] for q in range(i, j))) for (i, j) in PAIRS]
# average contribution per term
contrib = [0.0] * 15
for b in leaves:
    for t, (lo, hi) in enumerate(terms(b)): contrib[t] += aN[t] * P.lb(lo, hi)
orders = {"index": list(range(15)), "weight": sorted(range(15), key=lambda t: -aN[t]), "contrib": sorted(range(15), key=lambda t: -contrib[t])}
print("avg contribution order:", orders["contrib"])
CH = 1000
for name, order in orders.items():
    full = early = 0; nt = 0
    for c0 in range(0, len(leaves), CH):
        chunk = leaves[c0:c0 + CH]
        sf = set(); se = set()
        for b in chunk:
            if b[0][0] > b[Q - 1][1]: continue
            tq = terms(b); sf.update(tq)
            s = sum(bN[q] * b[q][0] for q in range(Q)) * U
            if s >= cN * SC * U: continue
            for t in order:
                se.add(tq[t]); nt += 1
                s += aN[t] * P.lb(*tq[t]) * SC
                if s >= cN * SC * U: break
        full += len(sf); early += len(se)
    print(f"order {name:8s}: distinct queries per {CH}-leaf chunk summed: all-terms {full} ({full/len(leaves):.2f}/leaf), early-exit {early} ({early/len(leaves):.2f}/leaf); terms evaluated {nt/len(leaves):.2f}/leaf")
