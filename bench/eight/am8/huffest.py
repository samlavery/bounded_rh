#!/usr/bin/env python3
"""Walk-size estimate from size8pz dumps (run8pz SAVE), any Q: the fixed-width layout (emit8pz, axis field widened to
fit Q + #sums) and the canonical-Huffman layout of HUFF.md (in-sample tables: per active term, axis, constraint), with
LB = 8 (LS 256), JB = 7, YB = 12.  Usage: huffest.py W.json DUMP.pkl [DUMP.pkl ...] [--bsplit] (--bsplit: +1 mode bit per split)"""
import sys, json, pickle, collections, heapq
J = json.load(open(sys.argv[1])); n_ = J["n"]; Q = n_ - 1
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
NADJ = [t for t, (i, j) in enumerate(PAIRS) if j - i >= 2]; RANK = {t: k for k, t in enumerate(NADJ)}
aN = [int(J["aN"][f"{i},{j}"]) for (i, j) in PAIRS]; ACT = [t for t in range(len(PAIRS)) if aN[t] > 0]
AXB = (Q + len(NADJ) - 1).bit_length(); CB = (len(NADJ) - 1).bit_length(); JB = 7; LB = 8; YB = 12
def huff_lengths(cnt):
    if len(cnt) == 1: return {next(iter(cnt)): 0}
    h = [(v, i, (k,)) for i, (k, v) in enumerate(sorted(cnt.items()))]; heapq.heapify(h); L = {k: 0 for k in cnt}; i = len(h)
    while len(h) > 1:
        a = heapq.heappop(h); b = heapq.heappop(h)
        for k in a[2] + b[2]: L[k] += 1
        heapq.heappush(h, (a[0] + b[0], i, a[2] + b[2])); i += 1
    return L
axc = collections.Counter(); cc = collections.Counter(); tc = collections.defaultdict(collections.Counter)
fixed = 0; extra = 0; nl = nsp = nrefl = 0
def walk(nd):
    global fixed, extra, nl, nsp, nrefl
    if nd[0] == 'split':
        nsp += 1; ax = nd[3]; a = ax if ax < Q else Q + RANK[ax - Q]; axc[a] += 1; fixed += 1 + AXB + BS; extra += 1 + BS
        walk(nd[4]); walk(nd[5]); return
    kind, pay = nd[3], nd[4]; nl += 1
    if kind == 7: return
    fixed += 1; extra += 1
    if kind == 0: nrefl += 1; return
    assert kind == 6, kind
    fixed += 1; extra += 1
    mc, Ys = pay
    for t in ACT:
        k, j1, j2, lam = mc[t]
        fixed += 2 + (JB if k >= 1 else 0) + (JB if k == 3 else 0) + (LB if k >= 2 else 0)
        tc[t][k * 16384 + (j1 if k >= 1 else 0) * 128 + (j2 if k == 3 else 0)] += 1
        extra += LB if k == 2 else (LB - 1 if k == 3 else 0)
    for (t, side) in Ys:
        cc[RANK[t]] += 1; fixed += 1 + CB + 1 + YB; extra += 1 + 1 + YB
    fixed += 1; extra += 1
BS = '--bsplit' in sys.argv
for f in [a for a in sys.argv[2:] if not a.startswith('--')]:
    for tr in pickle.load(open(f, "rb"))["trees"]: walk(tr)
huff = extra
for cnt in [axc, cc] + list(tc.values()):
    L = huff_lengths(cnt); huff += sum(L[s] * v for s, v in cnt.items())
tsyms = len(axc) + len(cc) + sum(len(c) for c in tc.values())
print(f"Q {Q}: {nl} leaves ({nrefl} reflected), {nsp} splits; fixed-width {fixed} bits ({fixed / nl:.1f}/leaf, {fixed / 4 / 1000:.1f} KB hex); "
      f"Huffman {huff} bits ({huff / nl:.1f}/leaf, {huff / 4 / 1000:.1f} KB hex, {100 * (1 - huff / fixed):.1f} % less); table symbols {tsyms}")
