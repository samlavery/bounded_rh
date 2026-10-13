#!/usr/bin/env python3
"""Bits per M leaf of the minorant payload (pair-cell dumps from run8pz SAVE) under:
  cur   : the current fields (kind 2, positions JB each, lam 10);
  H     : the static per-term entropy of the whole term choice (a lower bound for any static per-term code);
  pfx   : a decodable code: per term a 2-level kind code ('0' = the term's most common kind, '10' second, '110'/'111'),
          positions in a per-term-kind-independent skewed code (see below), lam as (lam' - 512) in 9 bits where the
          heavier minorant comes first;
plus the multiplier list (19 bits per entry + 1) and split/leaf bits as the walk.  Usage: paycode.py DUMP.pkl [JSH]"""
import sys, pickle, collections, math
L = pickle.load(open(sys.argv[1], "rb")); JSH = int(sys.argv[2]) if len(sys.argv) > 2 else 5
JB = JSH + 2; NPOS = (1 << JSH) + 1
def H(c):
    n = sum(c.values()); return -sum(v / n * math.log2(v / n) for v in c.values())
M = [(box, cons, pay) for box, cons, kind, pay in L if kind == 6]
nM = len(M); NP = len(M[0][2][0])
per = collections.defaultdict(collections.Counter); kinds = collections.defaultdict(collections.Counter)
pos = collections.Counter(); posg = collections.Counter(); lam = collections.Counter(); ny = 0
for box, cons, (mc, Ys) in M:
    ny += len(Ys)
    for t, c in enumerate(mc):
        per[t][tuple(c)] += 1; kinds[t][c[0]] += 1
        if c[0] >= 1: pos[c[1]] += 1
        if c[0] == 3: pos[c[2]] += 1
        if c[0] >= 2: lam[c[3]] += 1
cur = sum(2 + (JB if c[0] >= 1 else 0) + (JB if c[0] == 3 else 0) + (10 if c[0] >= 2 else 0) for _, _, (mc, _) in M for c in mc) / nM
Hs = sum(H(per[t]) * sum(per[t].values()) for t in per) / nM
# kind prefix code per term
rank = {t: [k for k, _ in kinds[t].most_common()] for t in kinds}
kb = {t: {k: (1 if i == 0 else 2 if i == 1 else 3) for i, k in enumerate(rank[t])} for t in rank}
# position code: Huffman over the observed position values (one shared table)
import heapq
def huff(cnt):
    h = [(v, i, (k,)) for i, (k, v) in enumerate(cnt.items())]; heapq.heapify(h); L_ = {k: 0 for k in cnt}; i = len(h)
    if len(h) == 1: return {k: 1 for k in cnt}
    while len(h) > 1:
        a = heapq.heappop(h); b = heapq.heappop(h)
        for k in a[2] + b[2]: L_[k] += 1
        heapq.heappush(h, (a[0] + b[0], i, a[2] + b[2])); i += 1
    return L_
PL = huff(pos)
lam_bits = 9  # heavier minorant first: lam' in [512, 1024]
pfx = 0
for box, cons, (mc, Ys) in M:
    for t, c in enumerate(mc):
        k = c[0]; pfx += kb[t][k]
        if k >= 1: pfx += PL[c[1]]
        if k == 3: pfx += PL[c[2]]
        if k >= 2: pfx += lam_bits
pfx /= nM
print(f"{nM} M leaves, {NP} terms; payload bits per M leaf: current {cur:.1f}; static per-term entropy {Hs:.1f}; "
      f"decodable (term kind prefix + Huffman positions + 9-bit lam) {pfx:.1f}")
print(f"  position entropy {H(pos):.2f} bits (field {JB}); Huffman mean {sum(PL[k]*v for k, v in pos.items())/sum(pos.values()):.2f}; "
      f"kind entropy per term (mean) {sum(H(kinds[t]) for t in kinds)/len(kinds):.2f}; multipliers per M leaf {ny/nM:.2f}")
# per-term Huffman positions and per-term-kind Huffman; lam entropy
pos_t = collections.defaultdict(collections.Counter); lam_hi = collections.Counter()
for box, cons, (mc, Ys) in M:
    for t, c in enumerate(mc):
        if c[0] >= 1: pos_t[t][c[1]] += 1
        if c[0] == 3: pos_t[t][c[2]] += 1
        if c[0] >= 2: lam_hi[max(c[3], 1024 - c[3])] += 1
PLt = {t: huff(pos_t[t]) for t in pos_t}
pfx2 = 0
for box, cons, (mc, Ys) in M:
    for t, c in enumerate(mc):
        k = c[0]; pfx2 += kb[t][k]
        if k >= 1: pfx2 += PLt[t][c[1]]
        if k == 3: pfx2 += PLt[t][c[2]]
        if k >= 2: pfx2 += 9
print(f"  per-term Huffman positions: {pfx2 / nM:.1f} bits per M leaf; heavier-weight lam entropy {H(lam_hi):.2f} bits (field 9); "
      f"table size ~{sum(len(v) for v in pos_t.values())} entries")
# per-term joint Huffman over (kind, j1, j2), lam 9 bits
jt = collections.defaultdict(collections.Counter)
for box, cons, (mc, Ys) in M:
    for t, c in enumerate(mc): jt[t][(c[0], c[1] if c[0] >= 1 else 0, c[2] if c[0] == 3 else 0)] += 1
JL = {t: huff(jt[t]) for t in jt}
pfx3 = sum(JL[t][(c[0], c[1] if c[0] >= 1 else 0, c[2] if c[0] == 3 else 0)] + (9 if c[0] >= 2 else 0)
           for box, cons, (mc, Ys) in M for t, c in enumerate(mc)) / nM
print(f"  per-term joint Huffman (kind, positions) + 9-bit lam: {pfx3:.1f} bits per M leaf; table {sum(len(v) for v in jt.values())} entries")
# whole walk under the joint code: split 6, empty 0, refl/Z 2, M 2 + joint payload + (19 per multiplier + 1), Farkas 60
cnt = collections.Counter(k for _, _, k, _ in L)
nsplit = len(L) - 1   # a full binary tree per root: leaves - roots; roots are few
walk = 6 * nsplit + 2 * (cnt[0] + cnt[1]) + 60 * cnt[8] + sum(2 + 1 + 19 * len(Ys) for _, _, (mc, Ys) in M) + pfx3 * nM
cur_walk = 6 * nsplit + 2 * (cnt[0] + cnt[1]) + 60 * cnt[8] + sum(2 + 1 + 19 * len(Ys) for _, _, (mc, Ys) in M) + cur * nM
print(f"  walk bits: current code {cur_walk:.0f} ({cur_walk/len(L):.1f}/leaf), joint code {walk:.0f} ({walk/len(L):.1f}/leaf); "
      f"as is: joint {walk/4/1e6:.3f} MB hex / {walk/6/1e6:.3f} MB base64; current {cur_walk/4/1e6:.3f} hex / {cur_walk/6/1e6:.3f} b64")
