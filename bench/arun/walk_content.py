#!/usr/bin/env python3
"""walk_content.py DATA.json: walk-content breakdown and the derivable-point estimate (am-cert, 2026-10-10; analysis only).

Replays the certificate with verify8pz.py (unmodified source exec'd with a recorder around `mcheck`; split-axis width
AXB = bit_length(Q + NC − 1)) and tallies the fixed-width walk bits by field:
  split headers [1][axis AXB][mode 1]; leaf marker [0]; kind bit; per active term kind (2), j1 (JB if κ ≥ 1),
  j2 (JB if κ = 3), λ (LB if κ ≥ 2); multipliers [1][c 5][side 1][Yq QB] and the closing [0].
Derivable points (lever 1 makes every used point carry one validity interval, the hull of its leaf ranges): for each
tangent point a leaf reads, the candidates are the table points q with L ≤ q ≤ U whose interval covers [L, U]; the
leaf then needs only the rank of its point among them (⌈log2 #cands⌉ bits), or a 1-bit "same point as the previous
leaf for this term" flag plus the rank on a miss.  Also reports the empirical entropies (static per-term) of kinds,
λ and ranks, as the Huffman-able floor of those fields."""
import sys, os, json, math, collections, bisect, io, contextlib
DATA = sys.argv[1]
VER = os.path.expanduser("~/work/riemann-submission/bench/eight/am8/verify8pz.py")
src = open(VER, encoding="utf-8").read()
assert src.count("ax = get(5)") == 1 and src.count("def weights(k, m):") == 1
src = src.replace("ax = get(5)", "ax = get((Q + len(NADJ) - 1).bit_length())")
src = src.replace("stats = dict(", """_LEAVES = []
_mcheck0 = mcheck
def mcheck(l, u, cons, I, terms, Ys):
    _LEAVES.append((list(l), list(u), dict(I), list(terms), dict(Ys)))
    return _mcheck0(l, u, cons, I, terms, Ys)
stats = dict(""", 1)
sys.argv = [VER, DATA]; sys.path.insert(0, os.path.dirname(VER))
g = {"__name__": "__main__", "__file__": VER}
with contextlib.redirect_stdout(io.StringIO()):
    exec(compile(src, VER, "exec"), g)
LV = g["_LEAVES"]; st = g["stats"]; Q = g["Q"]; NADJ = g["NADJ"]; PAIRS = g["PAIRS"]; JB = g["JB"]; LB = g["LB"]; QB = g["QB"]
AXB = (Q + len(NADJ) - 1).bit_length(); gpt = g["gpt"]; PT = g["PT"]; tcheck = g["tcheck"]
nleaf = st["M"] + st["refl"]; nsplit = st["split"]
bits = collections.Counter()
bits["split headers"] = nsplit * (1 + AXB + 1)
bits["leaf marker + kind bit"] = nleaf + st["M"]
uses = collections.defaultdict(list)          # point -> ranges (for the lever-1 intervals)
recs = []                                     # (leaf idx, term, κ, slot, point, L, U)
kinds = collections.defaultdict(collections.Counter); lams = collections.defaultdict(collections.Counter)
for n, (l, u, I, terms, Ys) in enumerate(LV):
    for t, (k, j1, j2, lam) in terms:
        bits["kind codes"] += 2; kinds[t][k] += 1
        if k >= 1: bits["point indices j1/j2"] += JB
        if k == 3: bits["point indices j1/j2"] += JB
        if k >= 2: bits["lambda"] += LB; lams[t][lam] += 1
        i, j = PAIRS[t]; L, U = I[(i, j)]
        for slot, jj in ((1, j1), (2, j2)):
            if (slot == 1 and k >= 1) or (slot == 2 and k == 3):
                p = gpt(L, U, jj); uses[p].append((L, U)); recs.append((n, t, k, slot, p, L, U))
    bits["multipliers"] += len(Ys) * (1 + 5 + 1 + QB) + 1
tot = sum(bits.values())
print(f"{DATA}: {nleaf} leaves ({st['M']} M), {nsplit} splits; fixed-width walk {tot} bits = {tot / nleaf:.1f} bits/leaf")
for k, v in bits.most_common():
    print(f"  {k:26s} {v / nleaf:7.1f} bits/leaf  {100 * v / tot:5.1f} %")
# lever-1 intervals (hulls of each point's ranges; lever1_check.py showed every hull passes tcheck)
iv = {p: (min(a for a, _ in rs), max(b for _, b in rs)) for p, rs in uses.items()}
pts = sorted(iv)
ncand = []; inrange = []
for (n, t, k, slot, p, L, U) in recs:
    a0 = bisect.bisect_left(pts, L); a1 = bisect.bisect_right(pts, U)
    c = [q for q in pts[a0:a1] if iv[q][0] <= L and U <= iv[q][1]]
    assert p in c
    ncand.append(len(c)); inrange.append(a1 - a0)
ncand.sort(); inrange.sort()
q = lambda v, f: v[min(len(v) - 1, int(f * len(v)))]
rankbits = sum(math.ceil(math.log2(c)) if c > 1 else 0 for c in ncand)
print(f"tangent points read: {len(recs)} ({len(recs) / st['M']:.1f} per M leaf)")
print(f"  candidates covering [L, U]: median {q(ncand, .5)}, p90 {q(ncand, .9)}, max {ncand[-1]}; "
      f"table points inside [L, U] (kernel scan length): median {q(inrange, .5)}, p90 {q(inrange, .9)}, max {inrange[-1]}")
print(f"  rank code (⌈log2 #cands⌉): {rankbits / nleaf:.1f} bits/leaf vs {bits['point indices j1/j2'] / nleaf:.1f} now")
# same-as-previous (per term and slot, in walk order)
prev = {}; same = 0; flagbits = 0
for (n, t, k, slot, p, L, U), c in zip(recs, [None] * len(recs)):
    pass
prev = {}; same = 0; fb = 0
cand_of = {}
for idx, (n, t, k, slot, p, L, U) in enumerate(recs):
    key = (t, slot)
    a0 = bisect.bisect_left(pts, L); a1 = bisect.bisect_right(pts, U)
    c = [qq for qq in pts[a0:a1] if iv[qq][0] <= L and U <= iv[qq][1]]
    if prev.get(key) == p: same += 1; fb += 1
    else: fb += 1 + (math.ceil(math.log2(len(c))) if len(c) > 1 else 0)
    prev[key] = p
print(f"  same-point-as-previous-leaf rate {same / len(recs):.2f}; flag + rank: {fb / nleaf:.1f} bits/leaf")
# static entropies of the other per-term fields
H = lambda cnt: -sum(v / sum(cnt.values()) * math.log2(v / sum(cnt.values())) for v in cnt.values())
hk = sum(H(c) * sum(c.values()) for c in kinds.values()) / nleaf
hl = sum(H(c) * sum(c.values()) for c in lams.values()) / nleaf
print(f"static per-term entropy: kinds {hk:.1f} bits/leaf (fixed {bits['kind codes'] / nleaf:.1f}); "
      f"λ {hl:.1f} (fixed {bits['lambda'] / nleaf:.1f})")
best = (bits["split headers"] + bits["leaf marker + kind bit"] + bits["multipliers"]) / nleaf + hk + hl + min(rankbits, fb) / nleaf
print(f"combination (entropy-coded kinds and λ, derived points, other fields fixed): ≈ {best:.0f} bits/leaf")
fixed_kinds = (bits["split headers"] + bits["leaf marker + kind bit"] + bits["multipliers"] + bits["kind codes"]
               + bits["lambda"]) / nleaf + min(rankbits, fb) / nleaf
print(f"combination (all fields fixed-width, derived points only): ≈ {fixed_kinds:.0f} bits/leaf")
# ---- entropy floors of the whole per-term payload (κ, j1, j2, λ) as one symbol per term
sym = collections.defaultdict(collections.Counter); cond = collections.defaultdict(collections.Counter)
prevs = {}
for n, (l, u, I, terms, Ys) in enumerate(LV):
    for t, s in terms:
        sym[t][s] += 1
        cond[(t, prevs.get(t))][s] += 1; prevs[t] = s
hs = sum(H(c) * sum(c.values()) for c in sym.values()) / nleaf
hc = sum(H(c) * sum(c.values()) for c in cond.values()) / nleaf
nsym = sum(len(c) for c in sym.values()); ncond = sum(len(c) for c in cond.values())
other = (bits["split headers"] + bits["leaf marker + kind bit"] + bits["multipliers"]) / nleaf
print(f"per-term joint symbol entropy: static {hs:.1f} bits/leaf ({nsym} table symbols) -> walk ≈ {hs + other:.0f} bits/leaf; "
      f"conditioned on the previous leaf's symbol for the term {hc:.1f} ({ncond} contexts, model cost ignored) -> ≈ {hc + other:.0f}")
