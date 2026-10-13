"""Round 11: bits per pair term in bridge-port's n = 9 certificate walks (read-only).  Re-walks each root's bit string with the
decoder logic of cert/n9/make9pcC.py (build2 / leafend; tz.close from the data's directory) and tallies, per active pair (i, j), the
bits of its leaf field, plus split headers and multiplier blocks.  Used to price a sub-frame leaf from the pairs it keeps.
usage: python3 decode_bits.py DATA.json OUT.json"""
import os, sys, json, collections
sys.setrecursionlimit(100000)
DJ, OUTJ = sys.argv[1], sys.argv[2]
D = json.load(open(DJ))
sys.path.insert(0, os.path.dirname(os.path.abspath(DJ))); sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/eight/am8")
import tz
Q = len(D["bN"]); PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]; NC = len(SUMS)
AXB = max(1, (Q + NC - 1).bit_length()); BSPLIT = bool(D["params"].get("BSPLIT", 0)); BND = D["params"].get("BND", []); BMG = D["params"].get("BMARG", 64)
NOREFL = D["settings"].get("NOREFL") == "1"
ACT = [p for p, a in zip(PAIRS, D["aN"]) if a > 0]
def bcut(lo, hi):
    best = None
    for z in BND:
        if lo + BMG <= z <= hi - BMG and (best is None or abs(2 * z - lo - hi) < abs(2 * best - lo - hi)): best = z
    return best
T = {'split_bits': 0, 'splits': 0, 'refl_leaves': 0, 'm_leaves': 0, 'leaf_head_bits': 0, 'mult_bits': 0, 'mult_blocks': 0}
PB = collections.Counter(); KH = collections.defaultdict(collections.Counter)
def leaf(W_, pos):
    p_ = pos + 2; T['leaf_head_bits'] += 2
    for pr in ACT:
        k = (W_ >> p_) & 3; nb = 2 + (7 if k >= 1 else 0) + (7 if k == 3 else 0) + (8 if k >= 2 else 0)
        PB[pr] += nb; KH[pr][k] += 1; p_ += nb
    while (W_ >> p_) & 1: p_ += 1 + 5 + 1 + 12; T['mult_bits'] += 19; T['mult_blocks'] += 1
    T['mult_bits'] += 1
    return p_ + 1
def walk(W_, l, u, cons, pos):
    r_ = tz.close(l, u, dict(cons), Q)
    l2, u2, cons2, I = r_; cons2 = {t: tuple(v) for t, v in cons2.items()}
    if (W_ >> pos) & 1:
        ax = (W_ >> (pos + 1)) & ((1 << AXB) - 1)
        md = (W_ >> (pos + 1 + AXB)) & 1 if BSPLIT else 0; p2 = pos + 2 + AXB if BSPLIT else pos + 1 + AXB
        T['split_bits'] += p2 - pos; T['splits'] += 1
        if ax < Q:
            m = bcut(l2[ax], u2[ax]) if md else (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
            e = walk(W_, l2, uA, dict(cons2), p2); return walk(W_, lB, u2, dict(cons2), e)
        t = SUMS[ax - Q]; lo, hi = cons2[t]; m = bcut(lo, hi) if md else (lo + hi) >> 1
        cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
        e = walk(W_, l2, u2, cA, p2); return walk(W_, l2, u2, cB, e)
    if u2[Q - 1] < l2[0] and not NOREFL: T['refl_leaves'] += 1; return pos + 1
    T['m_leaves'] += 1; return leaf(W_, pos)
tot = 0
for wk in D["walks"]:
    box = wk["cell"]; W_ = int(wk["hex"], 16)
    e = walk(W_, [c[0] for c in box], [c[1] for c in box], {}, 0); assert e == wk["nbits"], (e, wk["nbits"]); tot += e
nm = T['m_leaves']
per_pair = {'%d,%d' % p: PB[p] / nm for p in ACT}
print('total bits', tot, T, flush=True)
print('bits per M leaf: head %.2f, pairs %.2f, multipliers %.2f; per split %.2f' % (T['leaf_head_bits'] / nm, sum(PB.values()) / nm, T['mult_bits'] / nm, T['split_bits'] / max(1, T['splits'])))
for d in range(1, Q + 1):
    ps = [p for p in ACT if p[1] - p[0] == d]
    print('  pair distance %d: %d pairs, mean bits/pair/leaf %.2f' % (d, len(ps), sum(PB[p] for p in ps) / nm / max(1, len(ps))))
json.dump({'T': T, 'total_bits': tot, 'per_pair_bits_per_leaf': per_pair, 'kappa_hist': {'%d,%d' % p: dict(KH[p]) for p in ACT}}, open(OUTJ, 'w'))
