"""Round 12: context entropy budget of a PC9Q-family walk (read-only on bridge-port's / am-cert's data).
Re-walks every root with the decoder semantics of cert/n9/make9qIR.py (tz.close at every node, split modes with bcut, fixed-width
leaf fields), so every M-leaf term carries its closed range [L, U].  Records per term (kappa, jj1, jj2, lambda, L, U), the
multiplier blocks and the split fields, checks the bit count of every walk, and measures:
  order-0 and position-conditioned entropies; the point code inside the arithmetic candidate list (distinct gpt points, 0 table
  reads) and inside the table list (points whose precertified tangent interval contains [L, U]); previous-leaf contexts.
Entropies are given two ways: plug-in (empirical) and ADAPTIVE (sequential KT code length in walk order, a realisable cost).
usage: python3 decode_ctx.py DATA.json IV.json OUT.json"""
import os, sys, json, math, collections
sys.setrecursionlimit(100000)
DJ, IVJ, OUTJ = sys.argv[1:4]
D = json.load(open(DJ))
sys.path.insert(0, os.path.dirname(os.path.abspath(DJ))); sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/eight/am8")
import tz
Q = len(D["bN"]); PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
assert D["pairs"] == ["%d,%d" % p for p in PAIRS]
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]; NC = len(SUMS)
AXB = max(1, (Q + NC - 1).bit_length()); BSPLIT = bool(D["params"].get("BSPLIT", 0)); BND = D["params"].get("BND", []); BMG = D["params"].get("BMARG", 64)
NOREFL = D["settings"].get("NOREFL") == "1"
JB, LB, QB = int(D["params"]["JB"]), int(D["params"]["LB"]), int(D["params"]["QB"])
JSH = int(D["params"]["JSH"]); GS = int(D["params"]["GSH"]); TWOGRID = D["settings"].get("TWOGRID") == "1"; PLO = D["settings"].get("PLO") == "1"
JLO = (1 << JSH) + 1
ACT = [p for p, a in zip(PAIRS, D["aN"]) if a > 0]
IVS = {int(p): tuple(v) for p, v in json.load(open(IVJ))["ivs"].items()} if IVJ != '-' else {}
PTS = sorted(int(x) for x, _ in D["tables"]["points"])
def bcut(lo, hi):
    best = None
    for z in BND:
        if lo + BMG <= z <= hi - BMG and (best is None or abs(2 * z - lo - hi) < abs(2 * best - lo - hi)): best = z
    assert best is not None
    return best
def gpt(L, U, jj):
    if jj == JLO: return L
    gs = (GS if jj >> (JSH + 1) else 8) if TWOGRID else GS; j = jj & ((1 << (JSH + 1)) - 1)
    gm = (1 << gs) - 1; ga = ((L + gm) >> gs) << gs; gb = (U >> gs) << gs; x = ((L + (((U - L) * j) >> JSH)) >> gs) << gs
    r = ga if x <= ga else (gb if gb <= x else x)
    return r if ga <= gb else (r if L <= r <= U else None)
CODES = [j + (1 << (JSH + 1)) * f for f in ([0, 1] if TWOGRID else [0]) for j in range((1 << JSH) + 1)] + ([JLO] if PLO else [])
_m1 = {}
def m1list(L, U):
    """distinct gpt points in code order: [(p, first code)]"""
    k = (L, U)
    if k not in _m1:
        seen = {};
        for jj in CODES:
            p = gpt(L, U, jj)
            if p is not None and p not in seen: seen[p] = jj
        _m1[k] = list(seen.items())
    return _m1[k]
# ---- the walk
LEAVES = []; SPLITS = []; BITS = collections.Counter()
def leaf(W_, pos, I, meta):
    p_ = pos + 2; BITS['leaf_head'] += 2; terms = {}
    for t in ACT:
        k = (W_ >> p_) & 3; p_ += 2; BITS['kappa'] += 2; j1 = j2 = lam = None
        if k >= 1: j1 = (W_ >> p_) & ((1 << JB) - 1); p_ += JB; BITS['j'] += JB
        if k == 3: j2 = (W_ >> p_) & ((1 << JB) - 1); p_ += JB; BITS['j'] += JB
        if k >= 2: lam = (W_ >> p_) & ((1 << LB) - 1); p_ += LB; BITS['lambda'] += LB
        L, U = I[t]; terms[t] = (k, j1, j2, lam, L, U)
    mults = []
    while (W_ >> p_) & 1:
        c = (W_ >> (p_ + 1)) & 31; sd = (W_ >> (p_ + 6)) & 1; yq = (W_ >> (p_ + 7)) & ((1 << QB) - 1)
        mults.append((c, sd, yq)); p_ += 7 + QB; BITS['mult_blocks'] += 7 + QB
    BITS['mult_stop'] += 1
    LEAVES.append(dict(meta, terms=terms, mults=mults))
    return p_ + 1
def walk(W_, l, u, cons, pos, root, meta):
    r_ = tz.close(l, u, dict(cons), Q); assert r_ is not None
    l2, u2, cons2, I = r_; cons2 = {t: tuple(v) for t, v in cons2.items()}
    if (W_ >> pos) & 1:
        ax = (W_ >> (pos + 1)) & ((1 << AXB) - 1)
        md = (W_ >> (pos + 1 + AXB)) & 1 if BSPLIT else 0; p2 = pos + 2 + AXB if BSPLIT else pos + 1 + AXB
        BITS['split_flag'] += 1; BITS['split_axis'] += AXB; BITS['split_mode'] += (1 if BSPLIT else 0)
        SPLITS.append(dict(ax=ax, md=md, depth=meta['depth'], parent_ax=meta.get('pax')))
        m2 = dict(meta, depth=meta['depth'] + 1, pax=ax)
        if ax < Q:
            m = bcut(l2[ax], u2[ax]) if md else (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
            e = walk(W_, l2, uA, dict(cons2), p2, False, dict(m2, child='A')); return walk(W_, lB, u2, dict(cons2), e, False, dict(m2, child='B'))
        t = SUMS[ax - Q]; lo, hi = cons2[t]; m = bcut(lo, hi) if md else (lo + hi) >> 1
        cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
        e = walk(W_, l2, u2, cA, p2, False, dict(m2, child='A')); return walk(W_, l2, u2, cB, e, False, dict(m2, child='B'))
    BITS['leaf_flag'] += 1
    if u2[Q - 1] < l2[0] and not NOREFL: LEAVES.append(dict(meta, refl=True)); return pos + 1
    BITS['leaf_flag'] -= 1
    return leaf(W_, pos, I, meta)
tot = 0
for ri, wk in enumerate(D["walks"]):
    box = wk["cell"]; W_ = int(wk["hex"], 16)
    e = walk(W_, [c[0] for c in box], [c[1] for c in box], {}, 0, True, dict(root=ri, depth=0, child=None))
    assert e == wk["nbits"], (ri, e, wk["nbits"]); tot += e
assert sum(BITS.values()) == tot, (sum(BITS.values()), tot)
M = [x for x in LEAVES if not x.get('refl')]; NL = len(LEAVES)
print('walk bits %d over %d leaves (%d M, %d reflected) = %.1f bits/leaf; %d splits' % (tot, NL, len(M), NL - len(M), tot / NL, len(SPLITS)), flush=True)
print('bits by field per leaf:', {k: round(v / NL, 2) for k, v in BITS.items()}, flush=True)
# ---- entropy helpers
def H(cnt):
    n = sum(cnt.values()); return -sum(c / n * math.log2(c / n) for c in cnt.values() if c) if n else 0.0
def Hcond(pairs_):
    by = collections.defaultdict(collections.Counter)
    for c, s in pairs_: by[c][s] += 1
    n = len(pairs_); return sum(sum(v.values()) / n * H(v) for v in by.values()) if n else 0.0
def adaptive(pairs_, A):
    """sequential KT code length (bits per symbol) of symbols s under contexts c, alphabet size A"""
    by = collections.defaultdict(collections.Counter); tot_ = 0.0; nc = collections.Counter()
    for c, s in pairs_:
        tot_ += -math.log2((by[c][s] + 0.5) / (nc[c] + 0.5 * A)); by[c][s] += 1; nc[c] += 1
    return tot_ / len(pairs_) if pairs_ else 0.0
import heapq
def huff_len(cnt):
    """expected Huffman code length for a counter"""
    if len(cnt) <= 1: return 1.0 if cnt else 0.0
    h = [(c, i, None) for i, c in enumerate(cnt.values())]; heapq.heapify(h); n = sum(cnt.values()); tot_ = 0; k = len(h)
    while len(h) > 1:
        a = heapq.heappop(h); b = heapq.heappop(h); tot_ += a[0] + b[0]; heapq.heappush(h, (a[0] + b[0], k, None)); k += 1
    return tot_ / n
def huff_ctx(pairs_):
    by = collections.defaultdict(collections.Counter)
    for c, s_ in pairs_: by[c][s_] += 1
    n = len(pairs_); return sum(sum(v.values()) / n * huff_len(v) for v in by.values()) if n else 0.0
OUT = {'bits_per_leaf': tot / NL, 'fields_per_leaf': {k: v / NL for k, v in BITS.items()}, 'leaves': NL, 'mleaves': len(M)}
def rep(name, pairs_, A, width):
    r = dict(n=len(pairs_), width=width, H0=H(collections.Counter(s for _, s in pairs_)), Hctx=Hcond(pairs_), adaptive=adaptive(pairs_, A), huffman_ctx=huff_ctx(pairs_))
    OUT[name] = r
    print('  %-46s n %7d  width %5.2f  H0 %5.2f  H|ctx %5.2f  adaptive %5.2f  static Huffman|ctx %5.2f' % (name, r['n'], width, r['H0'], r['Hctx'], r['adaptive'], r['huffman_ctx']), flush=True)
    return r
# ---- kinds
prev = {}                                             # previous M leaf's term tuple per position (walk order)
KP0, KP1, KP2 = [], [], []; lastroot = None
for x in M:
    if x['root'] != lastroot: prev = {}; lastroot = x['root']
    for t in ACT:
        k = x['terms'][t][0]; KP0.append((0, k)); KP1.append((t, k)); pk = prev.get(t, (None,))[0]; KP2.append(((t, pk), k))
    for t in ACT: prev[t] = x['terms'][t]
print('KINDS (per term, 2-bit field):')
rep('kappa', KP0, 4, 2); rep('kappa | position', KP1, 4, 2); rep('kappa | position, prev leaf kappa', KP2, 4, 2)
dist = {t: t[1] - t[0] for t in ACT}
rep('kappa | pair distance', [(dist[t], k) for (t, k) in KP1], 4, 2)
# joint coding of two adjacent term positions (16-ary symbols), static Huffman per position pair, with and without the previous leaf's pair
JP, JPP = [], []; prev = {}; lastroot = None
for x in M:
    if x['root'] != lastroot: prev = {}; lastroot = x['root']
    ks = [x['terms'][t][0] for t in ACT]
    for q in range(0, len(ACT) - 1, 2):
        sym = ks[q] * 4 + ks[q + 1]; JP.append((q, sym)); JPP.append(((q, prev.get(q)), sym)); prev[q] = sym
r1 = rep('kappa PAIRS | position pair (per pair of terms)', JP, 16, 4); r2 = rep('kappa PAIRS | position pair, prev leaf pair', JPP, 16, 4)
OUT['kappa_pair_huff_per_term'] = r1['huffman_ctx'] / 2; OUT['kappa_pair_prev_huff_per_term'] = r2['huffman_ctx'] / 2
print('  per term: pair Huffman %.2f, with previous leaf pair %.2f' % (r1['huffman_ctx'] / 2, r2['huffman_ctx'] / 2))
# ---- point codes
print('POINT CODES (per jj field, 7 bits):')
J0, Jpos, Jprevjj, Jprevp, M1k, M1size, P2k, P2size = [], [], [], [], [], [], [], []; RK1, RK2, P2pos, DL, GAM = [], [], [], [], []
stats = collections.Counter(); prev = {}; lastroot = None
for x in M:
    if x['root'] != lastroot: prev = {}; lastroot = x['root']
    for t in ACT:
        k, j1, j2, lam, L, U = x['terms'][t]
        for slot, jj in ((1, j1), (2, j2)):
            if jj is None: continue
            p = gpt(L, U, jj); lst = m1list(L, U); pts = [q for q, _ in lst]; codes = [c for _, c in lst]
            stats['codes'] += 1
            if p is None: stats['p_none'] += 1; continue
            if p not in pts: stats['p_not_in_list'] += 1; continue
            i = pts.index(p)
            if codes[i] != jj: stats['noncanonical_code'] += 1
            J0.append((0, jj)); Jpos.append(((t, slot), jj))
            M1k.append((len(lst), i)); M1size.append(len(lst))
            mid = (L + U) / 2; near = min(range(len(pts)), key=lambda q: (abs(pts[q] - mid), q))
            stats['m1_first'] += (i == 0); stats['m1_nearest_mid'] += (i == near)
            # table list: reachable points that are table points with an interval containing [L, U]
            p2 = [q for q in pts if q in IVS and IVS[q][0] <= L and U <= IVS[q][1]]
            if p in p2:
                i2 = p2.index(p); P2k.append((len(p2), i2)); P2size.append(len(p2))
                near2 = min(range(len(p2)), key=lambda q: (abs(p2[q] - mid), q))
                stats['p2_first'] += (i2 == 0); stats['p2_nearest_mid'] += (i2 == near2); stats['p2_in'] += 1
            else: stats['p2_out'] += 1
            stats['blocks_spanned'] += (U >> 10) - (L >> 10) + 1
            pv = prev.get(t)
            pj = pv[slot] if (pv is not None and pv[0] >= slot and pv[slot] is not None) else None
            pp_ = gpt(pv[4], pv[5], pj) if pj is not None else None
            if pp_ is not None:                    # rank of the chosen point by distance from the previous leaf's point
                o1 = sorted(range(len(pts)), key=lambda q: (abs(pts[q] - pp_), q)); RK1.append(((t, slot), o1.index(i)))
                o2 = sorted(p2, key=lambda q: (abs(q - pp_), q)) if p in p2 else None
                if o2 is not None: RK2.append(((t, slot), o2.index(p)))
            else:
                RK1.append((('none', t, slot), i))
                if p in p2: RK2.append((('none', t, slot), p2.index(p)))
            if p in p2: P2pos.append(((t, slot, len(p2)), p2.index(p)))
            if pp_ is not None:
                d_ = p - pp_; DL.append(((t, slot), d_ // 32 if d_ % 32 == 0 else ('off', d_)))
                g_ = abs(d_ // 32) if d_ % 32 == 0 else None
                GAM.append(1 + (2 * (g_ + 1).bit_length() - 1 + (1 if g_ else 0)) if g_ is not None else 1 + 7 + 19)
            else: GAM.append(1 + 7)
            Jprevjj.append(((t, slot, pj), jj))
            if pj is not None:
                stats['prev_avail'] += 1; stats['prev_same_jj'] += (pj == jj)
                pp = gpt(pv[4], pv[5], pj); stats['prev_same_p'] += (pp == p)
                stats['prev_p_in_list'] += (pp in pts)
                Jprevp.append((pp in pts and pts.index(pp) == i, len(lst), i))
            else: Jprevp.append((False, len(lst), i))
    for t in ACT: prev[t] = x['terms'][t]
n_ = stats['codes']
print('  codes %d; p None %d; p not in arithmetic list %d; non-canonical code %d' % (n_, stats['p_none'], stats['p_not_in_list'], stats['noncanonical_code']))
import statistics
print('  arithmetic list size: mean %.1f, median %d, mean log2 %.2f; first hit %.1f%%, nearest-mid hit %.1f%%' % (
    statistics.mean(M1size), statistics.median(M1size), statistics.mean(math.log2(s) for s in M1size), 100 * stats['m1_first'] / len(M1k), 100 * stats['m1_nearest_mid'] / len(M1k)))
print('  table list: chosen point inside %d, outside %d; size mean %.2f median %d mean log2 %.2f; first hit %.1f%%, nearest-mid %.1f%%; blocks spanned per range mean %.1f' % (
    stats['p2_in'], stats['p2_out'], statistics.mean(P2size) if P2size else 0, statistics.median(P2size) if P2size else 0,
    statistics.mean(math.log2(s) for s in P2size) if P2size else 0, 100 * stats['p2_first'] / max(1, stats['p2_in']), 100 * stats['p2_nearest_mid'] / max(1, stats['p2_in']), stats['blocks_spanned'] / max(1, n_)))
print('  previous leaf same position: available %d (%.1f%%), same jj %.1f%%, same point %.1f%%, prev point in current list %.1f%%' % (
    stats['prev_avail'], 100 * stats['prev_avail'] / n_, 100 * stats['prev_same_jj'] / max(1, stats['prev_avail']), 100 * stats['prev_same_p'] / max(1, stats['prev_avail']), 100 * stats['prev_p_in_list'] / max(1, stats['prev_avail'])))
rep('jj (order 0)', J0, 128, 7); rep('jj | position, slot', Jpos, 128, 7); rep('jj | position, slot, prev jj', Jprevjj, 128, 7)
rep('index in arithmetic list | list size', M1k, 68, 7)
OUT['m1_mean_log2'] = statistics.mean(math.log2(s) for s in M1size)
hit = [r for r in Jprevp if r[0]]; miss = [(sz, i) for f, sz, i in Jprevp if not f]; ps_ = len(hit) / len(Jprevp)
hb = -(ps_ * math.log2(ps_) + (1 - ps_) * math.log2(1 - ps_)) if 0 < ps_ < 1 else 0.0
cm = adaptive(miss, 68); two = hb + (1 - ps_) * cm
print('  same-point flag + index in arithmetic list otherwise: P(same) %.3f, flag %.2f + miss index %.2f -> %.2f bits per code' % (ps_, hb, cm, two))
OUT['same_point_two_part'] = dict(p_same=ps_, bits=two)
if P2k: rep('index in table list | list size', P2k, 68, 7); OUT['p2_mean_log2'] = statistics.mean(math.log2(s) for s in P2size)
rep('rank in arithmetic list by distance from prev point', RK1, 68, 7)
rep('point delta from prev point (fine-grid units) | position', DL, 4096, 7)
OUT['delta_gamma_bits'] = statistics.mean(GAM); print('  delta from prev point, escape bit + Elias gamma (+ sign), else 1 + 7: %.2f bits per code; deltas off the fine grid %d' % (OUT['delta_gamma_bits'], sum(1 for _, d in DL if isinstance(d, tuple))))
rep('rank in table list by distance from prev point', RK2, 68, 7)
rep('index in table list | position, slot, size', P2pos, 68, 7)
OUT['point_stats'] = dict(stats)
# ---- lambda
print('LAMBDA (10 bits):')
L0, Lk, Lkt = [], [], []; prev = {}; same = 0; av = 0; lastroot = None
for x in M:
    if x['root'] != lastroot: prev = {}; lastroot = x['root']
    for t in ACT:
        k, j1, j2, lam, L, U = x['terms'][t]
        if lam is None: continue
        L0.append((0, lam)); Lk.append((k, lam)); Lkt.append(((k, t), lam))
        pv = prev.get(t); pl = pv[3] if pv is not None else None
        if pl is not None: av += 1; same += (pl == lam)
    for t in ACT: prev[t] = x['terms'][t]
rep('lambda (order 0)', L0, 1024, 10); rep('lambda | kappa', Lk, 1024, 10); rep('lambda | kappa, position', Lkt, 1024, 10)
print('  lambda same as previous leaf (same position): %.1f%% of %d' % (100 * same / max(1, av), av))
OUT['lambda_same_prev'] = same / max(1, av)
# ---- multipliers and splits
print('MULTIPLIERS and SPLITS:')
nm = collections.Counter(len(x['mults']) for x in M); print('  blocks per M leaf:', dict(sorted(nm.items())))
rep('mult c', [(0, c) for x in M for c, _, _ in x['mults']], 32, 5); rep('mult side | c', [(c, s) for x in M for c, s, _ in x['mults']], 2, 1)
rep('mult Yq (order 0)', [(0, y) for x in M for _, _, y in x['mults']], 1 << QB, QB)
rep('split axis', [(0, s['ax']) for s in SPLITS], 1 << AXB, AXB); rep('split axis | parent axis', [(s['parent_ax'], s['ax']) for s in SPLITS], 1 << AXB, AXB)
rep('split mode', [(0, s['md']) for s in SPLITS], 2, 1)
NT = len(KP0) / NL; NJ = len(J0) / NL; NLAM = len(L0) / NL; NMB = sum(len(x['mults']) for x in M) / NL; NS = len(SPLITS) / NL
fixed = BITS['leaf_head'] / NL + BITS['leaf_flag'] / NL + BITS['mult_stop'] / NL + NS * (1 + (1 if BSPLIT else 0))
def bound(kap, jj, lam, mc, ms, my, ax):
    return fixed + NT * kap + NJ * jj + NLAM * lam + NMB * (1 + mc + ms + my) + NS * ax
A = OUT
rows = [
 ('today (fixed widths)', 2, 7, 10, 5, 1, QB, AXB),
 ('order 0 (adaptive)', A['kappa']['adaptive'], A['jj (order 0)']['adaptive'], A['lambda (order 0)']['adaptive'], A['mult c']['adaptive'], 1, A['mult Yq (order 0)']['adaptive'], A['split axis']['adaptive']),
 ('kernel-cheap contexts (position, previous leaf, arithmetic list)', A['kappa | position, prev leaf kappa']['adaptive'],
   min(A['jj | position, slot, prev jj']['adaptive'], A['rank in arithmetic list by distance from prev point']['adaptive'], OUT['same_point_two_part']['bits']),
   A['lambda | kappa']['adaptive'], A['mult c']['adaptive'], A['mult side | c']['adaptive'], A['mult Yq (order 0)']['adaptive'], A['split axis']['adaptive']),
 ('kernel-cheap, static prefix codes (Huffman per context; delta-gamma points)', min(A['kappa | position, prev leaf kappa']['huffman_ctx'], OUT['kappa_pair_prev_huff_per_term']),
   min(OUT['delta_gamma_bits'], A['jj | position, slot']['huffman_ctx']), A['lambda | kappa']['huffman_ctx'], A['mult c']['huffman_ctx'], 1, A['mult Yq (order 0)']['huffman_ctx'], A['split axis']['huffman_ctx']),
 ('plus the table list (not <= 2 reads)', A['kappa | position, prev leaf kappa']['adaptive'],
   min(A['index in table list | list size']['adaptive'], A['rank in table list by distance from prev point']['adaptive'], A['index in table list | position, slot, size']['adaptive']),
   A['lambda | kappa']['adaptive'], A['mult c']['adaptive'], A['mult side | c']['adaptive'], A['mult Yq (order 0)']['adaptive'], A['split axis']['adaptive']),
]
print('BOUND (bits per leaf; per-leaf counts: %.2f kinds, %.2f point codes, %.2f lambdas, %.3f multiplier blocks, %.3f splits; fixed %.2f):' % (NT, NJ, NLAM, NMB, NS, fixed))
OUT['bound'] = {}
for name, *v in rows:
    b_ = bound(*v); OUT['bound'][name] = dict(bits=b_, fields=v)
    print('  %-70s %7.1f  (kappa %.2f, jj %.2f, lambda %.2f; hex KB in the file at %d leaves: %.0f)' % (name, b_, v[0], v[1], v[2], NL, b_ * NL / 4 / 1000))
json.dump(OUT, open(OUTJ, 'w'), default=float)
