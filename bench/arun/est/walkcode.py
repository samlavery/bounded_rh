"""Round 13: shared code spec for the PC9Q-family walk (codes A, B, C, each switchable) with a reference encoder and decoder.

Codes (built from a decoded walk; canonical, length-limited to 15 by package-merge, every symbol encodable through ESC):
  A  kinds of two terms jointly: context q = term-position pair (ACT[2q], ACT[2q+1]), symbol 4*kappa_a + kappa_b (alphabet 16)
  B  point code jj: context (t, slot), t = term position 0..33 in ACT order, slot 1 (j1) or 2 (j2); symbol jj (alphabet 128)
  C  lambda: context kappa (2 or 3); symbol lambda (alphabet 2^LB)
  Each code carries ESC = alphabet size, pseudo-count 1; ESC is followed by the symbol as a raw fixed-width field.
Bit order (as the Lean walk reads): the walk is one natural number, LSB-first: the k-th bit read is bit pos + k.
  Raw fixed-width fields are written value-LSB first (as today).  A prefix codeword is written MSB first: its first (most
  significant) bit at the lowest position.  Canonical codewords: symbols sorted by (length, symbol); first[1] = 0,
  first[l+1] = (first[l] + count[l]) << 1; decode reads bits one at a time, code = 2 code + bit, and stops at the first l with
  code - first[l] < count[l]; the symbol is the (offset[l] + code - first[l])-th in the sorted list.
New leaf layout (M leaf; head bits unchanged): for q = 0..16: [A(q) or kappa_a 2, kappa_b 2] [fields of ACT[2q]] [fields of ACT[2q+1]];
  fields of a term: [j1: B(t,1) or 7 raw if kappa >= 1] [j2: B(t,2) or 7 raw if kappa = 3] [lambda: C(kappa) or LB raw if kappa >= 2].
  Without A the order is today's: per term [kappa 2][fields].  Multipliers, splits, reflected leaves: unchanged.
usage: python3 walkcode.py DATA.json SPEC_OUT.json REPORT_OUT.json [SPEC_IN.json]   (SPEC_IN: use given codes instead of building)"""
import os, sys, json, collections, itertools
sys.setrecursionlimit(100000)
DJ, SPEC_OUT, REP_OUT = sys.argv[1:4]; SPEC_IN = sys.argv[4] if len(sys.argv) > 4 else None
D = json.load(open(DJ))
sys.path.insert(0, os.path.dirname(os.path.abspath(DJ))); sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/eight/am8")
import tz
Q = len(D["bN"]); PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]; NC = len(SUMS)
AXB = max(1, (Q + NC - 1).bit_length()); BSPLIT = bool(D["params"].get("BSPLIT", 0)); BND = D["params"].get("BND", []); BMG = D["params"].get("BMARG", 64)
NOREFL = D["settings"].get("NOREFL") == "1"
JB, LB, QB = int(D["params"]["JB"]), int(D["params"]["LB"]), int(D["params"]["QB"])
ACT = [p for p, a in zip(PAIRS, D["aN"]) if a > 0]; NA = len(ACT); assert NA % 2 == 0
LMAX = 15
def bcut(lo, hi):
    best = None
    for z in BND:
        if lo + BMG <= z <= hi - BMG and (best is None or abs(2 * z - lo - hi) < abs(2 * best - lo - hi)): best = z
    assert best is not None
    return best
# ---------- bit streams (LSB-first natural numbers)
class W:
    def __init__(self): self.v = 0; self.n = 0
    def raw(self, x, w):                       # value-LSB first
        assert 0 <= x < (1 << w), (x, w); self.v |= x << self.n; self.n += w
    def code(self, c, l):                      # codeword MSB first
        for k in range(l): self.v |= ((c >> (l - 1 - k)) & 1) << (self.n + k)
        self.n += l
class R:
    def __init__(self, v, pos=0): self.v = v; self.p = pos; self.iters = 0; self.sym = 0; self.reads = 0
    def raw(self, w): x = (self.v >> self.p) & ((1 << w) - 1); self.p += w; return x
    def bit(self): b = (self.v >> self.p) & 1; self.p += 1; return b
# ---------- the walk structure (closure semantics of cert/n9/make9qIR.py build2)
def children(l2, u2, cons2, ax, md):
    if ax < Q:
        m = bcut(l2[ax], u2[ax]) if md else (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
        return (l2, uA, dict(cons2)), (lB, u2, dict(cons2))
    t = SUMS[ax - Q]; lo, hi = cons2[t]; m = bcut(lo, hi) if md else (lo + hi) >> 1
    cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
    return (l2, u2, cA), (l2, u2, cB)
def closed(l, u, cons):
    r_ = tz.close(l, u, dict(cons), Q); assert r_ is not None
    l2, u2, cons2, I = r_; return l2, u2, {t: tuple(v) for t, v in cons2.items()}
def parse_orig(v, l, u, cons, ev):
    """original layout -> event list (split / refl / M) in walk order"""
    rd = R(v)
    def go(l, u, cons):
        l2, u2, cons2 = closed(l, u, cons)
        if rd.bit():
            ax = rd.raw(AXB); md = rd.raw(1) if BSPLIT else 0; ev.append(('S', ax, md))
            A, B = children(l2, u2, cons2, ax, md); go(*A); go(*B); return
        if u2[Q - 1] < l2[0] and not NOREFL: ev.append(('F',)); return
        assert rd.bit() == 0
        terms = []
        for _ in ACT:
            k = rd.raw(2); j1 = rd.raw(JB) if k >= 1 else None; j2 = rd.raw(JB) if k == 3 else None; lam = rd.raw(LB) if k >= 2 else None
            terms.append((k, j1, j2, lam))
        mults = []
        while rd.bit(): mults.append((rd.raw(5), rd.raw(1), rd.raw(QB)))
        ev.append(('M', tuple(terms), tuple(mults)))
    go(l, u, cons); return rd.p
# ---------- codes
def package_merge(w, L):
    """optimal length-limited (<= L) code lengths for weights w (all > 0)"""
    n = len(w)
    if n == 1: return [1]
    items = sorted(((wt, (i,)) for i, wt in enumerate(w)))
    cur = list(items)
    for _ in range(L - 1):
        pk = [(cur[k][0] + cur[k + 1][0], cur[k][1] + cur[k + 1][1]) for k in range(0, len(cur) - 1, 2)]
        cur = sorted(items + pk, key=lambda x: x[0])
    ln = [0] * n
    for wt, idx in cur[:2 * n - 2]:
        for i in idx: ln[i] += 1
    return ln
def build_code(cnt, alpha):
    """lengths {symbol: length} over the seen symbols plus ESC = alpha (pseudo-count 1)"""
    syms = sorted(cnt) + [alpha]; w = [cnt[s] for s in sorted(cnt)] + [1]
    ln = package_merge(w, LMAX); assert max(ln) <= LMAX and sum(2.0 ** -x for x in ln) <= 1 + 1e-12
    return {s: l for s, l in zip(syms, ln)}
ESCN = [0]
class Canon:
    def __init__(self, lengths, alpha, rawbits):
        self.alpha, self.rawbits = alpha, rawbits
        self.syms = sorted(lengths, key=lambda s: (lengths[s], s)); self.len = dict(lengths)
        self.count = [0] * (LMAX + 1)
        for s in self.syms: self.count[lengths[s]] += 1
        self.first = [0] * (LMAX + 2); self.offset = [0] * (LMAX + 2); c = 0; o = 0
        for l in range(1, LMAX + 1):
            self.first[l] = c; self.offset[l] = o; c = (c + self.count[l]) << 1; o += self.count[l]
        self.cw = {}
        nxt = list(self.first)
        for s in self.syms: l = lengths[s]; self.cw[s] = (nxt[l], l); nxt[l] += 1
    def enc(self, wr, s):
        if s in self.cw: c, l = self.cw[s]; wr.code(c, l)
        else: c, l = self.cw[self.alpha]; wr.code(c, l); wr.raw(s, self.rawbits); ESCN[0] += 1
    def dec(self, rd):
        c = 0; rd.sym += 1; rd.reads += 1
        for l in range(1, LMAX + 1):
            c = (c << 1) | rd.bit(); rd.iters += 1
            if c - self.first[l] < self.count[l] and c >= self.first[l]:
                s = self.syms[self.offset[l] + c - self.first[l]]
                return rd.raw(self.rawbits) if s == self.alpha else s
        raise ValueError('bad codeword')
# ---------- the new layout
def enc_leaf(wr, terms, mults, CA, CB, CC):
    wr.raw(0, 1); wr.raw(0, 1)
    def fields(t, k, j1, j2, lam):
        if k >= 1: (CB[(t, 1)].enc(wr, j1) if CB else wr.raw(j1, JB))
        if k == 3: (CB[(t, 2)].enc(wr, j2) if CB else wr.raw(j2, JB))
        if k >= 2: (CC[k].enc(wr, lam) if CC else wr.raw(lam, LB))
    if CA:
        for q in range(NA // 2):
            a, b = terms[2 * q], terms[2 * q + 1]; CA[q].enc(wr, 4 * a[0] + b[0])
            fields(2 * q, *a); fields(2 * q + 1, *b)
    else:
        for t, tm in enumerate(terms): wr.raw(tm[0], 2); fields(t, *tm)
    for c, sd, yq in mults: wr.raw(1, 1); wr.raw(c, 5); wr.raw(sd, 1); wr.raw(yq, QB)
    wr.raw(0, 1)
def dec_leaf(rd, CA, CB, CC):
    assert rd.bit() == 0
    terms = [None] * NA
    def fields(t, k):
        j1 = (CB[(t, 1)].dec(rd) if CB else rd.raw(JB)) if k >= 1 else None
        j2 = (CB[(t, 2)].dec(rd) if CB else rd.raw(JB)) if k == 3 else None
        lam = (CC[k].dec(rd) if CC else rd.raw(LB)) if k >= 2 else None
        return (k, j1, j2, lam)
    if CA:
        for q in range(NA // 2):
            s = CA[q].dec(rd); terms[2 * q] = fields(2 * q, s >> 2); terms[2 * q + 1] = fields(2 * q + 1, s & 3)
    else:
        for t in range(NA): terms[t] = fields(t, rd.raw(2))
    mults = []
    while rd.bit(): mults.append((rd.raw(5), rd.raw(1), rd.raw(QB)))
    return tuple(terms), tuple(mults)
def encode(ev, CA, CB, CC):
    wr = W(); wr.maxleaf = 0; wr.maxsplit = 0
    for e in ev:
        n0 = wr.n
        if e[0] == 'S': wr.raw(1, 1); wr.raw(e[1], AXB); (wr.raw(e[2], 1) if BSPLIT else None); wr.maxsplit = max(wr.maxsplit, wr.n - n0)
        elif e[0] == 'F': wr.raw(0, 1)
        else: enc_leaf(wr, e[1], e[2], CA, CB, CC); wr.maxleaf = max(wr.maxleaf, wr.n - n0)      # from the leaf's node bit to its end
    return wr
def decode(v, l, u, cons, CA, CB, CC):
    rd = R(v); ev = []
    def go(l, u, cons):
        l2, u2, cons2 = closed(l, u, cons)
        if rd.bit():
            ax = rd.raw(AXB); md = rd.raw(1) if BSPLIT else 0; ev.append(('S', ax, md))
            A, B = children(l2, u2, cons2, ax, md); go(*A); go(*B); return
        if u2[Q - 1] < l2[0] and not NOREFL: ev.append(('F',)); return
        t_, m_ = dec_leaf(rd, CA, CB, CC); ev.append(('M', t_, m_))
    go(l, u, cons); return ev, rd
# ---------- run
EV = []
for wk in D["walks"]:
    box = wk["cell"]; v = int(wk["hex"], 16); ev = []
    end = parse_orig(v, [c[0] for c in box], [c[1] for c in box], {}, ev); assert end == wk["nbits"]
    w0 = encode(ev, None, None, None); assert w0.n == wk["nbits"] and w0.v == v, "original layout does not re-encode bit-exactly"
    EV.append(ev)
NL = sum(1 for ev in EV for e in ev if e[0] != 'S'); NM = sum(1 for ev in EV for e in ev if e[0] == 'M')
print('parsed %d walks: %d leaves (%d M), original layout re-encodes bit-exactly' % (len(EV), NL, NM), flush=True)
if SPEC_IN:
    S = json.load(open(SPEC_IN))
    LA = {int(q): {int(s): l for s, l in v.items()} for q, v in S['A']['contexts'].items()}
    LBk = {tuple(map(int, k.split(','))): {int(s): l for s, l in v.items()} for k, v in S['B']['contexts'].items()}
    LC = {int(k): {int(s): l for s, l in v.items()} for k, v in S['C']['contexts'].items()}
else:
    cA = collections.defaultdict(collections.Counter); cB = collections.defaultdict(collections.Counter); cC = collections.defaultdict(collections.Counter)
    for ev in EV:
        for e in ev:
            if e[0] != 'M': continue
            T = e[1]
            for q in range(NA // 2): cA[q][4 * T[2 * q][0] + T[2 * q + 1][0]] += 1
            for t, (k, j1, j2, lam) in enumerate(T):
                if k >= 1: cB[(t, 1)][j1] += 1
                if k == 3: cB[(t, 2)][j2] += 1
                if k >= 2: cC[k][lam] += 1
    LA = {q: build_code(cA[q], 16) for q in range(NA // 2)}
    LBk = {(t, s): build_code(cB[(t, s)], 1 << JB) for t in range(NA) for s in (1, 2)}
    LC = {k: build_code(cC[k], 1 << LB) for k in (2, 3)}
CA = {q: Canon(LA[q], 16, 4) for q in LA}; CB = {k: Canon(LBk[k], 1 << JB, JB) for k in LBk}; CC = {k: Canon(LC[k], 1 << LB, LB) for k in LC}
spec = {
  'source': os.path.basename(DJ), 'max_length': LMAX,
  'bit_order': ('walk = one natural number read LSB-first (k-th bit read = bit pos+k, as rdw/WIN). Raw fixed-width fields: value LSB first. '
                'Prefix codewords: MSB first (first codeword bit at the lowest position). Canonical: symbols sorted by (length, symbol); '
                'first[1] = 0, first[l+1] = (first[l] + count[l]) << 1; decode code = 2*code + bit until code - first[l] < count[l].'),
  'escape': 'each code has ESC = alphabet size (pseudo-count 1); ESC is followed by the symbol as a raw field of raw_bits bits (value LSB first)',
  'leaf_layout': ('M leaf: [0][0]; with A: for q = 0..%d: [A(q)] [fields of term 2q] [fields of term 2q+1]; without A: per term [kappa 2][fields]; '
                  'fields of term t with kind k: [j1: B(t,1) or %d raw, if k >= 1][j2: B(t,2) or %d raw, if k = 3][lambda: C(k) or %d raw, if k >= 2]; '
                  'then multipliers [1][c 5][side 1][Yq %d] closed by [0]. Splits [1][axis %d][mode 1] and reflected leaves [0] unchanged.') % (NA // 2 - 1, JB, JB, LB, QB, AXB),
  'terms': ['%d,%d' % t for t in ACT],
  'A': {'what': 'kinds of terms 2q and 2q+1 jointly, symbol 4*kappa_a + kappa_b', 'alphabet': 16, 'raw_bits': 4,
        'contexts': {str(q): {str(s): l for s, l in sorted(LA[q].items())} for q in sorted(LA)}},
  'B': {'what': 'point code jj of term t (index into terms), slot 1 = j1, 2 = j2', 'alphabet': 1 << JB, 'raw_bits': JB,
        'contexts': {'%d,%d' % k: {str(s): l for s, l in sorted(LBk[k].items())} for k in sorted(LBk)}},
  'C': {'what': 'lambda given kappa', 'alphabet': 1 << LB, 'raw_bits': LB,
        'contexts': {str(k): {str(s): l for s, l in sorted(LC[k].items())} for k in sorted(LC)}},
}
if not SPEC_IN: json.dump(spec, open(SPEC_OUT, 'w'), indent=0)
# ---------- round trip and sizes per set
rep = {'leaves': NL, 'mleaves': NM, 'orig_bits': sum(wk['nbits'] for wk in D['walks'])}
WD = os.environ.get('WDUMP'); DUMPW = {'source': os.path.basename(DJ), 'spec': SPEC_IN or SPEC_OUT, 'hex_convention': 'hex of the walk as one natural number, bit 0 = the first bit read (as DATA walks)', 'variants': {}}
DUMPW['variants']['original'] = [dict(root=wk['root'], cell=wk['cell'], nbits=wk['nbits'], hex=wk['hex'], max_leaf_bits=encode(ev, None, None, None).maxleaf) for ev, wk in zip(EV, D['walks'])]
print('original %d bits = %.1f bits/leaf' % (rep['orig_bits'], rep['orig_bits'] / NL))
for name, a, b, c in [('A', 1, 0, 0), ('B', 0, 1, 0), ('C', 0, 0, 1), ('A+B', 1, 1, 0), ('A+B+C', 1, 1, 1)]:
    ca, cb, cc = (CA if a else None), (CB if b else None), (CC if c else None)
    tot = 0; it = sy = rds = 0; ESCN[0] = 0
    for ev, wk in zip(EV, D['walks']):
        wr = encode(ev, ca, cb, cc); tot += wr.n
        box = wk['cell']; ev2, rd = decode(wr.v, [x[0] for x in box], [x[1] for x in box], {}, ca, cb, cc)
        assert rd.p == wr.n and ev2 == ev, ('round trip failed', name)
        it += rd.iters; sy += rd.sym; rds += rd.reads
        DUMPW['variants'].setdefault(name, []).append(dict(root=wk['root'], cell=wk['cell'], nbits=wr.n, hex=hex(wr.v), max_leaf_bits=wr.maxleaf, max_split_bits=wr.maxsplit))
    rep[name] = dict(bits=tot, bits_per_leaf=tot / NL, hexKB=tot / 4 / 1000, symbols_per_Mleaf=sy / NM, length_iterations_per_Mleaf=it / NM,
                     context_reads_per_Mleaf=rds / NM, escapes=ESCN[0])
    print('%-6s %8d bits = %6.1f bits/leaf (%5.1f%% of original; %.0f KB hex, saves %.0f KB); per M leaf: %.1f codewords, %.1f length-loop steps, %.1f context reads; %d escapes; round trip bit-exact' % (
        name, tot, tot / NL, 100 * tot / rep['orig_bits'], tot / 4000, (rep['orig_bits'] - tot) / 4000, sy / NM, it / NM, rds / NM, ESCN[0]), flush=True)
# ---------- table bytes as Lean hex defs: per context one literal = 15 counts (cb bits each) then the canonical symbol list (sb bits each)

if WD: json.dump(DUMPW, open(WD, 'w')); print('encoded walks written to', WD, {k: (sum(x['nbits'] for x in v), max(x['max_leaf_bits'] for x in v)) for k, v in DUMPW['variants'].items()})
def lit_bits(cn, cb, sb): return LMAX * cb + len(cn.syms) * sb
def lean_bytes(prefix, ctxs, cb, sb):
    tot = 0
    for k, cn in ctxs.items():
        nb = lit_bits(cn, cb, sb); hexd = -(-nb // 4); name = '%s_%s' % (prefix, str(k).replace(', ', '_').replace('(', '').replace(')', ''))
        tot += len(('def %s : ℕ := 0x' % name).encode()) + hexd + 1
    disp = len(ctxs) * len('(dpk j 00 X_00_0) '.encode()) + len(ctxs) * len('def Xs00_00 (j : ℕ) : ℕ := dsel j 00 (Xs) (Xs)\n'.encode())
    return tot, disp
for name, ctxs, cb, sb in [('A', CA, 5, 5), ('B', CB, 8, 8), ('C', CC, 11, 11)]:
    lt, dp = lean_bytes('K' + name, ctxs, cb, sb)
    nsym = sum(len(c.syms) for c in ctxs.values())
    rep['table_' + name] = dict(contexts=len(ctxs), symbols=nsym, literal_bytes=lt, dispatch_bytes_est=dp, total_bytes=lt + dp, max_len=max(max(c.len.values()) for c in ctxs.values()))
    print('table %s: %d contexts, %d listed symbols (incl. ESC), max length %d; literals %d bytes + dispatch ~%d bytes = %.1f KB' % (
        name, len(ctxs), nsym, rep['table_' + name]['max_len'], lt, dp, (lt + dp) / 1000))
json.dump(rep, open(REP_OUT, 'w'), indent=1)
