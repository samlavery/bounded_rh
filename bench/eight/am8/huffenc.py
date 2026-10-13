#!/usr/bin/env python3
"""Reference encoder for the pair-cell walk (spec: HUFF.md).  Reads a size8pz dump (run8pz SAVE: per leaf (box, cons, kind,
payload) in walk order, one subtree per root), rebuilds the walk trees, computes Farkas multipliers for LP-infeasible
cells, builds the canonical Huffman tables from the certificate's own symbols, encodes every node, decodes it back
(round trip), and reports exact bits per component.
Usage: huffenc.py DUMP.pkl W.json [LS] [--golden OUT.json] [--tables OUT.json]"""
import sys, json, pickle, collections, math, heapq, itertools
import numpy as np
from scipy.optimize import linprog

Q = 7; N = Q + 1
PAIRS = [(i, j) for i in range(N) for j in range(i + 1, N)]
NADJ = [t for t, (i, j) in enumerate(PAIRS) if j - i >= 2]          # the 21 sum constraints, in pair order
RANK = {t: k for k, t in enumerate(NADJ)}
JSH = 5; JB = JSH + 2; YB = 12

# ---------------------------------------------------------------- canonical Huffman
def huff_lengths(cnt):
    """code lengths (package-free Huffman); a single symbol gets length 0 (no bits)"""
    if len(cnt) == 1: return {next(iter(cnt)): 0}
    h = [(v, i, (k,)) for i, (k, v) in enumerate(sorted(cnt.items()))]; heapq.heapify(h); L = {k: 0 for k in cnt}; i = len(h)
    while len(h) > 1:
        a = heapq.heappop(h); b = heapq.heappop(h)
        for k in a[2] + b[2]: L[k] += 1
        heapq.heappush(h, (a[0] + b[0], i, a[2] + b[2])); i += 1
    return L
def canonical(lengths):
    """(symbol, length) sorted by (length, symbol) and the code of each symbol: first code 0, then
    code = (code + 1) << (len - prev_len); the codeword's FIRST bit in the walk is its most significant bit"""
    order = sorted(lengths.items(), key=lambda kv: (kv[1], kv[0]))
    codes = {}; code = 0; prev = None
    for s, l in order:
        if l == 0: codes[s] = (0, 0); continue
        if prev is None: code = 0
        else: code = (code + 1) << (l - prev)
        codes[s] = (code, l); prev = l
    return order, codes
def put_code(bits, code, l):
    for k in range(l - 1, -1, -1): bits.append((code >> k) & 1)
def put_field(bits, v, n):
    assert 0 <= v < (1 << n), (v, n)
    for k in range(n): bits.append((v >> k) & 1)
def get_code(bits, pos, order):
    """canonical decode: read bits MSB-first, at each length compare against the first code of that length"""
    if order[0][1] == 0: return order[0][0], pos
    code = 0; l = 0; idx = 0; first = 0; nxt = 0
    by_len = collections.defaultdict(list)
    for s, ln in order: by_len[ln].append(s)
    maxl = max(by_len)
    first = 0
    for ln in range(1, maxl + 1):
        code = (code << 1) | bits[pos]; pos += 1
        cnt = len(by_len.get(ln, []))
        if code - first < cnt: return by_len[ln][code - first], pos
        first = (first + cnt) << 1
    raise ValueError("bad codeword")
def get_field(bits, pos, n):
    return sum(bits[pos + k] << k for k in range(n)), pos + n

# ---------------------------------------------------------------- the cells, Farkas multipliers
def iv0(box): return [(sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))) for (i, j) in PAIRS]
def farkas(box, cons, maxq=15):
    """integer multipliers (t, side) -> Yq >= 1 with  sum const + sum_r (u_r - l_r) max(0, P_r - S_r) < 0, or None"""
    I0 = iv0(box); keys = []; const = []; cols = []
    for t in sorted(cons):
        Lb, Ub = cons[t]; i, j = PAIRS[t]; L0 = I0[t][0]
        if Lb is not None: keys.append((t, 0)); const.append(L0 - Lb); cols.append((i, j, +1))
        if Ub is not None: keys.append((t, 1)); const.append(Ub - L0); cols.append((i, j, -1))
    nk = len(keys)
    if nk == 0: return None
    W = [box[r][1] - box[r][0] for r in range(Q)]
    # variables y (nk) and z (Q): minimise sum const y + sum W z, z_r >= coef_r(y), z >= 0, sum y = 1
    c = np.array(const + W, float)
    A = []; bu = []
    for r in range(Q):
        row = np.zeros(nk + Q)
        for k, (i, j, sg) in enumerate(cols):
            if i <= r < j: row[k] = sg
        row[nk + r] = -1.0; A.append(row); bu.append(0.0)
    Aeq = np.zeros((1, nk + Q)); Aeq[0, :nk] = 1.0
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(bu), A_eq=Aeq, b_eq=[1.0], bounds=[(0, None)] * (nk + Q), method="highs")
    if res.status != 0 or res.fun >= 0: return None
    y = res.x[:nk]
    def test(Yq):
        tot = sum(const[k] * Yq[k] for k in range(nk))
        for r in range(Q):
            co = sum(Yq[k] * sg for k, (i, j, sg) in enumerate(cols) if i <= r < j)
            tot += W[r] * max(0, co)
        return tot < 0
    ymax = y.max()
    for scale in range(1, maxq + 1):
        Yq = [int(round(v / ymax * scale)) for v in y]
        if any(Yq) and test(Yq): return {keys[k]: Yq[k] for k in range(nk) if Yq[k] > 0}
    return None

# ---------------------------------------------------------------- the walk trees from the dump
def rebuild(L):
    """split the leaf list into root subtrees and rebuild each binary tree by replaying the splits: a leaf's cell is
    recovered by matching; here we only need the node sequence, which the dump does not carry, so the trees are
    rebuilt from the cells: two leaves are siblings when their cells differ by one split"""
    raise NotImplementedError

def main():
    dump = pickle.load(open(sys.argv[1], "rb")); J = json.load(open(sys.argv[2]))
    LS = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3].isdigit() else 1024
    LB = LS.bit_length() - 1
    aN = [int(J["aN"][f"{i},{j}"]) for (i, j) in PAIRS]; ACT = [t for t in range(len(PAIRS)) if aN[t] > 0]
    leaves = dump["leaves"] if isinstance(dump, dict) else dump
    splits = dump.get("splits") if isinstance(dump, dict) else None
    # ---- symbols
    term_sym = collections.defaultdict(collections.Counter); recs = []
    nfark = 0; fark_fail = 0
    for box, cons, kind, pay in leaves:
        if kind == 7: recs.append(('empty',)); continue
        if kind == 0: recs.append(('refl',)); continue
        if kind == 8:
            Y = farkas(box, cons)
            if Y is None: fark_fail += 1; Y = {}
            nfark += 1; recs.append(('farkas', Y)); continue
        mc, Ys = pay if kind == 6 else ([(0, 0, 0, 0)] * len(PAIRS), {})
        terms = []
        for t in ACT:
            k, j1, j2, lam = mc[t]
            if k == 3 and lam > LS // 2: j1, j2, lam = j2, j1, LS - lam      # heavier tangent first
            sym = (k, j1 if k >= 1 else 0, j2 if k == 3 else 0)
            term_sym[t][sym] += 1; terms.append((t, sym, lam))
        recs.append(('M', terms, Ys))
    tables = {t: canonical(huff_lengths(term_sym[t])) for t in ACT}
    cnt_c = collections.Counter(); cnt_y = collections.Counter()
    for r in recs:
        if r[0] in ('M', 'farkas'):
            Ys = r[2] if r[0] == 'M' else r[1]
            for (t, side), v in Ys.items(): cnt_c[RANK[t]] += 1
    ctab = canonical(huff_lengths(cnt_c)) if cnt_c else None
    # ---- encode each leaf word (the leaf's own bits; splits are counted separately)
    comp = collections.Counter(); words = []
    for r in recs:
        bits = []
        if r[0] == 'empty': words.append(bits); continue
        put_field(bits, 0, 1)                                            # leaf
        if r[0] == 'refl': comp['leaf/kind'] += 1; words.append(bits); continue
        put_field(bits, 1 if r[0] == 'farkas' else 0, 1); comp['leaf/kind'] += 2
        if r[0] == 'M':
            _, terms, Ys = r
            for t, sym, lam in terms:
                order, codes = tables[t]; code, l = codes[sym]; put_code(bits, code, l); comp['term codes'] += l
                if sym[0] == 2: put_field(bits, lam, LB); comp['lambda'] += LB
                if sym[0] == 3: put_field(bits, lam - 1, LB - 1); comp['lambda'] += LB - 1
            ent = Ys; yb = YB
        else:
            ent = r[1]; yb = 4
        for (t, side) in sorted(ent):
            put_field(bits, 1, 1); code, l = ctab[1][RANK[t]]; put_code(bits, code, l); put_field(bits, side, 1)
            put_field(bits, ent[(t, side)], yb); comp['multipliers'] += 1 + l + 1 + yb
        put_field(bits, 0, 1); comp['multipliers'] += 1
        words.append(bits)
    # ---- round trip
    for r, bits in zip(recs, words):
        if r[0] == 'empty': assert bits == []; continue
        pos = 0; v, pos = get_field(bits, pos, 1); assert v == 0
        if r[0] == 'refl': assert pos == len(bits); continue
        kd, pos = get_field(bits, pos, 1)
        if r[0] == 'M':
            assert kd == 0
            for t, sym, lam in r[1]:
                s, pos = get_code(bits, pos, tables[t][0]); assert s == sym, (s, sym)
                if s[0] == 2: v, pos = get_field(bits, pos, LB); assert v == lam
                if s[0] == 3: v, pos = get_field(bits, pos, LB - 1); assert v == lam - 1
            ent = r[2]; yb = YB
        else: assert kd == 1; ent = r[1]; yb = 4
        got = {}
        while True:
            f, pos = get_field(bits, pos, 1)
            if not f: break
            c, pos = get_code(bits, pos, ctab[0]); side, pos = get_field(bits, pos, 1); yq, pos = get_field(bits, pos, yb)
            got[(NADJ[c], side)] = yq
        assert got == ent and pos == len(bits)
    nsplit = len(leaves) - (dump.get("nroots", 2) if isinstance(dump, dict) else 2)
    kinds = collections.Counter(r[0] for r in recs)
    leafbits = sum(len(w) for w in words)
    print(f"leaves {len(leaves)} {dict(kinds)}; Farkas certified {nfark - fark_fail}/{nfark}; "
          f"leaf bits {leafbits} ({dict(comp)}); M-leaf bits {sum(len(w) for r, w in zip(recs, words) if r[0] == 'M') / max(1, kinds['M']):.1f}, "
          f"Farkas-leaf bits {sum(len(w) for r, w in zip(recs, words) if r[0] == 'farkas') / max(1, kinds['farkas']):.1f}; "
          f"term tables {sum(len(tables[t][0]) for t in ACT)} entries; round trip OK")
    trees = dump.get("trees") if isinstance(dump, dict) else None
    out = dict(leaves=leaves, recs=recs, words=words, tables=tables, ctab=ctab, LS=LS, LB=LB, ACT=ACT, leafbits=leafbits,
               comp=comp, kinds=kinds, trees=trees)
    if not trees: return out
    # ---- the full walk: depth first, a split is [1][axis codeword] then child A (Ub := m / u := m) then child B
    cnt_ax = collections.Counter()
    def axcode(ax): return ax if ax < Q else Q + RANK[ax - Q]
    def axes(nd):
        if nd[0] == 'split': cnt_ax[axcode(nd[3])] += 1; axes(nd[4]); axes(nd[5])
    for tr in trees: axes(tr)
    axtab = canonical(huff_lengths(cnt_ax))
    it = iter(words); walks = []; nodes = []
    def enc(nd, bits, path):
        if nd[0] == 'split':
            start = len(bits); put_field(bits, 1, 1); code, l = axtab[1][axcode(nd[3])]; put_code(bits, code, l)
            nodes.append(dict(path=path, type='split', axis=axcode(nd[3]), box=nd[1], cons=nd[2], bits=bits[start:]))
            enc(nd[4], bits, path + 'A'); enc(nd[5], bits, path + 'B')
        else:
            w = next(it); start = len(bits); bits.extend(w)
            nodes.append(dict(path=path, type={0: 'reflected', 6: 'M', 8: 'farkas', 7: 'empty'}.get(nd[3], str(nd[3])),
                              box=nd[1], cons=nd[2], bits=w))
    for tr in trees:
        bits = []; enc(tr, bits, ''); walks.append(bits)
    walkbits = sum(len(b) for b in walks)
    nsp = sum(cnt_ax.values()); Hx = -sum(v / nsp * math.log2(v / nsp) for v in cnt_ax.values())
    axb = sum(cnt_ax[a_] * (1 + axtab[1][a_][1]) for a_ in cnt_ax)
    print(f"splits {nsp}: {axb / nsp:.2f} bits per split incl. the split bit (fixed 6; axis entropy {Hx:.2f}); "
          f"walk {walkbits} bits = {walkbits / 4 / 1e3:.2f} KB hex ({walkbits / len(leaves):.1f} bits per leaf)")
    out.update(axtab=axtab, walks=walks, nodes=nodes, walkbits=walkbits)
    return out

def dump_spec(res, tables_path, golden_path, J, ngold=20):
    ACT = res['ACT']
    T = dict(JSH=JSH, JB=JB, LS=res['LS'], LB=res['LB'], YB=YB, YB_farkas=4,
             symbol="kappa * 2^14 + j1 * 2^7 + j2",
             term_tables={f"{PAIRS[t][0]},{PAIRS[t][1]}": [[int(s[0] * 16384 + s[1] * 128 + s[2]), int(l)] for s, l in res['tables'][t][0]] for t in ACT},
             axis_table=[[int(a_), int(l)] for a_, l in res['axtab'][0]],
             c_table=[[int(c), int(l)] for c, l in res['ctab'][0]],
             sum_constraints_in_rank_order=[f"{PAIRS[t][0]},{PAIRS[t][1]}" for t in NADJ])
    json.dump(T, open(tables_path, "w"), indent=1)
    walk = res['walks'][0]
    nat = sum(b << k for k, b in enumerate(walk))
    G = dict(note="root 0 of the dump; walk bits LSB-first: bit k of the Nat is the k-th bit written", walk_bits=len(walk),
             walk_hex=hex(nat), nodes=[])
    off = 0
    for nd in res['nodes'][:ngold]:
        e = dict(path=nd['path'], type=nd['type'], box=[list(x) for x in nd['box']],
                 cons={f"{PAIRS[t][0]},{PAIRS[t][1]}": list(v) for t, v in nd['cons'].items()}, bits="".join(map(str, nd['bits'])))
        if nd['type'] == 'split': e['axis'] = nd['axis']
        G['nodes'].append(e)
    # decoded fields of the leaves among the golden nodes
    li = 0; leaf_iter = iter(zip(res['recs'], res['leaves']))
    for e in G['nodes']:
        if e['type'] == 'split': continue
        rec, lf = next(leaf_iter)
        if rec[0] == 'M':
            e['terms'] = [dict(pair=f"{PAIRS[t][0]},{PAIRS[t][1]}", kappa=s_[0], j1=s_[1], j2=s_[2], lam=lam if s_[0] >= 2 else None) for t, s_, lam in rec[1]]
            e['multipliers'] = [dict(c=RANK[t], pair=f"{PAIRS[t][0]},{PAIRS[t][1]}", side=sd, Yq=v) for (t, sd), v in sorted(rec[2].items())]
        elif rec[0] == 'farkas':
            e['multipliers'] = [dict(c=RANK[t], pair=f"{PAIRS[t][0]},{PAIRS[t][1]}", side=sd, Yq=v) for (t, sd), v in sorted(rec[1].items())]
    json.dump(G, open(golden_path, "w"), indent=1)
    print(f"wrote {tables_path} and {golden_path} ({len(G['nodes'])} nodes, walk {len(walk)} bits)")

if __name__ == "__main__":
    res = main()
    if "--golden" in sys.argv:
        J = json.load(open(sys.argv[2]))
        dump_spec(res, sys.argv[sys.argv.index("--tables") + 1], sys.argv[sys.argv.index("--golden") + 1], J)
