#!/usr/bin/env python3
"""gen_huffbench.py DATA.json NLEAF OUTNAME: in-kernel leaf-payload decode cost, fixed-width against canonical Huffman and
Huffman with a same-as-previous flag (am-cert, 2026-10-10; bench only, certifies nothing).

The leaves are PC8C5BF's (DATA_try2cb): the replay of verify8pz.py (exec'd with a recorder around `mcheck`) gives each
minorant leaf's terms (κ, j1, j2, λ) and ranges.  Per active term, a canonical Huffman table over the symbol
κ·2^14 + j1·2^7 + j2 (HUFF.md / PCellHuff's convention; λ follows the codeword raw: LB bits for κ = 2, λ − 1 in LB − 1 bits
for κ = 3).  Three decoders, each one unrolled CPS chain over the 26 terms that returns the payload end offset:
  decF  — the fixed-width fields with `dec4F` (as PC8C5BF's mleafP reads them);
  decH  — `hdec` (canonical code, bit-serial) then `dec4S`;
  decS  — a flag bit per term: 1 = the previous leaf's symbol for this term (passed in), 0 = `hdec`; then `dec4S`.
Grid points are computed on each term's real range in all three, so only the field decoding differs.
One `decide +kernel` theorem per leaf and decoder; kernel time per declaration comes from ReplayTimes."""
import sys, os, json, math, collections, io, contextlib, heapq
DATA, NLEAF, OUT = sys.argv[1], int(sys.argv[2]), sys.argv[3]
VER = os.path.expanduser("~/work/riemann-submission/bench/eight/am8/verify8pz.py")
src = open(VER, encoding="utf-8").read()
src = src.replace("ax = get(5)", "ax = get((Q + len(NADJ) - 1).bit_length())")
src = src.replace("stats = dict(", """_LEAVES = []
_mcheck0 = mcheck
def mcheck(l, u, cons, I, terms, Ys):
    _LEAVES.append((dict(I), list(terms)))
    return _mcheck0(l, u, cons, I, terms, Ys)
stats = dict(""", 1)
sys.argv = [VER, DATA]; sys.path.insert(0, os.path.dirname(VER))
g = {"__name__": "__main__", "__file__": VER}
with contextlib.redirect_stdout(io.StringIO()):
    exec(compile(src, VER, "exec"), g)
LV = g["_LEAVES"]; PAIRS = g["PAIRS"]; LB = g["LB"]; JB = g["JB"]
ACT = [t for t, _ in LV[0][1]]
assert JB == 7 and LB == 8

def huff_lengths(cnt):
    if len(cnt) == 1: return {next(iter(cnt)): 0}
    h = [(v, i, (k,)) for i, (k, v) in enumerate(sorted(cnt.items()))]; heapq.heapify(h); Ln = {k: 0 for k in cnt}; i = len(h)
    while len(h) > 1:
        a = heapq.heappop(h); b = heapq.heappop(h)
        for k in a[2] + b[2]: Ln[k] += 1
        heapq.heappush(h, (a[0] + b[0], i, a[2] + b[2])); i += 1
    return Ln
def canonical(lengths):
    order = sorted(lengths.items(), key=lambda kv: (kv[1], kv[0])); codes = {}; code = 0; prev = None
    for s, l in order:
        if l == 0: codes[s] = (0, 0); continue
        code = 0 if prev is None else (code + 1) << (l - prev); codes[s] = (code, l); prev = l
    return order, codes
def symb(k, j1, j2): return (k << 14) | ((j1 if k >= 1 else 0) << 7) | (j2 if k == 3 else 0)
cnt = collections.defaultdict(collections.Counter)
for I, terms in LV:
    for t, (k, j1, j2, lam) in terms: cnt[t][symb(k, j1, j2)] += 1
TAB = {}
for t in ACT:
    order, codes = canonical(huff_lengths(cnt[t]))
    mx = max(l for _, l in order); c = [0] * (mx + 1)
    for _, l in order: c[l] += 1
    assert mx <= 32 and all(s < 65536 for s, _ in order)
    TAB[t] = (codes, hex(sum(v << (16 * i) for i, v in enumerate(c))), hex(sum(s << (16 * i) for i, (s, _) in enumerate(order))))

def put(bits, v, n):
    for k in range(n): bits.append((v >> k) & 1)
def put_code(bits, code, l):
    for k in range(l - 1, -1, -1): bits.append((code >> k) & 1)
def word(bits): return sum(b << k for k, b in enumerate(bits))
def encF(terms):
    b = []
    for t, (k, j1, j2, lam) in terms:
        put(b, k, 2)
        if k >= 1: put(b, j1, 7)
        if k == 3: put(b, j2, 7)
        if k >= 2: put(b, lam, LB)
    return b
def lam_bits(b, k, lam):
    if k == 2: put(b, lam, LB)
    if k == 3: put(b, lam - 1, LB - 1)
def encH(terms):
    b = []
    for t, (k, j1, j2, lam) in terms:
        put_code(b, *TAB[t][0][symb(k, j1, j2)]); lam_bits(b, k, lam)
    return b
def encS(terms, prev):
    b = []; same = 0
    for t, (k, j1, j2, lam) in terms:
        s = symb(k, j1, j2)
        if prev.get(t) == s: b.append(1); same += 1
        else: b.append(0); put_code(b, *TAB[t][0][s])
        lam_bits(b, k, lam)
    return b, same

KB = int(os.environ.get("KB", "0"))      # > 0: also decL, the lookup decode `hdecL` on the next KB bits
def lut(codes):
    ent = [0] * (1 << KB)
    for s, (c, l) in codes.items():
        if l == 0 or l > KB: continue
        b = sum(((c >> (l - 1 - i)) & 1) << i for i in range(l))       # walk order: the codeword's MSB first = bit 0
        for hi in range(1 << (KB - l)): ent[b | (hi << l)] = s + (1 << 16) * (l + 1)
    return hex(sum(e << (24 * i) for i, e in enumerate(ent)))
def nm(t): return f"{PAIRS[t][0]}{PAIRS[t][1]}"
LU = " ".join(f"L{nm(t)} U{nm(t)}" for t in ACT)
PS = " ".join(f"s{nm(t)}" for t in ACT)
def chain(kind):
    out = []
    for q, t in enumerate(ACT):
        n = nm(t); o = f"o{q}"; o1 = f"o{q + 1}"
        if kind == "F":
            out.append(f"  dec4F 8 w {o} L{n} U{n} fun k{n} m{n} p{n} r{n} {o1} =>")
        elif kind == "X":   # flag 1: re-read the previous leaf's fields (word x{n}, offset 0); flag 0: the fields at o + 1
            out.append(f"  forceR (Nat.land (Nat.shiftRight w {o}) 1) fun f{n} => "
                       f"dec4F 8 (Bool.rec (motive := fun _ => ℕ) w x{n} (Nat.beq f{n} 1)) "
                       f"(Bool.rec (motive := fun _ => ℕ) (Nat.add {o} 1) 0 (Nat.beq f{n} 1)) L{n} U{n} fun k{n} m{n} p{n} r{n} e{n} => "
                       f"forceR (Bool.rec (motive := fun _ => ℕ) e{n} (Nat.add {o} 1) (Nat.beq f{n} 1)) fun {o1} =>")
        elif kind == "L":
            out.append(f"  forceR (hdecL {(1 << KB) - 1} HL{n} HC{n} HS{n} w {o}) fun h{n} => dec4S 8 h{n} w {o} L{n} U{n} fun k{n} m{n} p{n} r{n} {o1} =>")
        elif kind == "H":
            out.append(f"  forceR (hdec HC{n} HS{n} w {o}) fun h{n} => dec4S 8 h{n} w {o} L{n} U{n} fun k{n} m{n} p{n} r{n} {o1} =>")
        else:   # flag bit, then the previous symbol (its codeword length 0) or the codeword
            out.append(f"  forceR (Bool.rec (motive := fun _ => ℕ) (hdec HC{n} HS{n} w (Nat.add {o} 1)) s{n} "
                       f"(Nat.beq (Nat.land (Nat.shiftRight w {o}) 1) 1)) fun h{n} => "
                       f"dec4S 8 h{n} w (Nat.add {o} 1) L{n} U{n} fun k{n} m{n} p{n} r{n} {o1} =>")
    out.append(f"  o{len(ACT)}")
    return "\n".join(out)
p = os.path.expanduser(f"~/work/riemann-submission/bench/window/rootR8f/AMW/{OUT}.lean")
if os.path.exists(p): raise SystemExit(f"{p} exists")
L = ["import AMW.PCellT1\nimport AMW.PCellHuff\n", "/-! leaf-payload decode bench (am-cert): fixed-width vs Huffman vs Huffman + same flag; certifies nothing -/\n",
     "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n", "noncomputable section\n", f"namespace AMW.Cert.{OUT}\n",
     "open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell\n"]
for t in ACT:
    L.append(f"def HC{nm(t)} : ℕ := {TAB[t][1]}\ndef HS{nm(t)} : ℕ := {TAB[t][2]}")
L.append(f"def decF (w {LU} : ℕ) : ℕ :=\n  forceR 0 fun o0 =>\n{chain('F')}")
L.append(f"def decH (w {LU} : ℕ) : ℕ :=\n  forceR 0 fun o0 =>\n{chain('H')}")
L.append(f"def decS (w {LU} {PS} : ℕ) : ℕ :=\n  forceR 0 fun o0 =>\n{chain('S')}")
XS = " ".join(f"x{nm(t)}" for t in ACT)
if os.environ.get("XFLAG"):
    L.append(f"def decX (w {LU} {XS} : ℕ) : ℕ :=\n  forceR 0 fun o0 =>\n{chain('X')}")
if KB:
    for t_ in ACT: L.append(f"def HL{nm(t_)} : ℕ := {lut(TAB[t_][0])}")
    L.append(f"def decL (w {LU} : ℕ) : ℕ :=\n  forceR 0 fun o0 =>\n{chain('L')}")
# sample: NLEAF consecutive minorant leaves from the middle of the walk order (siblings, like a real walk)
start = len(LV) // 2; sample = LV[start:start + NLEAF]; prev = {}; prevF = {}
for t_, (k, j1, j2, lam) in LV[start - 1][1]: prevF[t_] = ((k, j1, j2, lam), encF([(t_, (k, j1, j2, lam))]))
for t_, (k, j1, j2, lam) in LV[start - 1][1]: prev[t_] = symb(k, j1, j2)
stat = collections.Counter()
for i, (I, terms) in enumerate(sample):
    lu = " ".join(f"{I[PAIRS[t]][0]} {I[PAIRS[t]][1]}" for t in ACT)
    bF = encF(terms); bH = encH(terms); bS, same = encS(terms, prev)
    ps = " ".join(str(prev.get(t, 0)) for t in ACT)
    stat["F"] += len(bF); stat["H"] += len(bH); stat["S"] += len(bS); stat["same"] += same; stat["terms"] += len(terms)
    L.append(f"theorem f{i} : decF {hex(word(bF))} {lu} = {len(bF)} := by decide +kernel")
    L.append(f"theorem h{i} : decH {hex(word(bH))} {lu} = {len(bH)} := by decide +kernel")
    L.append(f"theorem s{i} : decS {hex(word(bS))} {lu} {ps} = {len(bS)} := by decide +kernel")
    if os.environ.get("XFLAG"):
        bX = []; xs = []
        for t_, (k, j1, j2, lam) in terms:
            s_ = symb(k, j1, j2); fb = encF([(t_, (k, j1, j2, lam))])
            pv = prevF.get(t_)
            if pv is not None and pv[0] == (k, j1, j2, lam): bX.append(1)
            else: bX.append(0); bX.extend(fb)
            xs.append(hex(word(pv[1])) if pv is not None else "0")
        L.append(f"theorem x{i} : decX {hex(word(bX))} {lu} {' '.join(xs)} = {len(bX)} := by decide +kernel")
        stat["X"] += len(bX)
        for t_, (k, j1, j2, lam) in terms: prevF[t_] = ((k, j1, j2, lam), encF([(t_, (k, j1, j2, lam))]))
    if KB: L.append(f"theorem l{i} : decL {hex(word(bH))} {lu} = {len(bH)} := by decide +kernel")
    for t_, (k, j1, j2, lam) in terms: prev[t_] = symb(k, j1, j2)
L.append(f"end AMW.Cert.{OUT}\n")
open(p, "w", encoding="utf-8").write("\n\n".join(L))
n = len(sample)
print(p, f"{n} leaves; term-payload bits per leaf: fixed {stat['F'] / n:.1f}, Huffman {stat['H'] / n:.1f}, "
      f"Huffman+same {stat['S'] / n:.1f}, fixed+same(full term) {stat['X'] / n:.1f} (same rate {stat['same'] / stat['terms']:.2f}); "
      f"table symbols {sum(len(TAB[t][0]) for t in ACT)}")
