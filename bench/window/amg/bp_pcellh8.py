#!/usr/bin/env python3
"""(bridge-port) Kernel cost of the canonical-Huffman minorant leaf (HUFF.md) against the fixed-width kind-aware leaf and
AMT8's `mleafN`, on AMT8's own minorant leaves (as bp_pcellm8.py).  Each leaf's terms become symbols
`κ · 2^14 + j1 · 2^7 + j2` (position jj = 4 j + 64, which reproduces AMT8's gptG point), λ at LS = 1024 (LB = 10, so the
weights are AMT8's exactly; κ = 3 heavier tangent first); the per-pair canonical tables are built from the symbols of all
of AMT8's M leaves (huffenc's huff_lengths / canonical).  Writes the tables json (for genpcell3.py) and
ROOT/AMW/PCellH8B.lean (theorems a: mleafN, p: MODP's fixed-width mleafP, h: MODH's Huffman mleafP).
Usage: bp_pcellh8.py ROOT MODP MODH TABLES.json [NLEAF]   (env MODL: a second Huffman module, theorems l)"""
import sys, os, re, json, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "eight", "am8"))
from huffenc import huff_lengths, canonical, put_code, put_field

ROOT, MODP, MODH, TJ = sys.argv[1:5]
MODL = os.environ.get("MODL")          # optional: a second Huffman module (e.g. with the lookup), theorems l
NLEAF = int(sys.argv[5]) if len(sys.argv) > 5 else 60
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW")
d = open(os.path.join(P, "AMT8Data.lean")).read(); inst = open(os.path.join(P, "AMT8Inst.lean")).read()
Q = 7; NC = 21; BIG = 1 << 40; LS = 1024; LB = 10
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]
AL = [16291486, 0, 0, 100000000, 39006345, 100000000, 200000000, 32082429, 3747073, 59631729, 0, 121987310, 100000000,
      32723633, 96252927, 80736542, 0, 39006345, 37804904, 96252927, 59631729, 100000000, 32723633, 3747073, 0, 32082429, 0,
      16291486]
ACT = [t for t, a in zip(PAIRS, AL) if a > 0]
ND = len(re.findall(r"forceR \(Nat\.add o\d+ \(mlen k\d+\)\) fun o\d+", inst))
assert ND == len(ACT), (ND, len(ACT))
MLEN = {0: 2, 1: 6, 2: 16, 3: 20}
ws = re.findall(r"theorem (wk\d+) : (\S+)\.Covered ([\d ]+) :=\n  \S+\.covered_of_walk lbS lbD ptS hR (0x[0-9a-f]+|\d+) (\d+) ([\d ]+) (\d+) \(by decide \+kernel\) \(by decide\)", d)

def leaves_of(bits, box, fuel):
    out = []
    def go(pos, box, fuel):
        if fuel == 0: return 0
        w = bits >> pos
        if w & 1:
            ax = (w >> 1) & 7; m = (box[2 * ax] + box[2 * ax + 1]) >> 1
            A = list(box); A[2 * ax + 1] = m
            p = go(pos + 4, A, fuel - 1)
            if p == 0: return 0
            B = list(box); B[2 * ax] = m
            return go(p, B, fuel - 1)
        if box[2 * Q - 1] + 1 <= box[0] or (w >> 1) & 1 == 0: return pos + 2
        x = w >> 2; o = 0
        for _ in range(ND): o += MLEN[(x >> o) & 3]
        out.append((x & ((1 << o) - 1), tuple(box), o)); return pos + 2 + o
    go(1, list(box), fuel)
    return out

def fields(x):
    """AMT8 term fields -> (κ, j1, j2, λ) per active term, in the HUFF.md conventions"""
    o = 0; out = []
    for _ in range(ND):
        k = (x >> o) & 3; p = (x >> (o + 2)) & 15
        if k == 0: f = (0, 0, 0, 0)
        elif k == 1: f = (1, 4 * p + 64, 0, 0)
        elif k == 2:
            lam = (x >> (o + 6)) & 1023
            f = (0, 0, 0, 0) if lam == 0 else (2, 4 * p + 64, 0, lam)
        else:
            q = (x >> (o + 6)) & 15; lam = (x >> (o + 10)) & 1023; j1, j2 = 4 * p + 64, 4 * q + 64
            if lam > LS // 2: j1, j2, lam = j2, j1, LS - lam
            f = (1, j1, 0, 0) if lam == 0 else (3, j1, j2, lam)
        out.append(f); o += MLEN[k]
    return out

def sym(f): return f[0] * 16384 + f[1] * 128 + f[2]

allM = []
for (nm_, ns, cov, bits, fuel, coords, ln) in ws:
    allM += leaves_of(int(bits, 0), list(map(int, coords.split())), int(fuel))
cnt = collections.defaultdict(collections.Counter)
for x, box, o in allM:
    for t, f in zip(ACT, fields(x)): cnt[t][sym(f)] += 1
tabs = {t: canonical(huff_lengths(cnt[t])) for t in ACT}
axtab = canonical(huff_lengths({a: 1 for a in range(Q + NC)})); ctab = canonical(huff_lengths({c: 1 for c in range(NC)}))
T = dict(LS=LS, LB=LB, term_tables={f"{i},{j}": [[s, l] for s, l in tabs[(i, j)][0]] for (i, j) in ACT},
         axis_table=[[a, l] for a, l in axtab[0]], c_table=[[c, l] for c, l in ctab[0]],
         sum_constraints_in_rank_order=[f"{i},{j}" for (i, j) in SUMS])
json.dump(T, open(TJ, "w"), indent=1)

def huffword(x):
    b = []
    for t, f in zip(ACT, fields(x)):
        code, l = tabs[t][1][sym(f)]; put_code(b, code, l)
        if f[0] == 2: put_field(b, f[3], LB)
        if f[0] == 3: put_field(b, f[3] - 1, LB - 1)
    put_field(b, 0, 1)
    return sum(v << k for k, v in enumerate(b)), len(b)

def fixword(x):
    """the fixed-width layout of bp_pcellm8.py ([κ 2][j1 7][j2 7 if κ = 3][λ 10 if κ ≥ 2], the closing bit)"""
    o = 0; n = 0; y = 0
    def put(v, k):
        nonlocal y, n
        y |= (v & ((1 << k) - 1)) << n; n += k
    for _ in range(ND):
        k = (x >> o) & 3; p = (x >> (o + 2)) & 15
        if k == 0: put(0, 2)
        elif k == 1: put(1, 2); put(4 * p + 64, 7)
        elif k == 2: put(2, 2); put(4 * p + 64, 7); put((x >> (o + 6)) & 1023, 10)
        else: put(3, 2); put(4 * p + 64, 7); put(4 * ((x >> (o + 6)) & 15) + 64, 7); put((x >> (o + 10)) & 1023, 10)
        o += MLEN[k]
    return y, n + 1

pick = allM[::max(1, len(allM) // NLEAF)][:NLEAF]
defs = [blk for blk in re.split(r"\n(?=\S)", d) if blk.startswith("def ")]
thm = []; hb = fb = 0
for i, (x, box, o) in enumerate(pick):
    y, n = fixword(x); h, hn = huffword(x); hb += hn; fb += n
    st = ", ".join(map(str, box)) + ", " + ", ".join(["0", str(BIG)] * NC)
    thm.append(f"theorem a{i} : AMW.Cert.AMT8.mleafN TOP BK TOPD BKD PT3B REG {x} {' '.join(map(str, box))} = {o} := by decide +kernel")
    thm.append(f"theorem p{i} : AMW.Cert.{MODP}.mleafP TOP BK TOPD BKD PT3B REG {y} ⟨{st}, 0⟩ = {n} := by decide +kernel")
    thm.append(f"theorem h{i} : AMW.Cert.{MODH}.mleafP TOP BK TOPD BKD PT3B REG {h} ⟨{st}, 0⟩ = {hn} := by decide +kernel")
    if MODL: thm.append(f"theorem l{i} : AMW.Cert.{MODL}.mleafP TOP BK TOPD BKD PT3B REG {h} ⟨{st}, 0⟩ = {hn} := by decide +kernel")
hdr = (f"import AMW.{MODP}\nimport AMW.{MODH}\n" + (f"import AMW.{MODL}\n" if MODL else "") + f"\nset_option maxRecDepth 100000\n\nnoncomputable section\n\nnamespace AMW.Cert.PCellH8B\n\n"
       "open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\n\n" + "\n".join(defs) + "\n\n")
open(os.path.join(P, "PCellH8B.lean"), "w").write(hdr + "\n\n".join(thm) + "\n\nend AMW.Cert.PCellH8B\n")
ent = sum(len(tabs[t][0]) for t in ACT)
print(f"{len(allM)} M leaves; {len(pick)} sampled; table entries {ent}; payload bits per sampled leaf: fixed {fb / len(pick):.1f}, "
      f"Huffman {hb / len(pick):.1f} (in-sample tables, LB = {LB})")
