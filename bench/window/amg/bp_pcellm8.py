#!/usr/bin/env python3
"""(bridge-port) Kernel cost of the polytope minorant leaf (`mleafP`, Q = 7) against AMT8's `mleafN`, on AMT8's own minorant
leaves: each leaf's payload is re-encoded in the polytope term layout ([κ 2][j1 7][j2 7 if κ = 3][λ 10 if κ ≥ 2], position
jj = 4 j + 64: the fine grid 2^5 at j/8 = 4j/32 reproduces AMT8's gptG point exactly; no multipliers), on its box with every
pair bound absent.  The tables are AMT8's values (timing only).  Writes ROOT/AMW/PCellM8B.lean.
Usage: bp_pcellm8.py ROOT MODULE [NLEAF]"""
import sys, os, re
ROOT, MOD = sys.argv[1], sys.argv[2]
MOD2 = os.environ.get("MOD2")
NLEAF = int(sys.argv[3]) if len(sys.argv) > 3 else 60
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW")
d = open(os.path.join(P, "AMT8Data.lean")).read(); inst = open(os.path.join(P, "AMT8Inst.lean")).read()
Q = 7; NC = 21; BIG = 1 << 40
ND = len(re.findall(r"forceR \(Nat\.add o\d+ \(mlen k\d+\)\) fun o\d+", inst))
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

def recode(x):
    """AMT8 term fields -> the polytope layout; returns (payload, length incl. the closing multiplier bit)"""
    o = 0; n = 0; y = 0
    def put(v, k):
        nonlocal y, n
        y |= (v & ((1 << k) - 1)) << n; n += k
    for _ in range(ND):
        k = (x >> o) & 3
        p = (x >> (o + 2)) & 15
        if k == 0: put(0, 2)
        elif k == 1: put(1, 2); put(4 * p + 64, 7)
        elif k == 2: put(2, 2); put(4 * p + 64, 7); put((x >> (o + 6)) & 1023, 10)
        else: put(3, 2); put(4 * p + 64, 7); put(4 * ((x >> (o + 6)) & 15) + 64, 7); put((x >> (o + 10)) & 1023, 10)
        o += MLEN[k]
    n += 1       # the closing bit of the (empty) multiplier list
    return y, n

allM = []
for (nm, ns, cov, bits, fuel, coords, ln) in ws:
    allM += leaves_of(int(bits, 0), list(map(int, coords.split())), int(fuel))
pick = allM[::max(1, len(allM) // NLEAF)][:NLEAF]
defs = [blk for blk in re.split(r"\n(?=\S)", d) if blk.startswith("def ")]
thm = []
for i, (x, box, o) in enumerate(pick):
    y, n = recode(x)
    st = ", ".join(map(str, box)) + ", " + ", ".join(["0", str(BIG)] * NC)
    thm.append(f"theorem a{i} : AMW.Cert.AMT8.mleafN TOP BK TOPD BKD PT3B REG {x} {' '.join(map(str, box))} = {o} := by decide +kernel")
    thm.append(f"theorem p{i} : AMW.Cert.{MOD}.mleafP TOP BK TOPD BKD PT3B REG {y} ⟨{st}, 0⟩ = {n} := by decide +kernel")
    if MOD2: thm.append(f"theorem q{i} : AMW.Cert.{MOD2}.mleafP TOP BK TOPD BKD PT3B REG {y} ⟨{st}, 0⟩ = {n} := by decide +kernel")
hdr = (f"import AMW.{MOD}\n" + (f"import AMW.{MOD2}\n" if MOD2 else "") + "\nset_option maxRecDepth 100000\n\nnoncomputable section\n\nnamespace AMW.Cert.PCellM8B\n\n"
       "open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\n\n" + "\n".join(defs) + "\n\n")
open(os.path.join(P, "PCellM8B.lean"), "w").write(hdr + "\n\n".join(thm) + "\n\nend AMW.Cert.PCellM8B\n")
print(len(allM), "M leaves;", len(pick), "sampled")
