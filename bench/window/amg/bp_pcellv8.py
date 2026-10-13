#!/usr/bin/env python3
"""(bridge-port) [byte-lean layout, genpcell2] Per-node kernel cost of the polytope walk state (Q = 7: 14 gap bounds + 42 pair bounds) on the real
AMT8 trees: every AMT8 walk of ROOT/AMW/AMT8Data.lean is re-encoded in the polytope layout (split = 1 + 5-bit axis,
leaves copied verbatim, all pair bounds absent: A = 0, B = BIG) and run through PCellV8N{0,1,2} (0, 1, 2 rounds of bound
tightening per node, AMT8 box leaves); the original AMT8 walk is the baseline.  Writes ROOT/AMW/PCellV8B.lean.
Usage: bp_pcellw8.py ROOT"""
import sys, os, re
ROOT = sys.argv[1]
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW")
d = open(os.path.join(P, "AMT8Data.lean")).read(); inst = open(os.path.join(P, "AMT8Inst.lean")).read()
Q = 7; NC = 21; BIG = 1 << 40
# active-constraint masks: A pairs spread over the 21 (their bounds absent, so the passes run in full but change nothing)
MASKS = [(A, sum(1 << (round(i * (NC - 1) / max(1, A - 1)) if A > 1 else 0) for i in range(A))) for A in (0, 1, 2, 4, 8)]
ND = len(re.findall(r"forceR \(Nat\.add o\d+ \(mlen k\d+\)\) fun o\d+", inst))
MLEN = {0: 2, 1: 6, 2: 16, 3: 20}
ws = re.findall(r"theorem (wk\d+) : (\S+)\.Covered ([\d ]+) :=\n  \S+\.covered_of_walk lbS lbD ptS hR (0x[0-9a-f]+|\d+) (\d+) ([\d ]+) (\d+) \(by decide \+kernel\) \(by decide\)", d)

def recode(bits, box, fuel):
    """the node sequence of the AMT8 walk, re-encoded: returns (new bits, new end, nodes, leaves)"""
    out = [bits & 1]; st = dict(n=0, lv=0)
    def put(v, n):
        for i in range(n): out.append((v >> i) & 1)
    def go(pos, box, fuel):
        if fuel == 0: return 0
        w = bits >> pos; st['n'] += 1
        if w & 1:
            ax = (w >> 1) & 7; m = (box[2 * ax] + box[2 * ax + 1]) >> 1
            put(1 | (ax << 1), 6)
            A = list(box); A[2 * ax + 1] = m
            p = go(pos + 4, A, fuel - 1)
            if p == 0: return 0
            B = list(box); B[2 * ax] = m
            return go(p, B, fuel - 1)
        st['lv'] += 1
        if box[2 * Q - 1] + 1 <= box[0]: n = 2
        elif (w >> 1) & 1 == 0: n = 2
        else:
            x = w >> 2; o = 0
            for _ in range(ND): o += MLEN[(x >> o) & 3]
            n = 2 + o
        put(w & ((1 << n) - 1), n)
        return pos + n
    e = go(1, list(box), fuel)
    nb = sum(b << i for i, b in enumerate(out))
    return nb, len(out), st['n'], st['lv'], e

defs = [blk for blk in re.split(r"\n(?=\S)", d) if blk.startswith("def ")]
thm = []; tot = dict(n=0, lv=0, ob=0, nb=0)
for (nm, ns, cov, bits, fuel, coords, ln) in ws:
    b = int(bits, 0)
    nb, ne, nn, nl, e = recode(b, list(map(int, coords.split())), int(fuel)); assert e == int(ln), (nm, e, ln)
    tot['n'] += nn; tot['lv'] += nl; tot['ob'] += int(ln); tot['nb'] += ne
    pb = " ".join(["0", str(BIG)] * NC)
    thm.append(f"theorem a_{nm} : AMW.Cert.AMT8.walk TOP BK TOPD BKD PT3B REG {bits} {fuel} 1 {coords} = {ln} := by decide +kernel")
    thm.append(f"theorem n0a0_{nm} : AMW.Cert.PCellV8N0.walk TOP BK TOPD BKD PT3B REG {hex(nb)} {fuel} 1 {coords} {pb} 0 = {ne} := by decide +kernel")
    for v in (1, 2):
        for A, mask in MASKS:
            thm.append(f"theorem n{v}a{A}_{nm} : AMW.Cert.PCellV8N{v}.walk TOP BK TOPD BKD PT3B REG {hex(nb)} {fuel} 1 {coords} {pb} {mask} = {ne} := by decide +kernel")
hdr = ("import AMW.PCellV8N0\nimport AMW.PCellV8N1\nimport AMW.PCellV8N2\n\nset_option maxRecDepth 100000\n\nnoncomputable section\n\n"
       "namespace AMW.Cert.PCellV8B\n\nopen AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\n\n" + "\n".join(defs) + "\n\n")
open(os.path.join(P, "PCellV8B.lean"), "w").write(hdr + "\n\n".join(thm) + "\n\nend AMW.Cert.PCellV8B\n")
print(len(ws), "walks", tot)
