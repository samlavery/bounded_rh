#!/usr/bin/env python3
"""(bridge-port) Per-node kernel cost of the polytope walk state (Q = 7: 14 gap bounds + 42 pair bounds) on the real
AMT8 trees: every AMT8 walk of ROOT/AMW/AMT8Data.lean is re-encoded in the polytope layout (split = 1 + 5-bit axis,
leaves copied verbatim, all pair bounds absent: A = 0, B = BIG) and run through PCellW8N{0,1,2} (0, 1, 2 rounds of bound
tightening per node, AMT8 box leaves); the original AMT8 walk is the baseline.  Writes ROOT/AMW/PCellW8B.lean.
Usage: bp_pcellw8.py ROOT"""
import sys, os, re
ROOT = sys.argv[1]
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW")
d = open(os.path.join(P, "AMT8Data.lean")).read(); inst = open(os.path.join(P, "AMT8Inst.lean")).read()
Q = 7; NC = 21; BIG = 1 << 40
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
    for v in range(3):
        thm.append(f"theorem n{v}_{nm} : AMW.Cert.PCellW8N{v}.walk TOP BK TOPD BKD PT3B REG {hex(nb)} {fuel} 1 {coords} {pb} = {ne} := by decide +kernel")
    for v, M in (("m0", 0), ("mf", (1 << NC) - 1)):
        thm.append(f"theorem {v}_{nm} : AMW.Cert.PCellW8M2.walk TOP BK TOPD BKD PT3B REG {hex(nb)} {fuel} 1 {coords} {pb} {M} = {ne} := by decide +kernel")
hdr = ("import AMW.PCellW8N0\nimport AMW.PCellW8N1\nimport AMW.PCellW8N2\nimport AMW.PCellW8M2\n\nset_option maxRecDepth 100000\n\nnoncomputable section\n\n"
       "namespace AMW.Cert.PCellW8B\n\nopen AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\n\n" + "\n".join(defs) + "\n\n")
open(os.path.join(P, "PCellW8B.lean"), "w").write(hdr + "\n\n".join(thm) + "\n\nend AMW.Cert.PCellW8B\n")
print(len(ws), "walks", tot)
