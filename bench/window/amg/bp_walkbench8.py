#!/usr/bin/env python3
"""(bridge-port) Walk and leaf kernel bench for an eight-point (Q = 7) data module with zero-order and minorant leaves
(the AMT8 layout: leaf bit 1 = kind; a minorant leaf's payload is Σ mlen(k_t) over its data terms).
Writes ROOT/AMW/{NAME}BP.lean: one theorem per walk (as in the data module), and one theorem per sampled leaf
(`leafOK … = true`, `mleafN … = n`).  Prints the leaf composition per walk to amg/{NAME}_{ROOT}_bp.json.
Usage: bp_walkbench8.py ROOT NAME [NLEAF]"""
import sys, os, re, json
ROOT, NAME = sys.argv[1], sys.argv[2]
NLEAF = int(sys.argv[3]) if len(sys.argv) > 3 else 60
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW")
d = open(os.path.join(P, f"{NAME}Data.lean")).read()
inst = open(os.path.join(P, f"{NAME}Inst.lean")).read()
Q = 7
ND = len(re.findall(r"forceR \(Nat\.add o\d+ \(mlen k\d+\)\) fun o\d+", inst))   # data terms of a minorant leaf
MLEN = {0: 2, 1: 6, 2: 16, 3: 20}
ws = re.findall(r"theorem (wk\d+) : (\S+)\.Covered ([\d ]+) :=\n  \S+\.covered_of_walk lbS lbD ptS hR (0x[0-9a-f]+|\d+) (\d+) ([\d ]+) (\d+) \(by decide \+kernel\) \(by decide\)", d)


def decode(bits, box, fuel):
    comp = dict(Z=0, M=0, R=0); leaves = []

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
        if box[2 * Q - 1] + 1 <= box[0]: comp['R'] += 1; return pos + 2
        if (w >> 1) & 1 == 0:
            comp['Z'] += 1; leaves.append(('Z', 0, tuple(box), 0)); return pos + 2
        x = w >> 2; o = 0
        for _ in range(ND):
            k = (x >> o) & 3; o += MLEN[k]
        comp['M'] += 1; leaves.append(('M', x & ((1 << o) - 1), tuple(box), o)); return pos + 2 + o
    e = go(1, list(box), fuel)
    return comp, e, leaves


out = []; thm = []; allleaves = []
for (nm, ns, cov, bits, fuel, coords, ln) in ws:
    b = int(bits, 0); c = list(map(int, coords.split()))
    comp, e, lv = decode(b, c, int(fuel)); assert e == int(ln), (nm, e, ln)
    out.append(dict(name=nm, **comp)); allleaves += lv
    thm.append(f"theorem b{nm} : {ns}.walk TOP BK TOPD BKD PT3B REG {bits} {fuel} 1 {coords} = {ln} := by decide +kernel")
Z = [l for l in allleaves if l[0] == 'Z']; M = [l for l in allleaves if l[0] == 'M']
pick = lambda L: L[::max(1, len(L) // NLEAF)][:NLEAF]
for i, (k, w, box, n) in enumerate(pick(Z)):
    thm.append(f"theorem z{i} : {NAME}.leafOK TOP BK {' '.join(map(str, box))} = true := by decide +kernel")
for i, (k, w, box, n) in enumerate(pick(M)):
    thm.append(f"theorem m{i} : {NAME}.mleafN TOP BK TOPD BKD PT3B REG {w} {' '.join(map(str, box))} = {n} := by decide +kernel")
# the data definitions only (no table checks: the tables need not verify on this root's kernel for a timing run)
defs = []
for blk in re.split(r"\n(?=\S)", d):
    if blk.startswith("def "): defs.append(blk)
hdr = (f"import AMW.{NAME}Inst\n\nset_option maxRecDepth 100000\n\nnoncomputable section\n\nnamespace AMW.Cert.{NAME}BPD\n\n"
       f"open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\n\n" + "\n".join(defs) + "\n\n")
open(os.path.join(P, f"{NAME}BP.lean"), "w").write(hdr + "\n\n".join(thm) + f"\n\nend AMW.Cert.{NAME}BPD\n")
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f"{NAME}_{ROOT}_bp.json"), "w"))
print(len(out), "walks", {k: sum(o[k] for o in out) for k in 'ZMR'}, "data terms", ND, "sampled", len(pick(Z)), len(pick(M)))
