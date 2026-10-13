"""Walk-chunk kernel bench (diagnostic): re-check every walk chunk of a certificate data module, one theorem per chunk,
and decode each chunk's leaf composition (zero-order / slope / centre / minorant / reflected) from its bits.
Usage: mkwalkbench.py ROOT NAME  -> ROOT/AMW/{NAME}WB.lean, amg/{NAME}_wb_comp.json"""
import sys, os, re, json
ROOT, NAME = sys.argv[1], sys.argv[2]
P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW")
if not os.path.isdir(P): P = os.path.join(os.path.dirname(os.path.abspath(__file__)), ROOT, "AMW")
d = open(os.path.join(P, f"{NAME}Data.lean")).read()
ws = re.findall(r"theorem (wk\d+) : (\S+)\.Covered ([\d ]+) :=\n  \S+\.covered_of_walk \(C := CEN\) lbS lbD ptS hR (0x[0-9a-f]+|\d+) (\d+) ([\d ]+) (\d+) \(by decide \+kernel\) \(by decide\)", d)
Q = 6; NP = 21
def decode(bits, box):
    pos = [1]; comp = dict(Z=0, S=0, C=0, M=0, R=0)
    def bit():
        b = (bits >> pos[0]) & 1; pos[0] += 1; return b
    def rd(n):
        v = (bits >> pos[0]) & ((1 << n) - 1); pos[0] += n; return v
    def node(box):
        if bit():
            ax = rd(3); m = (box[ax][0] + box[ax][1]) // 2
            A = list(box); A[ax] = (box[ax][0], m); B = list(box); B[ax] = (m, box[ax][1])
            node(A); node(B); return
        if box[0][0] > box[Q - 1][1]: pos[0] += 2; comp['R'] += 1; return
        kind = rd(2)
        if kind == 0: comp['Z'] += 1
        elif kind == 1:
            rd(12); f = bit(); comp['S'] += 1
            if not f: rd(NP)
        elif kind == 3:
            rd(8); f = bit(); comp['C'] += 1
            if not f: rd(NP)
        else:
            comp['M'] += 1
            for t in range(NP):
                k = rd(2)
                if k >= 1: rd(4)
                if k == 3: rd(4)
                if k >= 2: rd(10)
    node(box); return comp, pos[0]
out = []; thm = []
for (nm, ns, cov, bits, fuel, coords, ln) in ws:
    b = int(bits, 0); c = list(map(int, coords.split())); box = [(c[2 * r], c[2 * r + 1]) for r in range(Q)]
    comp, L = decode(b, box); assert L == int(ln), (nm, L, ln)
    out.append(dict(name=nm, **comp))
    thm.append(f"theorem b{nm} : {ns}.Covered {cov}:=\n  {ns}.covered_of_walk (C := CEN) lbS lbD ptS hR {bits} {fuel} {coords} {ln} (by decide +kernel) (by decide)")
hdr = f"import AMW.{NAME}Data\n\nset_option maxRecDepth 100000\nset_option trace.profiler true\nset_option trace.profiler.threshold 200\n\nnamespace AMW.Cert.{NAME}Data\n\nopen AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\n\n"
open(os.path.join(P, f"{NAME}WB.lean"), "w").write(hdr + "\n\n".join(thm) + f"\n\nend AMW.Cert.{NAME}Data\n")
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f"{NAME}_{ROOT}_wb_comp.json"), "w"))
tot = {k: sum(o[k] for o in out) for k in 'ZSCMR'}
print(len(out), "chunks", tot)
