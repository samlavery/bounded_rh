#!/usr/bin/env bash
# int9q5.sh (bridge-port, 2026-10-11): ASSEMBLY of INT9Q5 = PC9QB5C (48 roots, RCUT 1:51168,1:39936; 5 walk cuts at 450;
# L3 PTD, L6 GSPL, QB 14) by CERTIFICATE-REGION SPLICE into INT9Q4.lean (which carries the hand-made master-of-puppets2
# window edits):
#  1. int9q4.sh steps 1-3 for PC9QB5C -> INT9Q5_noIns.lean (swap_cert9 into MOPX9_full.lean; its κ / final block unused);
#  2. check: outside the `-- SWAP BEGIN/END certificate` region, INT9Q5_noIns equals INT9Q4_noIns except the change-notice
#     weights line (same skeleton, same W9 / B / c, so the MoP2-edited final instantiation of INT9Q4 stays valid);
#  3. INT9Q5_pre.lean = INT9Q4.lean with its certificate region replaced by INT9Q5_noIns's region (generated text only).
# The header's certificate description is then updated BY HAND (Edit) in a copy, INT9Q5.lean.
set -eu
B=~/work/riemann-submission/bench; A=$B/arun; H=$A/cert/n9/root_PC9QB5C/AMW; R=$A/cert/n9/root9q5
for f in $H/PC9QB5CInst.lean $H/PC9QB5CData.lean; do test -s $f || { echo "missing $f"; exit 1; }; done
test ! -e $R && test ! -e $A/INT9Q5_full.lean && test ! -e $A/INT9Q5_noIns.lean && test ! -e $A/INT9Q5_pre.lean || { echo "outputs exist"; exit 1; }
mkdir -p $R/AMW
for f in $B/window/rootR8f/AMW/*.lean; do ln -s $f $R/AMW/$(basename $f); done
cp $H/PC9QB5CInst.lean $H/PC9QB5CData.lean $R/AMW/
python3 $B/window/tauint/assemble_am_tau9.py $A/INT9Q5_full.lean --root ../arun/cert/n9/root9q5 --roots PC9QB5CData,AMTail,Floor,Window \
  --final6 PC9QB5C --npts 9 | tail -1 | cut -c1-200
python3 $A/swap_cert9.py $A/MOPX9_full.lean $A/INT9Q5_full.lean PC9QB5C "t570 Q engine, ZEXT 32, lever 1, RCUT 1:51168,1:39936 (48 roots, 5 walk cuts at 450), limb walks LB 32768 (bridge-port), delta 5e-5" $A/INT9Q5_noIns.lean
python3 - <<PY
import re
def parts(p):
    L = open(p, encoding="utf-8").read().split("\n")
    b = next(i for i, l in enumerate(L) if l.startswith("-- SWAP BEGIN certificate"))
    e = next(i for i, l in enumerate(L) if l.startswith("-- SWAP END certificate"))
    return L[:b], L[b:e + 1], L[e + 1:]
p4, r4, s4 = parts("$A/INT9Q4_noIns.lean"); p5, r5, s5 = parts("$A/INT9Q5_noIns.lean")
d = [(i, a, b) for i, (a, b) in enumerate(zip(p4, p5)) if a != b] + [("suffix", a, b) for a, b in zip(s4, s5) if a != b]
assert len(p4) == len(p5) and len(s4) == len(s5), (len(p4), len(p5), len(s4), len(s5))
print("outside-region differences INT9Q4_noIns vs INT9Q5_noIns:", len(d))
for x in d: print("  ", str(x)[:240])
assert len(d) <= 2, "the skeleton outside the certificate region changed: inspect before splicing"
P4, R4, S4 = parts("$A/INT9Q4.lean")
out = "\n".join(P4 + r5 + S4)
open("$A/INT9Q5_pre.lean", "w", encoding="utf-8").write(out)
print("INT9Q5_pre.lean", len(out.encode()), "B; region", len("\n".join(r5).encode()), "B (INT9Q4 region", len("\n".join(R4).encode()), "B)")
PY
echo "== int9q5 assembly done $(date)"
