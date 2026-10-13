#!/usr/bin/env bash
# int9q4.sh (bridge-port, 2026-10-11): ASSEMBLY ONLY of INT9Q4 = the 9-point certificate PC9QB4 (PZ32R1 tree: RCUT 1:51168,
# 10,077 leaves; RCOMP root layout; LB 32768 / WIN 480 limb walks; L5 dprune; L2 point tree PTREE 3) in the n-generic
# skeleton MOPX9_full.lean, as int9q.sh steps 1-4 (PCellPT comes with the swap region; inserting it too duplicated it).
# Output: INT9Q4_pre.lean (old-H_W κ from swap_cert9.py). The master-of-puppets2 window edits are then made BY HAND
# (Edit) on a copy, INT9Q4.lean; the private check, the reachability strip and the stages are separate steps.
set -eu
B=~/work/riemann-submission/bench; A=$B/arun; H=$A/cert/n9/root_PC9QB4/AMW; R=$A/cert/n9/root9q4
for f in $H/PC9QB4Inst.lean $H/PC9QB4Data.lean; do test -s $f || { echo "missing $f"; exit 1; }; done
test ! -e $R && test ! -e $A/INT9Q4_full.lean && test ! -e $A/INT9Q4_noIns.lean && test ! -e $A/INT9Q4_pre.lean || { echo "outputs exist"; exit 1; }
mkdir -p $R/AMW
for f in $B/window/rootR8f/AMW/*.lean; do ln -s $f $R/AMW/$(basename $f); done
cp $H/PC9QB4Inst.lean $H/PC9QB4Data.lean $R/AMW/
python3 $B/window/tauint/assemble_am_tau9.py $A/INT9Q4_full.lean --root ../arun/cert/n9/root9q4 --roots PC9QB4Data,AMTail,Floor,Window \
  --final6 PC9QB4 --npts 9
python3 $A/swap_cert9.py $A/MOPX9_full.lean $A/INT9Q4_full.lean PC9QB4 "t570 Q engine, ZEXT 32, lever 1, RCUT 1:51168 (32 roots), limb walks LB 32768 (bridge-port), delta 5e-5" $A/INT9Q4_noIns.lean
python3 - <<PY
import re
t = open("$A/INT9Q4_noIns.lean", encoding="utf-8").read()
ins = ""
for m in ("PCBias", "PCellIV"):   # (16:19 fix) PCellPT is NOT inserted: the swap region already carries it (Inst < PCellPT < Data)
    s = re.sub(r"^import .*\n", "", open("$B/window/rootR8f/AMW/" + m + ".lean", encoding="utf-8").read(), flags=re.M)
    ls_ = [l.strip() for l in s.split("\n")]
    bal = sum(1 for l in ls_ if re.match(r"^(noncomputable )?section\b", l)) - sum(1 for l in ls_ if l == "end")
    assert bal >= 0, (m, bal)
    ins += "\nsection\n" + s + "\n" + "end\n" * (bal + 1)      # close the module's open sections, then the wrapper
k = t.index("-- SWAP BEGIN certificate")
open("$A/INT9Q4_pre.lean", "w", encoding="utf-8").write(t[:k] + ins + t[k:])
print("INT9Q4_pre.lean", len(open("$A/INT9Q4_pre.lean", encoding="utf-8").read().encode()), "B")
PY
echo "== int9q4 assembly done $(date)"
