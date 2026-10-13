#!/usr/bin/env bash
# int9q.sh (bridge-port, 2026-10-11): am-cert's int9.sh for the 9-point certificate PC9QB (t570, Q engine, ZEXT 32, lever 1,
# limb walks; cert/n9/root_PC9QB).  NOT an upload candidate unless it fits; this is the measured end-to-end baseline.
#  1. root9q/AMW: symlinks to rootR8f/AMW/*.lean, PC9QB{Inst,Data}.lean copied in
#  2. assemble_am_tau9.py --final6 PC9QB --npts 9 (FULL: the certificate text and RiemannFail W9 … cert_AM)
#  3. swap_cert9.py into MOPX9_full.lean (the unstripped n-generic base)
#  4. PCBias and PCellIV (the lever-1 engine module; imports stripped) inserted before the certificate region
#  5. private check (candidate 66780167/99143618 = (67216841 - 436674)/(1e8 - 856382); record = the current #1
#     167031227639218487/247987190000000000) in specroot_int9q, then the stages
set -eu
B=~/work/riemann-submission/bench; A=$B/arun; H=$A/cert/n9/root_PC9QB/AMW; R=$A/cert/n9/root9q
for f in $H/PC9QBInst.lean $H/PC9QBData.lean; do test -s $f || { echo "missing $f"; exit 1; }; done
test ! -e $R && test ! -e $B/specroot_int9q && test ! -e $A/INT9Q_full.lean && test ! -e $A/INT9Q.lean || { echo "outputs exist"; exit 1; }
mkdir -p $R/AMW
for f in $B/window/rootR8f/AMW/*.lean; do ln -s $f $R/AMW/$(basename $f); done
cp $H/PC9QBInst.lean $H/PC9QBData.lean $R/AMW/
python3 $B/window/tauint/assemble_am_tau9.py $A/INT9Q_full.lean --root ../arun/cert/n9/root9q --roots PC9QBData,AMTail,Floor,Window \
  --final6 PC9QB --npts 9
python3 $A/swap_cert9.py $A/MOPX9_full.lean $A/INT9Q_full.lean PC9QB "t570 Q engine, ZEXT 32, lever 1, limb walks (bridge-port), delta 5e-5; integration test" $A/INT9Q_noIns.lean
python3 - <<PY
import re
t = open("$A/INT9Q_noIns.lean", encoding="utf-8").read()
ins = ""
for m in ("PCBias", "PCellIV"):
    s = re.sub(r"^import .*\n", "", open("$B/window/rootR8f/AMW/" + m + ".lean", encoding="utf-8").read(), flags=re.M)
    ls_ = [l.strip() for l in s.split("\n")]
    bal = sum(1 for l in ls_ if re.match(r"^(noncomputable )?section\b", l)) - sum(1 for l in ls_ if l == "end")
    assert bal >= 0, (m, bal)
    ins += "\nsection\n" + s + "\n" + "end\n" * (bal + 1)      # close the module's open sections, then the wrapper
k = t.index("-- SWAP BEGIN certificate")
open("$A/INT9Q.lean", "w", encoding="utf-8").write(t[:k] + ins + t[k:])
print("INT9Q.lean", len(open("$A/INT9Q.lean", encoding="utf-8").read().encode()), "B")
PY
cd $B
bash pyr/private_check_rec.sh arun/INT9Q.lean CandINT9Q 66780167 99143618 167031227639218487 247987190000000000 specroot_int9q
grep -q "BUILD EXIT 0" specroot_int9q/build_CandINT9Q.log && bash nanoda/stage.sh CandINT9Q $PWD/specroot_int9q && rm -f nanoda/exp_CandINT9Q.ndjson
echo "== int9q done $(date)"
