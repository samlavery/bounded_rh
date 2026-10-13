#!/usr/bin/env bash
# int9.sh: the 9-point integration test (am-cert, 2026-10-10). NOT an upload candidate (over the 2 MB cap).
# handoff (bridge-port): cert/n9/handoff/PC9L{Inst,Data}.lean + DATA json
#  1. root9i/AMW: symlinks to rootR8f/AMW/*.lean, the handoff modules copied in
#  2. assemble_am_tau9.py --final6 PC9L --npts 9 (FULL: the certificate text and RiemannFail W9 … cert_AM)
#  3. swap_cert9.py into MOPX9_full.lean (the unstripped n-generic base), PCBias inserted before the region
#  4. private check (spec candidate 66779299/99140823, record 66812491/99194876) in specroot_int9, then the stages
set -eu
B=~/work/riemann-submission/bench; A=$B/arun; H=$A/cert/n9/handoff; R=$A/cert/n9/root9i
for f in $H/PC9LInst.lean $H/PC9LData.lean; do test -s $f || { echo "missing $f"; exit 1; }; done
test ! -e $R && test ! -e $B/specroot_int9 && test ! -e $A/INT9_full.lean && test ! -e $A/INT9.lean || { echo "outputs exist"; exit 1; }
mkdir -p $R/AMW
for f in $B/window/rootR8f/AMW/*.lean; do ln -s $f $R/AMW/$(basename $f); done
rm -f $R/AMW/PC9LInst.lean $R/AMW/PC9LData.lean
cp $H/PC9LInst.lean $H/PC9LData.lean $R/AMW/
python3 $B/window/tauint/assemble_am_tau9.py $A/INT9_full.lean --root ../arun/cert/n9/root9i --roots PC9LData,AMTail,Floor,Window \
  --final6 PC9L --npts 9
python3 $A/swap_cert9.py $A/MOPX9_full.lean $A/INT9_full.lean PC9L "window-scope lp9 (cert9_final), delta 2e-4; integration test" $A/INT9_noBias.lean
python3 - <<PY
import re
t = open("$A/INT9_noBias.lean", encoding="utf-8").read()
pb = open("$B/window/rootR8f/AMW/PCBias.lean", encoding="utf-8").read()
pb = re.sub(r"^import .*\n", "", pb, flags=re.M)
k = t.index("-- SWAP BEGIN certificate")
open("$A/INT9.lean", "w", encoding="utf-8").write(t[:k] + "\nsection\n" + pb + "\nend\nend\n" + t[k:])
print("INT9.lean", len(open("$A/INT9.lean", encoding="utf-8").read().encode()), "B")
PY
cd $B
bash pyr/private_check_rec.sh arun/INT9.lean CandINT9 66779299 99140823 66812491 99194876 specroot_int9
grep -q "BUILD EXIT 0" specroot_int9/build_CandINT9.log && bash nanoda/stage.sh CandINT9 $PWD/specroot_int9 && rm -f nanoda/exp_CandINT9.ndjson
echo "== int9 done $(date)"
