#!/usr/bin/env bash
# n = 8 τ pipeline (track 1): assemble the R8 layer + AMW.BrTau + the band-profile module + bridge-port's eight-point
# certificate NAME (rootR8) with the τ = 8/7 tail, build once (private check) for the dead set, safecut, private check
# of the stripped file, stage.
# Usage: run_n8.sh NAME PROFMOD KNUM KDEN RNUM RDEN CSRC [ROOT] [TAG]   (record RNUM/RDEN read from the board at check
#   time; CSRC: a text file with the certificate's credit lines for the header, written by the certificate's authors;
#   ROOT: the layer root under bench/window, default rootR8 (rootR8f: typh's engine, credited by provenance);
#   TAG: suffix for the output files and spec roots of a rerun or variant (outputs ${NAME}${TAG}T.lean, ...TS.lean))
#   env SQRTMOD=BrSqrtWS: the √ band tail (window-scope's AMW.BrSqrtWS; m optimised for Φ_g, no cap) instead of τ-linear
#   env EDGE=E4,E5,E6 EDGEMODS=BrEdgeA,…: edge-window certificates (each E's Inst/Data) and the edge Lean chain
set -e
NAME=$1; PROF=$2; KN=$3; KD=$4; RN=$5; RD=$6; CSRC=$(cd "$(dirname "$7")" && pwd)/$(basename "$7")
ROOT=${8:-rootR8}; OUT=$NAME${9:-}; lc=$(echo "$OUT" | tr A-Z a-z)
test -d ~/work/riemann-submission/bench/window/$ROOT/AMW || { echo "no root $ROOT"; exit 1; }
test -s "$CSRC" || { echo "credit file $CSRC missing or empty"; exit 1; }
cd ~/work/riemann-submission/bench
T=window/tauint; C=Cand${OUT}T; CS=Cand${OUT}TS
for r in specroot_${lc}t specroot_${lc}ts; do test ! -e $r || { echo "root $r exists"; exit 1; }; done
for f in $T/${OUT}T.lean $T/${OUT}TS.lean $T/deps_${OUT}.tsv; do test ! -e $f || { echo "$f exists"; exit 1; }; done
ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt)
SQ=${SQRTMOD:+--sqrt --sqrtmod $SQRTMOD}
EDATA=""; for e in $(echo "${EDGE:-}" | tr , ' '); do EDATA="$EDATA,${e}Data"; done
EG=${EDGE:+--edge $EDGE --edgemods ${EDGEMODS:-}}
python3 $T/assemble_am_tau.py $T/${OUT}T.lean --root $ROOT --roots AMTail,BrTau,$PROF${SQRTMOD:+,$SQRTMOD}${EDGEMODS:+,$EDGEMODS},${NAME}Data$EDATA --final6 $NAME --npts 8 --tau $SQ $EG --kappa $KN/$KD --profmod $PROF --csrc "$CSRC"
bash pyr/private_check_rec.sh $T/${OUT}T.lean $C $KN $KD $RN $RD specroot_${lc}t
grep -q "BUILD EXIT 0" specroot_${lc}t/build_$C.log
sed "s/^import CandAT7c\$/import $C/; s/getModuleIdx? \`CandAT7c /getModuleIdx? \`$C /; s/\"deps_at7c.tsv\"/\"deps_${OUT}.tsv\"/" \
  window/bbaudit/DepAT7c.lean > $T/Dep_${OUT}.lean
(cd $T && env LEAN_PATH="$HOME/work/riemann-submission/bench/specroot_${lc}t:$ZP" LEAN_NUM_THREADS=2 nice -n 10 \
   ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean Dep_${OUT}.lean)
python3 window/bbaudit/safecut.py $T/${OUT}T.lean $T/deps_${OUT}.tsv $T/${OUT}TS.lean
SZ=$(wc -c < $T/${OUT}TS.lean | tr -d ' ')
echo "SIZE ${OUT}TS.lean $SZ B (watch 1900000, cap 2000000)"
[ "$SZ" -le 2000000 ] || { echo "SIZE OVER CAP: stop"; exit 1; }
[ "$SZ" -le 1900000 ] || echo "SIZE WARN: ${OUT}TS.lean over 1.90 MB, tell the lead"
bash pyr/private_check_rec.sh $T/${OUT}TS.lean $CS $KN $KD $RN $RD specroot_${lc}ts
grep -q "BUILD EXIT 0" specroot_${lc}ts/build_$CS.log
echo "== stage"
bash nanoda/stage.sh $CS $PWD/specroot_${lc}ts
