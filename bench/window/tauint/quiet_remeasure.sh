#!/usr/bin/env bash
# quiet_remeasure.sh OUT KNUM KDEN RNUM RDEN : re-measure an already-checked stripped file ${OUT}TS.lean on a quiet
# machine: the private check (build + replay) into a fresh spec root specroot_${out}tsq as module Cand${OUT}TSq, then
# the staging (export, nanoda, closure replay); prints load before each stage and the conservative projection
# 157 + 2·build + 2.46·(export + nanoda + closure).
set -e
OUT=$1; KN=$2; KD=$3; RN=$4; RD=$5; lc=$(echo "$OUT" | tr A-Z a-z)
cd ~/work/riemann-submission/bench
T=window/tauint; M=Cand${OUT}TSq; R=specroot_${lc}tsq
test ! -e $R || { echo "root $R exists"; exit 1; }
echo "== quiet re-measure of $T/${OUT}TS.lean, load $(uptime | sed 's/.*averages: //')"
bash pyr/private_check_rec.sh $T/${OUT}TS.lean $M $KN $KD $RN $RD $R
grep -q "BUILD EXIT 0" $R/build_$M.log
echo "== stage, load $(uptime | sed 's/.*averages: //')"
bash nanoda/stage.sh $M $PWD/$R
echo "== done, load $(uptime | sed 's/.*averages: //')"
b=$(awk '/ real /{t=$1} END{print t}' $R/build_$M.log)
e=$(awk '/ real /{t=$1} END{print t}' nanoda/export_$M.err)
n=$(awk '/ real /{t=$1} END{print t}' nanoda/nanoda_$M.err)
c=$(awk '/ real /{t=$1} END{print t}' nanoda/replayx_$M.err)
python3 -c "b,e,n,c=$b,$e,$n,$c; print(f'build {b} export {e} nanoda {n} closure {c}; conservative {157+2*b+2.46*(e+n+c):.1f} s')"
