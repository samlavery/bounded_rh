#!/usr/bin/env bash
# √-tail (window-scope's BrSqrtWS) compile test on PC8CF (rootR8f), private record 6734812/10^7 (< κ 6734824, which
# ties the board): TEST ONLY, never staged or uploaded.  Build + replay, Dep, safecut, size.
set -e
cd ~/work/riemann-submission/bench
T=window/tauint; C=CandPC8CFwsT; ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt)
bash pyr/private_check_rec.sh $T/PC8CFwsT.lean $C 6734824 10000000 6734812 10000000 specroot_pc8cfwst
grep -q "BUILD EXIT 0" specroot_pc8cfwst/build_$C.log
sed "s/^import CandAT7c\$/import $C/; s/getModuleIdx? \`CandAT7c /getModuleIdx? \`$C /; s/\"deps_at7c.tsv\"/\"deps_PC8CFws.tsv\"/" \
  window/bbaudit/DepAT7c.lean > $T/Dep_PC8CFws.lean
(cd $T && env LEAN_PATH="$HOME/work/riemann-submission/bench/specroot_pc8cfwst:$ZP" LEAN_NUM_THREADS=2 nice -n 10 \
   ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean Dep_PC8CFws.lean)
python3 window/bbaudit/safecut.py $T/PC8CFwsT.lean $T/deps_PC8CFws.tsv $T/PC8CFwsTS.lean
echo "SIZE PC8CFwsTS.lean $(wc -c < $T/PC8CFwsTS.lean | tr -d ' ') B"
