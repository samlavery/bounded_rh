#!/usr/bin/env bash
# AT7T pipeline (track 1): assemble with the band-profile proof, build once (private check, record 6734302/10^7) to get
# the dead set from the compiled olean, safecut, private check of the stripped file, stage.  Usage: run_at7t.sh PROFILE.lean
set -e
cd ~/work/riemann-submission/bench
T=window/tauint
ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt)
python3 $T/assemble_at7t.py "$1" $T/AT7T.lean
bash pyr/private_check_rec.sh $T/AT7T.lean CandAT7T 6734383 10000000 6734302 10000000 specroot_at7t
grep -q "BUILD EXIT 0" specroot_at7t/build_CandAT7T.log
(cd $T && env LEAN_PATH="$HOME/work/riemann-submission/bench/specroot_at7t:$ZP" LEAN_NUM_THREADS=2 nice -n 10 \
   ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean DepAT7T.lean)
python3 window/bbaudit/safecut.py $T/AT7T.lean $T/deps_at7t.tsv $T/AT7TS.lean
bash pyr/private_check_rec.sh $T/AT7TS.lean CandAT7TS 6734383 10000000 6734302 10000000 specroot_at7ts
grep -q "BUILD EXIT 0" specroot_at7ts/build_CandAT7TS.log
echo "== stage"
bash nanoda/stage.sh CandAT7TS $PWD/specroot_at7ts
