#!/usr/bin/env bash
# profbuild.sh SRC.lean MOD ROOT: build SRC with the profiler on (threshold 200 ms) in an existing private spec root ROOT
# (made by private_check_rec.sh, whose CandidateSpec matches SRC's kappa), under the shared lock; no replay.
# Log: ROOT/prof_MOD.log.
set -u
cd ~/work/riemann-submission/bench
SRC=$1; MOD=$2; R=$3
until mkdir .leanlock 2>/dev/null; do echo "[profbuild] waiting $(date +%T)"; sleep 30; done
trap 'rmdir .leanlock 2>/dev/null' EXIT
free=$(memory_pressure | tail -1 | grep -oE '[0-9]+'); [ "${free:-0}" -lt 20 ] && { echo "memory pressure ${free}%"; exit 2; }
ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt)
LEANBIN=~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
python3 - "$SRC" "$R/$MOD.lean" <<'PY'
import sys
s = open(sys.argv[1], encoding="utf-8").read()
i = s.index("\nnoncomputable section")
open(sys.argv[2], "w", encoding="utf-8").write(s[:i] + "\nset_option profiler true\nset_option profiler.threshold 200\n" + s[i:])
PY
/usr/bin/time -l env LEAN_PATH=$PWD/$R:$ZP LEAN_NUM_THREADS=2 nice -n 10 $LEANBIN $R/$MOD.lean > $R/prof_$MOD.log 2>&1
echo "BUILD EXIT $?" >> $R/prof_$MOD.log
grep -E "BUILD EXIT| real|peak memory" $R/prof_$MOD.log
