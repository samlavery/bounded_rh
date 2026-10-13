#!/usr/bin/env bash
# build_cand.sh NAME: compile bench/<NAME>.lean to bench/<NAME>.olean against the zeta23 LEAN_PATH (as Cand35RKF was),
# under the shared Lean lock; log to bench/<log>, start/end epoch stamps, exit code appended.
set -u
cd "$(dirname "$0")/.."
N=$1; LOG=${2:-${N}_build.log}
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
body() {
  date +%s > ${N}.start
  /usr/bin/time -l env LEAN_PATH=$(cat lean_path_zeta23.txt) LEAN_NUM_THREADS=2 nice -n 10 $LEAN -o ${N}.olean ${N}.lean > $LOG 2>&1
  echo "exit=$?" >> $LOG
  date +%s > ${N}.end
}
export -f body; export N LOG LEAN
pyr/withlock.sh bash -c body
tail -25 $LOG | grep -E "exit=|real|peak memory|maximum resident|error" 
