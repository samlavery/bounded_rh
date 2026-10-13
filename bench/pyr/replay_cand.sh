#!/usr/bin/env bash
# replay_cand.sh NAME: Lean kernel replay of bench/<NAME>.olean (comparator/Solution/ReplayHarness.lean), under the lock
set -u
cd "$(dirname "$0")/.."
N=$1
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
body() {
  /usr/bin/time -l env LEAN_PATH=$(cat lean_path_zeta23.txt) LEAN_NUM_THREADS=2 nice -n 10 $LEAN --run ../zeta23/comparator/Solution/ReplayHarness.lean ${N}.olean > replay_${N}.log 2>&1
  echo "exit=$?" >> replay_${N}.log
}
export -f body; export N LEAN
pyr/withlock.sh bash -c body
cat replay_${N}.log | grep -E "constants|replay|exit=|real|peak memory"
