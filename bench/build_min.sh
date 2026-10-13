#!/usr/bin/env bash
# Build a candidate exactly as Cand35RKF was built (zeta23 LEAN_PATH, olean written into bench/, nothing under
# zeta23/), then replay the olean through the Lean kernel with comparator/Solution/ReplayHarness.lean.
# usage: bench/build_min.sh SRC.lean MODNAME      (copies SRC to bench/MODNAME.lean)
# Holds bench/.leanlock for the duration (another agent builds Lean on this machine).
set -u
B=$HOME/work/riemann-submission/bench
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
src=$1; mod=$2
cd "$B" || exit 1
until mkdir .leanlock 2>/dev/null; do sleep 30; done
trap 'rmdir "$B/.leanlock"' EXIT
free=$(memory_pressure | tail -1 | grep -oE '[0-9]+')
if [ "$free" -lt 20 ]; then echo "memory pressure: ${free}% free; stopping"; exit 2; fi
cp "$src" "$mod.lean"
export LEAN_PATH=$(cat lean_path_zeta23.txt)
date +%s > "${mod}_build.start"
/usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" -o "$mod.olean" "$mod.lean" > "${mod}_build.log" 2>&1
st=$?
echo "exit=$st" >> "${mod}_build.log"
date +%s > "${mod}_build.end"
[ $st -eq 0 ] || exit $st
free=$(memory_pressure | tail -1 | grep -oE '[0-9]+')
if [ "$free" -lt 20 ]; then echo "memory pressure: ${free}% free; skipping replay"; exit 2; fi
/usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" --run ../zeta23/comparator/Solution/ReplayHarness.lean "$mod.olean" > "replay_${mod}.log" 2>&1
echo "exit=$?" >> "replay_${mod}.log"
