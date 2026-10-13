#!/usr/bin/env bash
# phase1_mem.sh (am-cert, 2026-10-10): build RSS and post-build stages (export → nanoda → closure replay) of the PC8C5BF
# walk benches: PFBenchNP (real side conditions), PFBenchNO (side conditions → true), PFBenchNPH (16 of the 32 walks),
# PFBenchNP1 (the single largest walk, root 10).  Measurement only; bench modules certify nothing.
set -u
B=~/work/riemann-submission/bench; W=$B/window; ZP=$(cut -d: -f2- $B/specroot/LEAN_PATH.txt)
LEANBIN=~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
until mkdir $B/.leanlock 2>/dev/null; do sleep 30; done
trap 'rmdir $B/.leanlock 2>/dev/null' EXIT
for M in PFBenchNP PFBenchNO PFBenchNPH PFBenchNP1; do
  echo "== build $M $(date +%T)"
  ( cd $W && /usr/bin/time -l env LEAN_PATH="$W/rootR8f:$ZP" LEAN_NUM_THREADS=2 nice -n 10 $LEANBIN -o rootR8f/AMW/$M.olean rootR8f/AMW/$M.lean ) > $B/arun/p1_build_$M.log 2>&1
  echo "build exit $?"; grep -E " real|instructions retired|maximum resident|peak memory" $B/arun/p1_build_$M.log
done
rmdir $B/.leanlock; trap - EXIT
for M in PFBenchNP PFBenchNO PFBenchNPH PFBenchNP1; do
  T=$(grep -oE "^theorem b[0-9]+" $W/rootR8f/AMW/$M.lean | awk -v m=$M '{print "AMW.Cert." m "." $2}' | tr '\n' ' ')
  TARGETS="$T" bash $B/nanoda/stage_bench.sh AMW.$M $W/rootR8f
  rm -f $B/nanoda/exp_AMW.$M.ndjson
done
echo "== phase1_mem done $(date +%T)"
