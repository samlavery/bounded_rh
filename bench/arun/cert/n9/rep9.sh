#!/usr/bin/env bash
# rep9.sh (bridge-port, 2026-10-11): nanoda peak spread (am-cert: the peak is not deterministic, ±0.9 GB). For each variant,
# export TARGETS once (lean4export, as nanoda/stage_bench.sh), then nanoda_bin N times on the same export; peaks and
# instructions per run.  Usage: rep9.sh N MOD ROOT TARGET TAG [MOD ROOT TARGET TAG ...]  (holds the lean lock)
set -u
cd ~/work/riemann-submission/bench
NREP=$1; shift
until mkdir .leanlock 2>/dev/null; do sleep 30; done
trap 'rmdir .leanlock 2>/dev/null' EXIT
ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt); T=~/work/riemann-submission/tools; O=arun/cert/n9/rep
mkdir -p $O
while [ $# -ge 4 ]; do
  MOD=$1; PFX=$2; TG1=$3; TAG=$4; shift 4
  EXP=$O/exp_$TAG.ndjson
  TG="$TG1 Nat String String.mk Char Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce"
  env LEAN_PATH=$PFX:$ZP LEAN_ABORT_ON_PANIC=1 nice -n 10 $T/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export $MOD -- $TG > $EXP 2> $O/export_$TAG.err || { echo "$TAG export failed"; continue; }
  for k in $(seq 1 $NREP); do
    /usr/bin/time -l nice -n 10 $T/nanoda/target/release/nanoda_bin nanoda/nanoda_cfg.json < $EXP > $O/nanoda_${TAG}_$k.out 2> $O/nanoda_${TAG}_$k.err
    printf "%s run %d exit %d: " $TAG $k $?; grep -E "instructions retired|peak memory" $O/nanoda_${TAG}_$k.err | awk '{printf "%s ", $1}'; echo
  done
  rm -f $EXP
done
echo "== rep9 done $(date)"
