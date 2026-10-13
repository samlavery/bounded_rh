#!/usr/bin/env bash
# iso9.sh (bridge-port, 2026-10-11): nanoda peak isolation on PC9QB4 (ANATOMY §nanoda peak isolation). Waits for int9q4b.sh,
# then walk-only stages with TARGETS = (a) rc10._proof_1 (the 784-leaf walk's decide: walk defs, tables, PT def; no PTT_ok),
# (b) PTT_ok (the 8 point-subtree checks), (c) PT (the base: tables, PT/PTT definitions, instance defs; am-cert's suggestion).
# Each run's .err files are copied to stagerr_PC9QB4_iso_<tag>/ (stage_bench.sh reuses the module's file names).
set -u
B=~/work/riemann-submission/bench; N=$B/arun/cert/n9; R=$N/root_PC9QB4
until grep -q "== int9q4b done\|failed\|stop\|outputs exist\|no unreach" $B/arun/int9q4b.log; do sleep 30; done
cd $B
for T in rc10._proof_1 PTT_ok PT; do
  tag=${T%%.*}
  echo "== iso $T $(date)"
  TARGETS="AMW.Cert.PC9QB4Data.$T" bash nanoda/stage_bench.sh AMW.PC9QB4Data $R > $N/nanoda_PC9QB4_iso_$tag.log 2>&1
  mkdir -p $N/stagerr_PC9QB4_iso_$tag && cp nanoda/{export,nanoda,replayx}_AMW.PC9QB4Data.err $N/stagerr_PC9QB4_iso_$tag/
  rm -f nanoda/exp_AMW.PC9QB4Data.ndjson
  for s in export nanoda replayx; do printf "%s %s: " $tag $s; grep -E "instructions retired|peak memory" $N/stagerr_PC9QB4_iso_$tag/${s}_AMW.PC9QB4Data.err | awk '{printf "%s ", $1}'; echo; done
  grep -E "exit|export bytes" $N/nanoda_PC9QB4_iso_$tag.log | tr '\n' ' '; echo
done
echo "== iso done $(date)"
