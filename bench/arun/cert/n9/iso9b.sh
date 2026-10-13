#!/usr/bin/env bash
# iso9b.sh (bridge-port, 2026-10-11): per-walk nanoda peak against leaves on PC9QB4 (LB 32768): TARGETS = rcN._proof_1 for
# roots 31 (37 leaves), 0 (53), 5 (521), 9 (649), 4 (654); rc10 (784) is in iso9.sh.
set -u
B=~/work/riemann-submission/bench; N=$B/arun/cert/n9; R=$N/root_PC9QB4
cd $B
for n in 31 0 5 9 4; do
  tag=rc$n
  TARGETS="AMW.Cert.PC9QB4Data.rc$n._proof_1" bash nanoda/stage_bench.sh AMW.PC9QB4Data $R > $N/nanoda_PC9QB4_iso_$tag.log 2>&1
  mkdir -p $N/stagerr_PC9QB4_iso_$tag && cp nanoda/{export,nanoda,replayx}_AMW.PC9QB4Data.err $N/stagerr_PC9QB4_iso_$tag/
  rm -f nanoda/exp_AMW.PC9QB4Data.ndjson
  printf "%s nanoda: " $tag; grep -E "instructions retired|peak memory" $N/stagerr_PC9QB4_iso_$tag/nanoda_AMW.PC9QB4Data.err | awk '{printf "%s ", $1}'; echo
done
echo "== iso9b done $(date)"
