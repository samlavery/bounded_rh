#!/usr/bin/env bash
# stage_mem.sh OUT : time, peak memory footprint and max RSS of every stage of a run_n8.sh run with outputs ${OUT}T/TS
# (private checks' build and replay, export, nanoda, closure replay), plus nanoda's instruction count.
OUT=$1; lc=$(echo "$OUT" | tr A-Z a-z); B=~/work/riemann-submission/bench
row() {  # label file
  [ -e "$2" ] || { printf '%-22s (missing %s)\n' "$1" "$2"; return; }
  awk -v l="$1" '/ real /{t=$1} /maximum resident set size/{r=$1} /peak memory footprint/{p=$1}
    /instructions retired/{i=$1}
    END{printf "%-22s %8.1f s  footprint %5.2f GB  max RSS %5.2f GB%s\n", l, t, p/1e9, r/1e9, (i ? sprintf("  instr %.3e", i) : "")}' "$2"
}
row "build T" $B/specroot_${lc}t/build_Cand${OUT}T.log
row "module replay T" $B/specroot_${lc}t/replay_Cand${OUT}T.log
row "build TS" $B/specroot_${lc}ts/build_Cand${OUT}TS.log
row "module replay TS" $B/specroot_${lc}ts/replay_Cand${OUT}TS.log
row "export" $B/nanoda/export_Cand${OUT}TS.err
row "nanoda" $B/nanoda/nanoda_Cand${OUT}TS.err
row "closure replay" $B/nanoda/replayx_Cand${OUT}TS.err
