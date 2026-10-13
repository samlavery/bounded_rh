#!/usr/bin/env bash
# Per-declaration kernel time ("type checking took") for each variant's combined file Bench{V}.lean.
# Usage: ./profile.sh [variants...]   default: A B C P0 P1 P2.  Writes prof_{V}.log and profile.tsv.
set -u
cd "$(dirname "$0")"
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean}
export LEAN_PATH=$PWD
VARIANTS=${*:-"A B C P0 P1 P2"}
run() { env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" "$@"; }
for m in BenchCore BenchData; do
  if [ ! -f $m.olean ] || [ $m.lean -nt $m.olean ]; then run -o $m.olean $m.lean || exit 1; fi
done
printf 'variant\ttheorem\tkernel_s\n' > profile.tsv
for v in $VARIANTS; do
  m=Bench${v}Defs
  if [ ! -f $m.olean ] || [ $m.lean -nt $m.olean ]; then run -o $m.olean $m.lean || exit 1; fi
  free=$(memory_pressure | tail -1 | grep -oE '[0-9]+')
  if [ "$free" -lt 20 ]; then echo "memory pressure: ${free}% free; stopping"; exit 2; fi
  /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" Bench$v.lean > prof_$v.log 2>&1
  echo "== $v exit=$? $(grep -E ' real ' prof_$v.log | awk '{print "wall="$1"s"}') $(grep 'peak memory footprint' prof_$v.log | awk '{printf "peak=%.0fMB", $1/1048576}')"
  grep -E 'error' prof_$v.log
  thms=$(grep -oE '^theorem wk[0-9]+' Bench$v.lean | awk '{print $2}')
  paste <(echo "$thms") <(grep -E '^type checking took' prof_$v.log | awk '{print $4}') | awk -v v=$v '{t=$2; if (t ~ /ms$/) {sub(/ms$/,"",t); t=t/1000} else sub(/s$/,"",t); printf "%s\t%s\t%.3f\n", v, $1, t}' | tee -a profile.tsv
done
