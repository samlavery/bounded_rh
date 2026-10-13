#!/usr/bin/env bash
# run_variant.sh TAG: compile Bench{TAG}Data/Defs to .olean and profile Bench{TAG}.lean (per-theorem kernel time) under the lock
set -u
cd "$(dirname "$0")/.."
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean}
export LEAN_PATH=$PWD
v=$1
body() {
  for m in BenchCore BenchData Bench${v}Data Bench${v}Defs; do
    [ -f $m.lean ] || continue; if [ ! -f $m.olean ] || [ $m.lean -nt $m.olean ]; then env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" -o $m.olean $m.lean || exit 1; fi
  done
  /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" Bench$v.lean > prof_$v.log 2>&1
}
pyr/withlock.sh bash -c "$(declare -f body); LEAN=$LEAN; v=$v; body" || exit 1
echo "== $v $(grep -E ' real ' prof_$v.log | awk '{print "wall="$1"s"}') $(grep 'peak memory footprint' prof_$v.log | awk '{printf "peak=%.0fMB", $1/1048576}')"
grep -E 'error' prof_$v.log | head -5
thms=$(grep -oE '^theorem wk[0-9]+' Bench$v.lean | awk '{print $2}')
paste <(echo "$thms") <(grep -E '^type checking took' prof_$v.log | awk '{print $4}') | awk -v v=$v '{t=$2; if (t ~ /ms$/) {sub(/ms$/,"",t); t=t/1000} else sub(/s$/,"",t); printf "%s\t%s\t%.3f\n", v, $1, t; s+=t} END {printf "%s\tTOTAL\t%.3f\n", v, s}'
