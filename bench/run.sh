#!/usr/bin/env bash
# Kernel-time benchmark runner. Usage: ./run.sh [reps]   (from this directory)
# Compiles BenchCore/BenchData/BenchADefs/BenchBDefs to .olean (if stale), then times each
# per-theorem file per/{A,B}_wk*.lean and the imports-only baselines per/Empty_{A,B}.lean.
# Output: results.tsv  (file, rep, wall_s, user_s, maxrss_bytes, peak_footprint_bytes, status)
set -u
cd "$(dirname "$0")"
REPS=${1:-2}
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean}
export LEAN_PATH=$PWD
run() { env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" "$@"; }

for m in BenchCore BenchData BenchADefs BenchBDefs; do
  if [ ! -f $m.olean ] || [ $m.lean -nt $m.olean ]; then run -o $m.olean $m.lean || exit 1; fi
done

out=results.tsv
printf 'file\trep\twall_s\tuser_s\tmaxrss\tpeak_footprint\tstatus\n' > $out
for rep in $(seq 1 "$REPS"); do
  for f in per/Empty_A.lean per/Empty_B.lean per/A_*.lean per/B_*.lean; do
    free=$(memory_pressure | tail -1 | grep -oE '[0-9]+')
    if [ "$free" -lt 20 ]; then echo "memory pressure: ${free}% free; stopping"; exit 2; fi
    log=$(mktemp)
    /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" "$f" > "$log" 2>&1
    st=$?
    wall=$(grep -E ' real ' "$log" | awk '{print $1}')
    user=$(grep -E ' real ' "$log" | awk '{print $3}')
    rss=$(grep 'maximum resident set size' "$log" | awk '{print $1}')
    pk=$(grep 'peak memory footprint' "$log" | awk '{print $1}')
    if grep -q 'error' "$log"; then st=ERR; fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$rep" "$wall" "$user" "$rss" "$pk" "$st" | tee -a $out
    rm -f "$log"
  done
done
