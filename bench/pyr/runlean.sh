#!/usr/bin/env bash
# runlean.sh FILE.lean [LOG]: core-Lean compile under the lock, LEAN_PATH = bench dir (+ pyr), timing to LOG
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean}
f=$1; log=${2:-${1%.lean}.log}
cd "$(dirname "$0")"
export LEAN_PATH=$PWD/..:$PWD
./withlock.sh /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" ${OUT:+-o $OUT} "$f" > "$log" 2>&1
st=$?
echo "== $f exit=$st $(grep -E ' real ' "$log" | awk '{print "wall="$1"s"}') $(grep 'peak memory footprint' "$log" | awk '{printf "peak=%.0fMB", $1/1048576}')"
grep -E "type checking took|error" "$log" | head -40
