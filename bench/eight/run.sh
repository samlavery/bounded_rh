#!/usr/bin/env bash
# run.sh FILE.lean [OUT.olean]: compile against the zeta23 Mathlib (LEAN_PATH = this dir + ../lean_path_zeta23.txt) under the shared lock
cd "$(dirname "$0")"
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean}
f=$1; log=${f%.lean}.log
export LEAN_PATH=$PWD:$(cat ../lean_path_zeta23.txt)
if [ -n "$2" ]; then OUTARG="-o $2"; else OUTARG=""; fi
../pyr/withlock.sh /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 "$LEAN" $OUTARG "$f" > "$log" 2>&1
st=$?
echo "== $f exit=$st $(grep -E ' real ' "$log" | awk '{print "wall="$1"s"}') $(grep 'peak memory footprint' "$log" | awk '{printf "peak=%.0fMB", $1/1048576}')"
grep -E "error" "$log" | head -30
exit $st
