#!/usr/bin/env bash
# run every mb/T*.lean (or the given ones) under one lock acquisition; print kernel time of the theorem
cd "$(dirname "$0")"
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean}
files=${*:-mb/T*.lean}
./withlock.sh bash -c "for f in $files; do t=\$(env LEAN_NUM_THREADS=2 nice -n 10 $LEAN \$f 2>&1 | grep 'type checking took' | head -1 | awk '{print \$4}'); echo \"\$f \$t\"; done"
