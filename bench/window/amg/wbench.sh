#!/usr/bin/env bash
# walk-chunk kernel bench for ROOT in $@ (AMR7WB.lean, olean to /tmp), profiler on, one after the other
LP=$(cut -d: -f2- $HOME/work/riemann-submission/bench/specroot/LEAN_PATH.txt)
for R in "$@"; do
  D=$HOME/work/riemann-submission/bench/window/$R
  cd $D && LEAN_PATH="$D:$LP" /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 $HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -DElab.async=false -Dprofiler=true -Dprofiler.threshold=10 -o /tmp/wb_$R.olean AMW/AMR7WB.lean > $HOME/work/riemann-submission/bench/window/amg/wb_$R.log 2>&1
  echo "$R exit=$? $(grep ' real ' $HOME/work/riemann-submission/bench/window/amg/wb_$R.log)"
done
