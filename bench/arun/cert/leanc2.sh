#!/bin/sh
# bridge-port 2026-10-11: as leanc.sh, but `exec`s lean (env and nice exec in place) so that `/usr/bin/time -l leanc2.sh …`
# measures the lean process itself (peak memory footprint).  Usage: withlock.sh /usr/bin/time -l leanc2.sh /abs/root AMW/Module
R=$1; M=$2
W=/Users/samuellavery/work/riemann-submission/bench/window
LP="$R:$W/rootR8f:$(cut -d: -f2- $W/../specroot/LEAN_PATH.txt)"
exec env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -o "$R/$M.olean" "$R/$M.lean"
