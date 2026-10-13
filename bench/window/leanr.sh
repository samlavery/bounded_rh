#!/bin/sh
# compile one module in a chosen root: ./leanr.sh rootR AMW/Window   (olean into rootR/AMW)
cd /Users/samuellavery/work/riemann-submission/bench/window
R=$1; M=$2
LP="/Users/samuellavery/work/riemann-submission/bench/window/$R:$(cut -d: -f2- ../specroot/LEAN_PATH.txt)"
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -o $R/$M.olean $R/$M.lean
