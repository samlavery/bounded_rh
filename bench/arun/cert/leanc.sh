#!/bin/sh
# bridge-port 2026-10-10: compile one module of a root under bench/arun/cert against rootR8f's oleans
# (as window/leanr.sh, with the cert root searched first).  Usage: leanc.sh /abs/cert/root AMW/Module
# Run it through ../../pyr/withlock.sh.
R=$1; M=$2
W=/Users/samuellavery/work/riemann-submission/bench/window
LP="$R:$W/rootR8f:$(cut -d: -f2- $W/../specroot/LEAN_PATH.txt)"
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -o "$R/$M.olean" "$R/$M.lean"
