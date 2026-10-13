#!/bin/sh
# abl_run.sh NAME ENV...: one ablation sizing (roots 4+17) -> abl_NAME.log
n=$1; shift
cd "$(dirname "$0")"
env "$@" nice -n 10 python3 run8pz.py /Users/samuellavery/work/riemann-submission/bench/window/rwin8_B440000.json 0.001 > abl_$n.log 2>&1
