#!/usr/bin/env bash
# bridge-port: compile a module of bpprof against CandAT7c (specroot_at7c); usage: lean.sh MODULE [-o]
cd $HOME/work/riemann-submission/bench/window/bpprof
ZP=$(cut -d: -f2- ../../specroot/LEAN_PATH.txt)
LP="$PWD:$HOME/work/riemann-submission/bench/specroot_at7c:$ZP"
s=$(date +%s)
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -o $1.olean $1.lean > $1.log 2>&1
rc=$?; echo "$1 rc=$rc errors=$(grep -c 'error' $1.log) $(( $(date +%s) - s ))s"
