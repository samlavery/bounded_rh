#!/bin/sh
# compile one AMW module: ./lean.sh AMW/Window   (olean into root/AMW)
cd /Users/samuellavery/work/riemann-submission/bench/window
LP="/Users/samuellavery/work/riemann-submission/bench/window/root:$(cut -d: -f2- ../specroot/LEAN_PATH.txt)"
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -o root/$1.olean root/$1.lean
