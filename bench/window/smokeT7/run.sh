#!/bin/sh
# smoke-compile the n = 7 tail generator against rootR7 (stub certificate; test only)
cd /Users/samuellavery/work/riemann-submission/bench/window
S=$PWD/smokeT7
LP="$S:$PWD/rootR7:$(cat ../specroot/LEAN_PATH.txt)"
L=~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 $L -o $S/ChallengeDeps/CandidateSpec.olean $S/ChallengeDeps/CandidateSpec.lean || exit 1
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 $L -o $S/AMW/T7SInst.olean $S/AMW/T7SInst.lean || exit 1
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 $L $S/TailSmoke7.lean
