#!/bin/sh
# smoke-compile the n = 8 tail generator against rootR8 (stub certificate; test only)
cd /Users/samuellavery/work/riemann-submission/bench/window
S=$PWD/smokeT8
LP="$S:$PWD/rootR8:$(cat ../specroot/LEAN_PATH.txt)"
L=~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 $L -o $S/ChallengeDeps/CandidateSpec.olean $S/ChallengeDeps/CandidateSpec.lean || exit 1
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 $L -o $S/AMW/T8SInst.olean $S/AMW/T8SInst.lean || exit 1
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 $L $S/TailSmoke8.lean
