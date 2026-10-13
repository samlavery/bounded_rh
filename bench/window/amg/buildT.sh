#!/usr/bin/env bash
# typh-engine port test: rebuild the changed stack in rootT, then AMR7Data with the profiler; baseline AMR7Data (rootR7) with the profiler to /tmp
cd ~/work/riemann-submission/bench/window/amg
for m in GCell GBase GConst GFar GNear GAsm1 GAsm2 GCellSound CFacade CEngine CWindow CMin CMLeaf AMR7Inst; do ./lean_r.sh rootT $m || exit 1; done
EXTRA="-Dprofiler=true -Dprofiler.threshold=1" ./lean_r.sh rootT AMR7Data || exit 1
R=$HOME/work/riemann-submission/bench/window/rootR7
LP=$(cut -d: -f2- $HOME/work/riemann-submission/bench/specroot/LEAN_PATH.txt)
cd $R && LEAN_PATH="$R:$LP" /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 $HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -DElab.async=false -Dprofiler=true -Dprofiler.threshold=1 -o /tmp/AMR7Data_base.olean AMW/AMR7Data.lean > $HOME/work/riemann-submission/bench/window/amg/base_AMR7Data_prof.log 2>&1
echo "baseline exit=$?"
