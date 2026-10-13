#!/usr/bin/env bash
cd ~/work/riemann-submission/bench/window/amg
for m in GCell GBase GConst GFar GNear GAsm1 GAsm2 GCellSound CFacade CEngine CWindow CMin CMLeaf AMR7Inst AMR7Data; do ./lean_r.sh rootT $m || exit 1; done
LP=$(cut -d: -f2- $HOME/work/riemann-submission/bench/specroot/LEAN_PATH.txt)
for R in amg/rootT rootR7; do
  D=$HOME/work/riemann-submission/bench/window/$R; tag=$(basename $R)
  cd $D && LEAN_PATH="$D:$LP" /usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 $HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -DElab.async=false -o /tmp/wb_$tag.olean AMW/AMR7WB.lean > $HOME/work/riemann-submission/bench/window/amg/wbt_$tag.log 2>&1
  echo "$tag exit=$? $(grep ' real ' $HOME/work/riemann-submission/bench/window/amg/wbt_$tag.log)"
done
