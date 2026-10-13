#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench
while [ ! -f window/run_h.done ]; do sleep 30; done
bash pyr/private_check_rec.sh $PWD/window/AMHM.lean CandAMHM 6734 10000 6731631 10000000 specroot_amhm > window/amhm_check.log 2>&1
bash nanoda/stage.sh CandAMHM $PWD/specroot_amhm > window/amhm_stage.log 2>&1
echo DONE > window/run_h2.done
