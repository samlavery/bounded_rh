#!/bin/sh
# stage H: layer + MT-certificate stand-in, then the pruned layer alone; build+replay then export/nanoda/closure replay
cd /Users/samuellavery/work/riemann-submission/bench
bash pyr/private_check_rec.sh $PWD/window/AMHM.lean CandAMHM 6734 10000 6731631 10000000 specroot_amhm > window/amhm_check.log 2>&1
bash nanoda/stage.sh CandAMHM $PWD/specroot_amhm > window/amhm_stage.log 2>&1
bash pyr/private_check_rec.sh $PWD/window/AMH2.lean CandAMH2 6734 10000 6731631 10000000 specroot_amh2 > window/amh2_check.log 2>&1
bash nanoda/stage.sh CandAMH2 $PWD/specroot_amh2 > window/amh2_stage.log 2>&1
echo DONE > window/run_h.done
