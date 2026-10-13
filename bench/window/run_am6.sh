#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench
bash pyr/private_check_rec.sh $PWD/window/AM6.lean CandAM6 6733143 10000000 6731663 10000000 specroot_am6 > window/am6_check.log 2>&1
bash nanoda/stage.sh CandAM6 $PWD/specroot_am6 > window/am6_stage.log 2>&1
echo DONE > window/run_am6.done
