#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench
bash pyr/private_check_rec.sh $PWD/window/AT7.lean CandAT7 6734302 10000000 67342981 100000000 specroot_at7 > window/at7_check.log 2>&1
bash nanoda/stage.sh CandAT7 $PWD/specroot_at7 > window/at7_stage.log 2>&1
echo DONE > window/run_at7.done
