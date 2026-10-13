#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench
bash pyr/private_check_rec.sh $PWD/window/AR7.lean CandAR7 6734227 10000000 6733166 10000000 specroot_ar7 > window/ar7_check.log 2>&1
bash nanoda/stage.sh CandAR7 $PWD/specroot_ar7 > window/ar7_stage.log 2>&1
echo DONE > window/run_am7m.done
