#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench
bash pyr/private_check_rec.sh $PWD/window/AM7m.lean CandAM7m 6734033 10000000 6733166 10000000 specroot_am7m > window/am7m_check.log 2>&1
bash nanoda/stage.sh CandAM7m $PWD/specroot_am7m > window/am7m_stage.log 2>&1
echo DONE > window/run_am7m.done
