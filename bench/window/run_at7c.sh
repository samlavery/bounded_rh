#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench/window
until [ -f run_at7.done ]; do sleep 30; done
bash ./buildonly_rec.sh $PWD/AT7c.lean CandAT7c 6734302 10000000 67342981 100000000 specroot_at7c > at7c_build.log 2>&1
echo DONE > run_at7c.done
