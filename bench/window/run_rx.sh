#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench
T=~/work/riemann-submission/tools
/usr/bin/time -l nice -n 10 $T/replayx/.lake/build/bin/replayx nanoda/exp_CandAMHM.ndjson > window/amhm_replayx.out 2> window/amhm_replayx.err
echo "replayx exit $?" >> window/amhm_replayx.out
