#!/bin/sh
cd /Users/samuellavery/work/riemann-submission/bench/window
for n in 6 7; do for B in 0.0032 0.0036 0.0040; do for w0 in 1.40 1.4142135623730951 1.45 1.5 1.55; do
  nice -n 10 python3 wopt.py scan $n $B $w0 0 >> wscan_single.log 2>&1
done; done; done
echo DONE >> wscan_single.log
