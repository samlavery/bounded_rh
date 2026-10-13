#!/bin/sh
# AMTOPA-window LP ceilings under our assembly; sequential to keep RAM low.
cd /Users/samuellavery/work/riemann-submission/bench/window
for QB in "5 0.0030" "5 0.0036" "5 0.0042" "6 0.0036" "6 0.0040435" "6 0.0046" "7 0.0040435" "7 0.0046" "7 0.0036"; do
  set -- $QB
  nice -n 10 python3 ww.py AM $1 $2 30 >> am_runs.log 2>&1
done
echo DONE >> am_runs.log
