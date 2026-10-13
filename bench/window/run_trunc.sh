#!/bin/sh
# n = 7 LP ceilings for truncations of AMTOPA's window (first k terms, coefficients unchanged), B = 93/23000.
cd /Users/samuellavery/work/riemann-submission/bench/window
while ! grep -q DONE am_runs.log; do sleep 60; done
for k in 2 3 5 9 13; do
  nice -n 10 python3 ww.py AM$k 6 0.0040435 30 >> trunc_runs.log 2>&1
done
echo DONE >> trunc_runs.log
