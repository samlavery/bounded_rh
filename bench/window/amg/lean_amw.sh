#!/usr/bin/env bash
# lean_amw.sh X : compile root/AMW/X.lean -> root/AMW/X.olean (stage G); LOCK=1 to go through the shared lock
R=$HOME/work/riemann-submission/bench/window/root
LP=$(cut -d: -f2- $HOME/work/riemann-submission/bench/specroot/LEAN_PATH.txt)
export LEAN_PATH="$R:$LP"
cd $R
CMD="/usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 $HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean $EXTRA -o AMW/$1.olean -i AMW/$1.ilean AMW/$1.lean"
if [ -n "$LOCK" ]; then $HOME/work/riemann-submission/bench/pyr/withlock.sh $CMD > $HOME/work/riemann-submission/bench/window/amg/$1.log 2>&1
else $CMD > $HOME/work/riemann-submission/bench/window/amg/$1.log 2>&1; fi
st=$?
echo "== AMW/$1 exit=$st $(grep -E ' real ' $HOME/work/riemann-submission/bench/window/amg/$1.log | awk '{print "wall="$1"s"}') $(grep 'peak memory footprint' $HOME/work/riemann-submission/bench/window/amg/$1.log | awk '{printf "peak=%.0fMB", $1/1048576}')"
grep -E "error|warning: declaration uses" $HOME/work/riemann-submission/bench/window/amg/$1.log | head -40
exit $st
