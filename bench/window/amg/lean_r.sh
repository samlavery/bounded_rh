#!/usr/bin/env bash
# lean_r.sh ROOT X : compile ROOT/AMW/X.lean (ROOT a sibling of root/, e.g. rootR7) -> its olean (stage G); LOCK=1 for the shared lock
R=$HOME/work/riemann-submission/bench/window/$1; [ -d "$R" ] || R=$HOME/work/riemann-submission/bench/window/amg/$1
LP=$(cut -d: -f2- $HOME/work/riemann-submission/bench/specroot/LEAN_PATH.txt)
export LEAN_PATH="$R:$LP"
cd $R
LOG=$HOME/work/riemann-submission/bench/window/amg/$1_$2.log
CMD="/usr/bin/time -l env LEAN_NUM_THREADS=2 nice -n 10 $HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -DElab.async=false $EXTRA -o AMW/$2.olean -i AMW/$2.ilean AMW/$2.lean"
if [ -n "$LOCK" ]; then $HOME/work/riemann-submission/bench/pyr/withlock.sh $CMD > $LOG 2>&1; else $CMD > $LOG 2>&1; fi
st=$?
echo "== $1/AMW/$2 exit=$st $(grep -E ' real ' $LOG | awk '{print "wall="$1"s"}') $(grep 'peak memory footprint' $LOG | awk '{printf "peak=%.0fMB", $1/1048576}')"
grep -E "error|warning: declaration uses" $LOG | head -40
exit $st
