#!/bin/bash
# bridge-port 2026-10-10: peak memory of the PC8C5BFData build (control for memprof_data.sh) per declaration, with Elab.async false (as in the assembled
# MOP file) and the profiler on.  The same source compiles to a scratch olean (n9/memprof/), so root9 is untouched.
# Output: memprof/out.log (profiler lines, each prefixed with the epoch second), memprof/rss.log (epoch second, RSS KB).
# Run through ../../../pyr/withlock.sh.
R=/Users/samuellavery/work/riemann-submission/bench/arun/cert/n9
W=/Users/samuellavery/work/riemann-submission/bench/window
M=$R/memprof8
LP="$W/rootR8f:$(cut -d: -f2- $W/../specroot/LEAN_PATH.txt)"
env LEAN_PATH="$LP" LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=200 --root=$W/rootR8f -o $M/PC8C5BFData.olean $W/rootR8f/AMW/PC8C5BFData.lean 2>&1 \
  | while IFS= read -r line; do echo "$(date +%s) $line"; done > $M/out.log &
sleep 2
LPID=$(pgrep -f "lean -DElab.async=false -Dprofiler=true.*PC8C5BFData.lean" | head -1)
echo "lean pid $LPID"
while kill -0 $LPID 2>/dev/null; do echo "$(date +%s) $(ps -o rss= -p $LPID)" >> $M/rss.log; sleep 1; done
wait
echo "done $(date)"
