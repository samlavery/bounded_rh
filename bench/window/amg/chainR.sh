#!/usr/bin/env bash
# chainR.sh ROOT X Y ...: compile ROOT/AMW/X.lean, Y.lean, ... in order under one hold of the shared lock (stage G)
cd "$(dirname "$0")"
R=$1; shift
exec ~/work/riemann-submission/bench/pyr/withlock.sh bash -c 'R=$1; shift; for m in "$@"; do ./lean_r.sh "$R" "$m" || exit 1; done' _ "$R" "$@"
