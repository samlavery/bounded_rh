#!/usr/bin/env bash
# chain.sh X Y Z ...: compile root/AMW/X.lean, Y.lean, ... in order under one hold of the shared lock (stage G)
cd "$(dirname "$0")"
exec ~/work/riemann-submission/bench/pyr/withlock.sh bash -c 'for m in "$@"; do EXTRA="-DElab.async=false" ./lean_amw.sh "$m" || exit 1; done' _ "$@"
