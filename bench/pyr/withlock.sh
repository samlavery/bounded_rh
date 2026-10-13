#!/usr/bin/env bash
# Run a command under the shared Lean lock (mkdir ~/work/riemann-submission/bench/.leanlock), retrying every 30 s;
# the lock is released on exit (normal, error or signal). Refuses to start under critical memory pressure.
LOCK=$HOME/work/riemann-submission/bench/.leanlock
until mkdir "$LOCK" 2>/dev/null; do echo "[withlock] waiting for $LOCK ($(date +%T))" >&2; sleep 30; done
trap 'rmdir "$LOCK" 2>/dev/null' EXIT INT TERM HUP
free=$(memory_pressure | tail -1 | grep -oE '[0-9]+')
if [ "${free:-0}" -lt 20 ]; then echo "[withlock] memory pressure: ${free}% free; not running" >&2; exit 2; fi
"$@"
