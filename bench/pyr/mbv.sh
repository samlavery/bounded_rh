#!/usr/bin/env bash
cd "$(dirname "$0")/.."
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean
for k in "$@"; do
  env LEAN_PATH=$PWD LEAN_NUM_THREADS=2 nice -n 10 $LEAN -o BenchV${k}Defs.olean BenchV${k}Defs.lean || exit 1
  echo "V$k $(env LEAN_PATH=$PWD LEAN_NUM_THREADS=2 nice -n 10 $LEAN MbV$k.lean 2>&1 | grep 'type checking took' | head -1)"
  echo "V$k again $(env LEAN_PATH=$PWD LEAN_NUM_THREADS=2 nice -n 10 $LEAN MbV$k.lean 2>&1 | grep 'type checking took' | head -1)"
done
