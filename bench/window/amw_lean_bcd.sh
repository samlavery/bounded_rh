#!/usr/bin/env bash
# compile one AMW module: amw_lean_bcd.sh X   (root/AMW/X.lean -> root/AMW/X.olean); stage B/C/D/F agent
set -o pipefail
R=$HOME/work/riemann-submission/bench/window/root
LP=$(cut -d: -f2- $HOME/work/riemann-submission/bench/specroot/LEAN_PATH.txt)
export LEAN_PATH="$R:$LP"
export LEAN_NUM_THREADS=2
cd $R
/usr/bin/time -l nice -n 10 $HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean -o AMW/$1.olean -i AMW/$1.ilean AMW/$1.lean 2>&1 | grep -v "^\s*[0-9]* *\(involuntary\|voluntary\|block\|messages\|signals\|swaps\|page\|instructions\|cycles\|average\|maximum resident\)" 
