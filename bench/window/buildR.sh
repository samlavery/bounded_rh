#!/bin/sh
# build the AMW layer in a chosen root, in dependency order, stopping at the first failure: ./buildR.sh rootR [MODS...]
R=$1; shift
MODS=${*:-"Window Kernel Moments Swap Constant Floor Trig Adm Profile PV Params ZeroSide Concrete BHalf BrA BrB BrC AMTail"}
for m in $MODS; do
  t0=$(date +%s)
  if ./leanr.sh $R AMW/$m > logs_$R/$m.log 2>&1; then echo "$m OK $(( $(date +%s) - t0 ))s"; else echo "$m FAIL $(( $(date +%s) - t0 ))s"; head -40 logs_$R/$m.log; exit 1; fi
done
