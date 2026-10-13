#!/bin/bash
# bridge-port, 2026-10-10. From a Q = 8 sizing dump to the Lean modules of the 9-point certificate:
#   (E) emit9pz.py (replay, exact re-verification of every leaf on the built tables, DATA json)
#   (D) make9pcC.py (Data module)   (I) window/amg/genpcellQ.py CLOSE=1 HELP=1 BSPLIT=1 DFAST=3 LETC=1 (Inst module)
# Usage: DELTA=... DUMP=... NAME=... ./gen9.sh      (outputs: n9/DATA_$NAME.json, n9/root9/AMW/$NAME{Data,Inst}.lean)
set -u
B=/Users/samuellavery/work/riemann-submission/bench
R=$B/arun/cert/n9
cd "$R"
export AMWIN=$B/window/rwin8.json
export TWOGRID=1 GSH=5 JSH=5 WMIN=8 DLO=7 DHI=8 PLO=1 MINR=0 YFRAC=14 LSC=256 NR=0 TRIPLE=1 PERSIST=1 ZEXT=8 \
       SPLIT=pf PFK=8 MINPW=256 NOZ=1 TCLOSE=1 MINSPLIT=2 BSPLIT=1
mkdir -p "$R/root9/AMW"
echo "== E emit $(date)"
/usr/bin/time -l nice -n 5 python3 $R/emit9pz.py $R/rwin9_lp9.json $DELTA $DUMP $R/DATA_$NAME.json 2>&1 || exit 1
echo "== D data module $(date)"
( unset NR; /usr/bin/time -l nice -n 5 python3 $R/make9pcC.py $R/DATA_$NAME.json $NAME $R/root9 2>&1 ) || exit 1
echo "== I instance module $(date)"
( unset NR AMWIN; CLOSE=1 HELP=1 BSPLIT=1 DFAST=3 LETC=1 DATA=$R/DATA_$NAME.json PCOUT=$R/root9/AMW /usr/bin/time -l nice -n 5 \
    python3 $B/window/amg/genpcellQ.py rootR8f ${NAME}Inst 8 2>&1 ) || exit 1
echo "== done $(date)"
