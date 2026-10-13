#!/bin/bash
# bridge-port, 2026-10-10. Emit + Data + Inst for a build-engine (rank-1 quantisation [+ EXACTV]) dump, with the
# quantisation-aware generator copies emit9q.py / make9qC.py and window/amg/genpcellQ.py (SIGSH, QB from env).
# Usage: WJ=... DELTA=... DUMP=... NAME=... [LSC=1024 YFRAC=16 QB=13 EXACTV=1] ./gen9q.sh   (bytes measurement; the
# EXACTV certificate needs the lever-1 Lean validity layer to compile)
set -u
B=/Users/samuellavery/work/riemann-submission/bench
R=$B/arun/cert/n9
cd "$R"
export AMWIN=$B/window/rwin8.json
: ${TWOGRID:=1} ${GSH:=5} ${JSH:=5} ${WMIN:=8} ${DLO:=7} ${DHI:=8} ${PLO:=1} ${MINR:=0} ${YFRAC:=16} ${LSC:=1024} ${NR:=0}
: ${TRIPLE:=1} ${PERSIST:=1} ${ZEXT:=8} ${SPLIT:=pf} ${PFK:=8} ${MINPW:=256} ${NOZ:=1} ${TCLOSE:=1} ${MINSPLIT:=2} ${BSPLIT:=1} ${QB:=13}
export TWOGRID GSH JSH WMIN DLO DHI PLO MINR YFRAC LSC NR TRIPLE PERSIST ZEXT SPLIT PFK MINPW NOZ TCLOSE MINSPLIT BSPLIT QB
OUTR=$R/root_$NAME; mkdir -p $OUTR/AMW
echo "== E emit $(date)"
/usr/bin/time -l nice -n 5 python3 $R/emit9q.py $WJ $DELTA $DUMP $R/DATA_$NAME.json 2>&1 || exit 1
echo "== D data module $(date)"
( unset NR; /usr/bin/time -l nice -n 5 python3 $R/make9qC.py $R/DATA_$NAME.json $NAME $OUTR 2>&1 ) || exit 1
echo "== I instance module $(date)"
( unset NR AMWIN; CLOSE=1 HELP=1 BSPLIT=1 DFAST=3 LETC=1 SIGSH=$YFRAC QB=$QB DATA=$R/DATA_$NAME.json PCOUT=$OUTR/AMW \
    /usr/bin/time -l nice -n 5 python3 $B/window/amg/genpcellQ.py rootR8f ${NAME}Inst 8 2>&1 ) || exit 1
echo "== done $(date)"
