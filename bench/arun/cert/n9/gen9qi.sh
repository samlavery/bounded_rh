#!/bin/bash
# bridge-port, 2026-10-11. REAL emission of a Q-engine (table-check) 9-point tree with lever 1:
#   (E) emit9q.py (rank-1 fields: LB from LSC, QB, SIGSH = YFRAC; replay + exact re-verification on built tables)
#   (V) arun/lever1_ivs.py with eight/am8/verify8pz.py: the independent replay; every point's hull must pass tcheck
#   (D) make9qI.py (am-cert's make9pcI.py + JB/LB/QB from the data) with IV, CHB, CHL
#   (I) window/amg/genpcellQI.py (am-cert's lever-1 instance generator) with SIGSH, QB, WIN
# Usage: WJ=... DELTA=... DUMP=... NAME=... [ZEXT=32 LSC=1024 YFRAC=16 QB=13 CHB=100000 CHL=1 WIN=512] ./gen9qi.sh
# Output: n9/root_$NAME/AMW/{NAME}Data.lean, {NAME}Inst.lean; n9/DATA_$NAME.json, n9/IV_$NAME.json.  The modules get
# `set_option Elab.async false` after their imports by hand (Edit), before any build.
set -u
B=/Users/samuellavery/work/riemann-submission/bench
R=$B/arun/cert/n9
cd "$R"
export AMWIN=$B/window/rwin8.json
: ${TWOGRID:=1} ${GSH:=5} ${JSH:=5} ${WMIN:=8} ${DLO:=7} ${DHI:=8} ${PLO:=1} ${MINR:=0} ${YFRAC:=16} ${LSC:=1024} ${NR:=0}
: ${TRIPLE:=1} ${PERSIST:=1} ${ZEXT:=32} ${SPLIT:=pf} ${PFK:=8} ${MINPW:=256} ${NOZ:=1} ${TCLOSE:=1} ${MINSPLIT:=2} ${BSPLIT:=1}
: ${QB:=13} ${CHB:=100000} ${CHL:=1} ${WIN:=512}
export TWOGRID GSH JSH WMIN DLO DHI PLO MINR YFRAC LSC NR TRIPLE PERSIST ZEXT SPLIT PFK MINPW NOZ TCLOSE MINSPLIT BSPLIT QB
OUTR=$R/root_$NAME; test ! -e "$OUTR" || { echo "$OUTR exists"; exit 1; }; mkdir -p $OUTR/AMW
echo "== E emit $(date)"
/usr/bin/time -l nice -n 5 python3 $R/emit9q.py $WJ $DELTA $DUMP $R/DATA_$NAME.json 2>&1 || exit 1
echo "== V lever-1 intervals $(date)"
/usr/bin/time -l nice -n 5 python3 $B/arun/lever1_ivs.py $R/DATA_$NAME.json $R/IV_$NAME.json 2>&1 || exit 1
echo "== D data module $(date)"
( unset NR; IV=$R/IV_$NAME.json CHB=$CHB CHL=$CHL /usr/bin/time -l nice -n 5 python3 $R/make9qI.py $R/DATA_$NAME.json $NAME $OUTR 2>&1 ) || exit 1
echo "== I instance module $(date)"
( unset NR AMWIN; CLOSE=1 HELP=1 BSPLIT=1 DFAST=3 LETC=1 SIGSH=$YFRAC QB=$QB WIN=$WIN ZN=$ZEXT DATA=$R/DATA_$NAME.json PCOUT=$OUTR/AMW \
    /usr/bin/time -l nice -n 5 python3 $B/window/amg/genpcellQI.py rootR8f ${NAME}Inst 8 2>&1 ) || exit 1
echo "== done $(date)"
