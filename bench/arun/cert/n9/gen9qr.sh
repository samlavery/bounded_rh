#!/bin/bash
# bridge-port, 2026-10-11. Emission of an RCUT (finer root partition) 9-point tree as limb walks, no boundaries:
#   (E) emit9qr.py (emit9q on size9pr: the replay sees the RCUT root covers; exact re-verification on built tables)
#   (V) arun/lever1_ivs.py: the independent replay; every point's hull must pass tcheck
#   (D) make9qIL.py (limb-table walks, LIMB/WIN, one boundary-free walk per root)
#   (I) window/amg/genpcellQI.py (am-cert's lever-1 instance generator) with LIMB, WIN, SIGSH, QB, ZN
# Usage: WJ=... DELTA=... DUMP=... NAME=... RCUT=g:m [ZEXT=32 LSC=1024 YFRAC=16 QB=13 LIMB=16384 WIN=512] ./gen9qr.sh
# Output: n9/root_$NAME/AMW/{NAME}Data.lean, {NAME}Inst.lean; n9/DATA_$NAME.json, n9/IV_$NAME.json.  The modules get
# `set_option Elab.async false` after their imports by hand (Edit), before any build.
set -u
B=/Users/samuellavery/work/riemann-submission/bench
R=$B/arun/cert/n9
cd "$R"
export AMWIN=$B/window/rwin8.json
: ${TWOGRID:=1} ${GSH:=5} ${JSH:=5} ${WMIN:=8} ${DLO:=7} ${DHI:=8} ${PLO:=1} ${MINR:=0} ${YFRAC:=16} ${LSC:=1024} ${NR:=0}
: ${TRIPLE:=1} ${PERSIST:=1} ${ZEXT:=32} ${SPLIT:=pf} ${PFK:=8} ${MINPW:=256} ${NOZ:=1} ${TCLOSE:=1} ${MINSPLIT:=2} ${BSPLIT:=1}
: ${QB:=13} ${LIMB:=16384} ${WIN:=512}
export TWOGRID GSH JSH WMIN DLO DHI PLO MINR YFRAC LSC NR TRIPLE PERSIST ZEXT SPLIT PFK MINPW NOZ TCLOSE MINSPLIT BSPLIT QB RCUT
OUTR=$R/root_$NAME; test ! -e "$OUTR" || { echo "$OUTR exists"; exit 1; }
for f in DATA_$NAME.json IV_$NAME.json; do test ! -e "$R/$f" || { echo "$R/$f exists"; exit 1; }; done
mkdir -p $OUTR/AMW
echo "== E emit $(date)"
/usr/bin/time -l nice -n 5 python3 $R/emit9qr.py $WJ $DELTA $DUMP $R/DATA_$NAME.json 2>&1 || exit 1
echo "== V lever-1 intervals $(date)"
/usr/bin/time -l nice -n 5 python3 $B/arun/lever1_ivs.py $R/DATA_$NAME.json $R/IV_$NAME.json 2>&1 || exit 1
echo "== D data module $(date)"
( unset NR CHB CHL CH; PYTHONPATH=$B/eight/am8 IV=$R/IV_$NAME.json LIMB=$LIMB WIN=$WIN CSH=4 /usr/bin/time -l nice -n 5 python3 $R/make9qIL.py $R/DATA_$NAME.json $NAME $OUTR 2>&1 ) || exit 1
echo "== I instance module $(date)"
( unset NR AMWIN; CLOSE=1 HELP=1 BSPLIT=1 DFAST=3 LETC=1 SIGSH=$YFRAC QB=$QB WIN=$WIN LIMB=$LIMB ZN=$ZEXT CSH=4 DATA=$R/DATA_$NAME.json PCOUT=$OUTR/AMW \
    /usr/bin/time -l nice -n 5 python3 $B/window/amg/genpcellQI.py rootR8f ${NAME}Inst 8 2>&1 ) || exit 1
echo "== done $(date)"
