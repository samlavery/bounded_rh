#!/bin/bash
# bridge-port, 2026-10-11. full9.sh with a ROOTSEL subset kept (full9s.sh): a saved dump of the selected roots only, for merging.
# Usage: WJ=<weights json> DELTA=<δ> TAG=<name> [engine env: LSC YFRAC EXACTV ...] [SIZER=run9pz.py] ./full9.sh
# The base settings are PC8C5BF's; any set in the caller's environment wins.  Dump: n9/dump_$TAG.pkl.
set -u
B=/Users/samuellavery/work/riemann-submission/bench
R=$B/arun/cert/n9
cd "$R"
export AMWIN=$B/window/rwin8.json
: ${TWOGRID:=1} ${GSH:=5} ${JSH:=5} ${WMIN:=8} ${DLO:=7} ${DHI:=8} ${PLO:=1} ${MINR:=0} ${YFRAC:=14} ${LSC:=256} ${NR:=0}
: ${TRIPLE:=1} ${PERSIST:=1} ${ZEXT:=8} ${SPLIT:=pf} ${PFK:=8} ${MINPW:=256} ${NOZ:=1} ${TCLOSE:=1} ${MINSPLIT:=2} ${BSPLIT:=1}
export TWOGRID GSH JSH WMIN DLO DHI PLO MINR YFRAC LSC NR TRIPLE PERSIST ZEXT SPLIT PFK MINPW NOZ TCLOSE MINSPLIT BSPLIT
: ${ROOTSEL:?ROOTSEL required}; export ROOTSEL
export SAVE=$R/dump_$TAG.pkl
test ! -e "$SAVE" || { echo "$SAVE exists"; exit 1; }
# (lead's decision 10-10: under EXACTV, tangent positions are capped at the Lean convex-region limit p < 507904)
if [ "${EXACTV:-}" = 1 ]; then export TCAP=${TCAP:-507904}; SZ=$R/${SIZER:-run9so.py}; else SZ=$R/${SIZER:-run9pz.py}; fi
echo "== full9 tag=$TAG wj=$WJ delta=$DELTA sizer=$SZ LSC=$LSC YFRAC=$YFRAC EXACTV=${EXACTV:-} LPACCEPT=${LPACCEPT:-} $(date)"
/usr/bin/time -l nice -n 5 python3 $SZ $WJ $DELTA 2>&1
echo "== done $(date)"
