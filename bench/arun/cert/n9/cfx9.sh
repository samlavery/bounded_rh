#!/bin/bash
# bridge-port, 2026-10-10. Counterfactual engine sizings for ANATOMY.md §0(C), on the calibrated root subset 2/5/9.
# Usage: WJ=<weights json> DELTA=<δ> TAG=<name> [variant env: LPACCEPT EXACTV EXACTC SO PFK ...] [SIZER=run9so.py] ./cfx9.sh
# The base settings are PC8C5BF's; any of them set in the caller's environment wins (e.g. PFK=16).
set -u
B=/Users/samuellavery/work/riemann-submission/bench
R=$B/arun/cert/n9
cd "$R"
export AMWIN=$B/window/rwin8.json
: ${TWOGRID:=1} ${GSH:=5} ${JSH:=5} ${WMIN:=8} ${DLO:=7} ${DHI:=8} ${PLO:=1} ${MINR:=0} ${YFRAC:=14} ${LSC:=256} ${NR:=0}
: ${TRIPLE:=1} ${PERSIST:=1} ${ZEXT:=8} ${SPLIT:=pf} ${PFK:=8} ${MINPW:=256} ${NOZ:=1} ${TCLOSE:=1} ${MINSPLIT:=2} ${BSPLIT:=1}
export TWOGRID GSH JSH WMIN DLO DHI PLO MINR YFRAC LSC NR TRIPLE PERSIST ZEXT SPLIT PFK MINPW NOZ TCLOSE MINSPLIT BSPLIT
export ROOTSEL=${ROOTSEL:-2,5,9}
# (lead's decision 10-10: under EXACTV, tangent positions are capped at the Lean convex-region limit p < 507904
#  (PCDZ tcheckZC / lever-1 ivOk: region k = (p + 16384) >> 15 < 16); the cap lives in size9so.py, so EXACTV runs use it)
if [ "${EXACTV:-}" = 1 ]; then export TCAP=${TCAP:-507904}; SZ=$R/${SIZER:-run9so.py}; else SZ=$R/${SIZER:-run9pz.py}; fi
echo "== cfx9 tag=$TAG wj=$WJ delta=$DELTA sizer=$SZ PFK=$PFK LPACCEPT=${LPACCEPT:-} EXACTV=${EXACTV:-} EXACTC=${EXACTC:-} SO=${SO:-} $(date)"
/usr/bin/time -l nice -n 5 python3 $SZ $WJ $DELTA 2>&1
echo "== done $(date)"
