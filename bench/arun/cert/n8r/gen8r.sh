#!/bin/bash
# bridge-port, 2026-10-10. The 8-point fallback: window-scope's re-optimised n = 8 weights (cert/rwin8_reopt.json,
# B = 406753/1e8, eps_strong 0.008087608236768037) at δ = 3e-5 (cN 808736, κ = 8351261/12398908 = 0.6735481, +3.1e-7),
# with PC8C5BF's exact recipe (run8pz / emit8pz / make8pcC / genpcellC CLOSE=1 LETC=1 BSPLIT=1 DFAST=3, settings of
# DATA_try2cb_0.00005.json; reproduced byte-identically on PC8C5BF in cert/rep).  Certificate name PC8R.
# Usage: STAGE=size ./gen8r.sh   (full sizing, dump saved)
#        STAGE=gen  ./gen8r.sh   (emit, Data, Inst; only after the leaf count is checked against the rule)
#
# PRE-REGISTERED (written before any run):
#   rule (lead): if the full count is ≤ ~7.4k leaves, emit → Data/Inst → Lean build → axiom check; above, report and stop.
#   my prediction: 5.5k–7.0k leaves (PC8C5BF's weights at δ = 3e-5 gave 6,049 in cert/rep/scan_0.00003.log), so BUILD.
#   (outcome at δ = 3e-5: 18,731 leaves, root 18 = 11,962; refuted; stopped per the rule)
#
# PRE-REGISTERED, round 2 (δ = 5e-5, cN 808720, κ = 8351261/12398910; DELTA=0.00005 TAG=...):
#   (1) pre-check ROOTSEL=18: PASS iff root 18 ≤ ~500 leaves (PC8C5BF@5e-5: 225).  Prediction: 250–450, PASS.
#   (2) full sizing: build iff ≤ 7.4k leaves.  Prediction: 4.6k–5.6k leaves, about 2.2k–2.6k points; BUILD.
#   (3) if root 18 is not tame: report and stop.
#   (A first pre-check launch ran at δ = 3e-5 because this script still hard-coded D; it re-measured root 18 = 11,962,
#    identical to the full run, and overwrote dump_PC8R.pkl with that single-root dump.)
set -u
B=/Users/samuellavery/work/riemann-submission/bench
A8=$B/eight/am8
R=$B/arun/cert/n8r
WJ=$B/arun/cert/rwin8_reopt.json
D=${DELTA:-0.00003}
TAG=${TAG:-}
cd "$R"
export AMWIN=$B/window/rwin8.json
export TWOGRID=1 GSH=5 JSH=5 WMIN=8 DLO=7 DHI=8 PLO=1 MINR=0 YFRAC=14 LSC=256 NR=0 TRIPLE=1 PERSIST=1 ZEXT=8 \
       SPLIT=pf PFK=8 MINPW=256 NOZ=1 TCLOSE=1 MINSPLIT=2 BSPLIT=1
if [ "${STAGE:?}" = size ]; then
  echo "== S sizing $(date)"
  SAVE=$R/dump_PC8R$TAG.pkl /usr/bin/time -l nice -n 5 python3 $A8/run8pz.py $WJ $D 2>&1
elif [ "$STAGE" = gen ]; then
  echo "== E emit $(date)"
  /usr/bin/time -l nice -n 5 python3 $A8/emit8pz.py $WJ $D $R/dump_PC8R$TAG.pkl $R/DATA_PC8R.json 2>&1 || exit 1
  echo "== D data module $(date)"
  ( unset NR; PYTHONPATH=$A8 /usr/bin/time -l nice -n 5 python3 $A8/make8pcC.py $R/DATA_PC8R.json PC8R $R/root8 2>&1 ) || exit 1
  echo "== I instance module $(date)"
  ( unset NR AMWIN; CLOSE=1 LETC=1 BSPLIT=1 DFAST=3 DATA=$R/DATA_PC8R.json PCOUT=$R/root8/AMW /usr/bin/time -l nice -n 5 \
      python3 $A8/genpcellC.py rootR8f PC8RInst 7 2>&1 ) || exit 1
fi
echo "== done $(date)"
