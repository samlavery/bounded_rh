#!/bin/bash
# bridge-port, 2026-10-10. 9-point (Q = 8) sizing of window-scope's rounded lp9 weights (n9/rwin9_lp9.json, B = 437542/1e8,
# c_true 0.008593488739838) with PC8C5BF's sizing settings (closure TCLOSE=1, BSPLIT=1, Z8, fixed-width layout).
# Usage: DELTA=... TAG=... [ROOTSEL=...] [SAVE=1] ./size9.sh
#
# PRE-REGISTERED (written before any run):
#   prediction, delta 2e-4, all roots: about 13,000 leaves (range 11k-17k).  Basis: the earlier n = 9 sizing (rwin9_B440000,
#     delta 2e-4, closure, no BSPLIT) gave 17,164 leaves; BSPLIT cut root 2 by 24 % there and n = 8 by 21.7 %.
#     Points about 3,000-4,000 (n = 8: 2,166); w / d table cells 1,984 / 2,240 as at n = 8 (same kernel and settings).
#   scaling: delta 5e-4 and 1e-3 about 2-6 % fewer leaves than 2e-4 (earlier n = 9: delta 1e-3 was -3.6 %).
#   window-scope's 3-6x PC8C5BF (14k-28k): I predict the low end, about 2.8x.
#   decision: report counts as measured; a run that exceeds MAXL (default 4e6) or does not finish in 3 h is reported as such.
#
# PRE-REGISTERED, round 2 (window-scope's κ-for-leaves variants rwin9_t570/t562/t555, single near-binding basin;
#   WJ=<file> SIZER=run9pz.py DELTA=0.00005 ROOTSEL=2,5,9; estimate = subset × 3.44, the PC9L calibration):
#   lead's rule: BUILDABLE if the estimate is ≤ 11k leaves at gain ≥ +1.5e-5 over 0.6735478 (t570 only qualifies on gain).
#   my prediction: subset 2.3k–3.0k for each variant (PC9L subset 5,101 had 16 basins), estimate 8k–10k:
#   t570 BUILDABLE; t562 and t555 slightly fewer leaves than t570.
#   (outcome: refuted; subsets ≈ 4.0k, full t570 14,906 = 3.76 × subset)
#
# PRE-REGISTERED, round 3 (written 15:35, after launch and before any root finished; the heavier-pressure refuting test,
#   window-scope's rwin9_tP570.json, κ ≥ 0.673570, pressures maximised; WJ=rwin9_tP570.json SIZER=run9pz.py DELTA=0.00005
#   ROOTSEL=2,5,9; estimate = subset × 3.76):
#   rule (lead, SUBMISSION.md, updated before the result): REOPENS the 9-point route iff the estimate is ≲ 8k leaves;
#     8k–11k "not enough"; otherwise closed for this design.
#   the claim under test (mine): at n = 9 the leaf count is set by the bulk minorant reach, not by basin structure or the
#     linear part; it is refuted if heavier pressure drops leaves well over 15 % against t570 (subset 3,966).
#   my prediction: subset 3.4k–4.2k, estimate 12.8k–15.8k: NOT reopened.
#   secondary rwin9_tPs570.json: did not start; its b_0 = 26333 puts S_0 = cN·SC/b_0 ≈ 1.098e6 > KB = 2^20 (the
#     Lean root cover needs every b_r ≥ cN/32 in units of 1e-8; here 27,575).
set -u
B=/Users/samuellavery/work/riemann-submission/bench
A8=$B/eight/am8
R=$B/arun/cert/n9
cd "$R"
export AMWIN=$B/window/rwin8.json
export TWOGRID=1 GSH=5 JSH=5 WMIN=8 DLO=7 DHI=8 PLO=1 MINR=0 YFRAC=14 LSC=256 NR=0 TRIPLE=1 PERSIST=1 ZEXT=8 \
       SPLIT=pf PFK=8 MINPW=256 NOZ=1 TCLOSE=1 MINSPLIT=2 BSPLIT=1
D=${DELTA:?}
TAG=${TAG:?}
[ "${SAVE:-0}" = 1 ] && export SAVE=$R/dump_$TAG.pkl || unset SAVE
echo "== size9 delta=$D tag=$TAG rootsel=${ROOTSEL:-all} $(date)"
SZ=${SIZER:-$A8/run8pz.py}     # SIZER=$R/run9pz.py: the S_r < KB variant (needed at n = 9: gap 0's S hit KB = 2^20)
WJ=${WJ:-$R/rwin9_lp9.json}
echo "window json $WJ"
/usr/bin/time -l nice -n 5 python3 $SZ $WJ $D 2>&1
echo "== done $(date)"
