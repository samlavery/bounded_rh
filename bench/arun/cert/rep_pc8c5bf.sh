#!/bin/bash
# bridge-port, 2026-10-10. Reproduction of the PC8C5BF certificate pipeline on PC8C5BF's own weights.
#
# PRE-REGISTERED (written before any run):
#   inputs : window/rwin8.json (R8 window cnum, W8 weights aN/bN, B = 404350, eps_strong 0.008051650008812845), delta 5e-5,
#            the sizing env recorded in eight/am8/DATA_try2cb_0.00005.json "settings", plus AMWIN = rwin8.json (amk's
#            default window is NOT R8, and AMWIN is not recorded in "settings").
#   stages : (S) eight/am8/run8pz.py (size8pz sizing, dump)  (E) eight/am8/emit8pz.py (replay + re-verify + DATA json)
#            (D) eight/am8/make8pcC.py (Data module)       (I) eight/am8/genpcellC.py CLOSE=1 LETC=1 BSPLIT=1 DFAST=3 (Inst)
#   PASS   : cN 805124; leaves 4598 (kinds 6: 4419, 0: 179); splits 4566; points 2166; walk bits 1132496;
#            DATA json equal to DATA_try2cb_0.00005.json on walks, tables, covers, counts;
#            Data / Inst modules byte-identical to rootR8f/AMW/PC8C5BF{Data,Inst}.lean, or every difference explained.
#   PREDICTION: S/E reproduce exactly (deterministic integer pipeline).  Data identical.  Inst identical unless the
#            post-10-08 edits to genpcellC.py (edge windows, NOREFL) changed default output; I predict identical.
#   Outputs go only under bench/arun/cert/rep (PCOUT for Inst, ROOT=../arun/cert/rep/root for Data, cwd for strays).
set -u
B=/Users/samuellavery/work/riemann-submission/bench
A8=$B/eight/am8
R=$B/arun/cert/rep
cd "$R"
export AMWIN=$B/window/rwin8.json
export TWOGRID=1 GSH=5 JSH=5 WMIN=8 DLO=7 DHI=8 PLO=1 MINR=0 YFRAC=14 LSC=256 NR=0 TRIPLE=1 PERSIST=1 ZEXT=8 \
       SPLIT=pf PFK=8 MINPW=256 NOZ=1 TCLOSE=1 MINSPLIT=2 BSPLIT=1
D=${DELTA:-0.00005}
TAG=${TAG:-rep}
echo "== S sizing delta=$D $(date)"
SAVE=$R/dump_$TAG.pkl /usr/bin/time -l nice -n 5 python3 $A8/run8pz.py $B/window/rwin8.json $D 2>&1
[ "${SIZEONLY:-0}" = 1 ] && exit 0
echo "== E emit $(date)"
/usr/bin/time -l nice -n 5 python3 $A8/emit8pz.py $B/window/rwin8.json $D $R/dump_$TAG.pkl $R/DATA_$TAG.json 2>&1
echo "== D data module $(date)"
( unset NR; PYTHONPATH=$A8 /usr/bin/time -l nice -n 5 python3 $A8/make8pcC.py $R/DATA_$TAG.json PC8C5BF ../arun/cert/rep/root 2>&1 )
echo "== I instance module $(date)"
( unset NR AMWIN; CLOSE=1 LETC=1 BSPLIT=1 DFAST=3 DATA=$R/DATA_$TAG.json PCOUT=$R/root/AMW /usr/bin/time -l nice -n 5 \
    python3 $A8/genpcellC.py rootR8f PC8C5BFInst 7 2>&1 )
echo "== done $(date)"
