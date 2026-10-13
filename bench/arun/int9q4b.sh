#!/usr/bin/env bash
# int9q4b.sh (bridge-port, 2026-10-11): INT9Q4 checks after assembly (int9q4.sh) and the hand-made master-of-puppets2 window
# edits (INT9Q4.lean). Waits for the PC9QB4 module build to pass, then:
#  1. private check of the unstripped INT9Q4.lean (candidate 166950417639218487/247859045000000000 = (H_W⁻ − B)/(1 − c) with
#     H_W⁻ = 672168410556873948/10¹⁸, B = 436674/10⁸, c = 856382/10⁸; record = master-of-puppets2's
#     167031227639218487/247987190000000000) in specroot_int9q4;
#  2. reachability on that olean (am-cert's ReachQ.lean, my copy cert/n9/strip4/ReachQ4.lean) -> strip4/unreachQ4.tsv;
#  3. am-cert's strip9.py with am-cert's keep.txt -> INT9Q4S.lean;
#  4. private check of INT9Q4S.lean in specroot_int9q4s, then the stages (nanoda/stage.sh).
set -u
B=~/work/riemann-submission/bench; A=$B/arun; S=$A/cert/n9/strip4
cd $B
for i in $(seq 1 240); do
  grep -q "PC9QB4_cert_full' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $A/cert/n9/lean_PC9QB4.log && break
  grep -q "error" $A/cert/n9/lean_PC9QB4.log && { echo "PC9QB4 build error; stop"; exit 1; }
  sleep 30
done
grep -q "PC9QB4_cert_full' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $A/cert/n9/lean_PC9QB4.log || { echo "PC9QB4 not ready; stop"; exit 1; }
test ! -e specroot_int9q4 && test ! -e specroot_int9q4s && test ! -e $A/INT9Q4S.lean || { echo "outputs exist"; exit 1; }
echo "== 1 private check INT9Q4 $(date)"
bash pyr/private_check_rec.sh arun/INT9Q4.lean CandINT9Q4 166950417639218487 247859045000000000 167031227639218487 247987190000000000 specroot_int9q4
grep -q "BUILD EXIT 0" specroot_int9q4/build_CandINT9Q4.log || { echo "INT9Q4 build failed"; grep -m5 -A6 "error" specroot_int9q4/build_CandINT9Q4.log; exit 1; }
echo "== 2 reachability $(date)"
ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt)
until mkdir .leanlock 2>/dev/null; do sleep 20; done
env LEAN_PATH=$PWD/specroot_int9q4:$ZP LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean $S/ReachQ4.lean 2>&1 | tail -3
rmdir .leanlock
test -s $S/unreachQ4.tsv || { echo "no unreach table"; exit 1; }
echo "== 3 strip $(date)"
python3 $A/strip9.py $A/INT9Q4.lean $S/unreachQ4.tsv $A/INT9Q4S.lean $S/keep.txt
echo "== 4 private check INT9Q4S $(date)"
bash pyr/private_check_rec.sh arun/INT9Q4S.lean CandINT9Q4S 166950417639218487 247859045000000000 167031227639218487 247987190000000000 specroot_int9q4s
grep -q "BUILD EXIT 0" specroot_int9q4s/build_CandINT9Q4S.log || { echo "INT9Q4S build failed"; grep -m8 -A4 "error" specroot_int9q4s/build_CandINT9Q4S.log; exit 1; }
bash nanoda/stage.sh CandINT9Q4S $PWD/specroot_int9q4s && rm -f nanoda/exp_CandINT9Q4S.ndjson
echo "== int9q4b done $(date)"
