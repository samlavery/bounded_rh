#!/usr/bin/env bash
# int9q5b.sh (bridge-port, 2026-10-11): INT9Q5 checks after assembly (int9q5.sh) and the hand-made master-of-puppets2 window
# edits (INT9Q5.lean). Waits for the PC9QB5C module build to pass, then:
#  1. private check of the unstripped INT9Q5.lean (candidate 166950417639218487/247859045000000000 = (H_W⁻ − B)/(1 − c) with
#     H_W⁻ = 672168410556873948/10¹⁸, B = 436674/10⁸, c = 856382/10⁸; record = master-of-puppets2's
#     167031227639218487/247987190000000000) in specroot_int9q5;
#  2. reachability on that olean (am-cert's ReachQ.lean, my copy cert/n9/strip5/ReachQ5.lean) -> strip5/unreachQ5.tsv;
#  3. am-cert's strip9.py with am-cert's keep.txt -> INT9Q5S.lean;
#  4. private check of INT9Q5S.lean in specroot_int9q5s, then the stages (nanoda/stage.sh).
set -u
B=~/work/riemann-submission/bench; A=$B/arun; S=$A/cert/n9/strip5
cd $B
for i in $(seq 1 240); do
  grep -q "PC9QB5C_cert_full' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $A/cert/n9/lean_PC9QB5C.log && break
  grep -q "error" $A/cert/n9/lean_PC9QB5C.log && { echo "PC9QB5C build error; stop"; exit 1; }
  sleep 30
done
grep -q "PC9QB5C_cert_full' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $A/cert/n9/lean_PC9QB5C.log || { echo "PC9QB5C not ready; stop"; exit 1; }
test ! -e specroot_int9q5 && test ! -e specroot_int9q5s && test ! -e $A/INT9Q5S.lean || { echo "outputs exist"; exit 1; }
echo "== 1 private check INT9Q5 $(date)"
bash pyr/private_check_rec.sh arun/INT9Q5.lean CandINT9Q5 166950417639218487 247859045000000000 167031227639218487 247987190000000000 specroot_int9q5
grep -q "BUILD EXIT 0" specroot_int9q5/build_CandINT9Q5.log || { echo "INT9Q5 build failed"; grep -m5 -A6 "error" specroot_int9q5/build_CandINT9Q5.log; exit 1; }
echo "== 2 reachability $(date)"
ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt)
until mkdir .leanlock 2>/dev/null; do sleep 20; done
env LEAN_PATH=$PWD/specroot_int9q5:$ZP LEAN_NUM_THREADS=2 nice -n 10 ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean $S/ReachQ5.lean 2>&1 | tail -3
rmdir .leanlock
test -s $S/unreachQ5.tsv || { echo "no unreach table"; exit 1; }
echo "== 3 strip $(date)"
python3 $A/strip9.py $A/INT9Q5.lean $S/unreachQ5.tsv $A/INT9Q5S.lean $S/keep.txt
echo "== 4 private check INT9Q5S $(date)"
bash pyr/private_check_rec.sh arun/INT9Q5S.lean CandINT9Q5S 166950417639218487 247859045000000000 167031227639218487 247987190000000000 specroot_int9q5s
grep -q "BUILD EXIT 0" specroot_int9q5s/build_CandINT9Q5S.log || { echo "INT9Q5S build failed"; grep -m8 -A4 "error" specroot_int9q5s/build_CandINT9Q5S.log; exit 1; }
bash nanoda/stage.sh CandINT9Q5S $PWD/specroot_int9q5s
# the lead's gate: full-file nanoda worst of >= 5 runs <= 6.0 GB (the stage run above is run 1; 4 more on the same export)
until mkdir .leanlock 2>/dev/null; do sleep 30; done
for k in 2 3 4 5; do
  /usr/bin/time -l nice -n 10 ~/work/riemann-submission/tools/nanoda/target/release/nanoda_bin nanoda/nanoda_cfg.json < nanoda/exp_CandINT9Q5S.ndjson > $A/cert/n9/rep/nanoda_INT9Q5S_$k.out 2> $A/cert/n9/rep/nanoda_INT9Q5S_$k.err
  printf "INT9Q5S nanoda run %d exit %d: " $k $?; grep -E "instructions retired|peak memory" $A/cert/n9/rep/nanoda_INT9Q5S_$k.err | awk '{printf "%s ", $1}'; echo
done
rmdir .leanlock
rm -f nanoda/exp_CandINT9Q5S.ndjson
echo "== int9q5b done $(date)"
