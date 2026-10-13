#!/usr/bin/env bash
# stage.sh MOD LEANPATH_PREFIX : the board verifier's post-build stages on an already-compiled solution module, timed:
#   lean4export (b18d673) of the comparator targets -> nanoda_bin (4183202, comparator's config) -> Lean replay of the
#   whole exported closure into an empty environment (replayx = comparator runKernel). Holds the shared lean lock.
set -u
cd ~/work/riemann-submission/bench
MOD=$1; PFX=$2
until mkdir .leanlock 2>/dev/null; do echo "[stage] waiting $(date +%T)"; sleep 30; done
trap 'rmdir .leanlock 2>/dev/null' EXIT
ZP=$(cut -d: -f2- specroot/LEAN_PATH.txt)
T=~/work/riemann-submission/tools
EXP=nanoda/exp_$MOD.ndjson
TG="Nat String String.mk Char Quot Quot.mk Quot.lift Quot.ind candidate_strict_improvement candidate_critical_line_bound candidate_critical_line_bound_cumulative propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce"
echo "== $MOD export"
/usr/bin/time -l env LEAN_PATH=$PFX:$ZP LEAN_ABORT_ON_PANIC=1 nice -n 10 $T/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export $MOD -- $TG > $EXP 2> nanoda/export_$MOD.err
echo "export exit $?"; grep -E " real|peak memory" nanoda/export_$MOD.err; ls -la $EXP | awk '{print "export bytes", $5}'
echo "== $MOD nanoda"
/usr/bin/time -l nice -n 10 $T/nanoda/target/release/nanoda_bin nanoda/nanoda_cfg.json < $EXP > nanoda/nanoda_$MOD.out 2> nanoda/nanoda_$MOD.err
echo "nanoda exit $?"; tail -3 nanoda/nanoda_$MOD.out; grep -E " real|peak memory" nanoda/nanoda_$MOD.err
echo "== $MOD lean replay (full closure)"
/usr/bin/time -l nice -n 10 $T/replayx/.lake/build/bin/replayx $EXP 2> nanoda/replayx_$MOD.err
echo "replayx exit $?"; grep -E " real|peak memory" nanoda/replayx_$MOD.err
