#!/usr/bin/env bash
# retake8.sh NAME MODDIR "WEIGHTS ID" [TAG]: the 8-point retake, from bridge-port's certificate modules to a verified, staged
# file (am-cert, 2026-10-10).  NOT an upload: uploads are Sam's.
#   MODDIR holds NAMEInst.lean and NAMEData.lean (Data ends with the AMW.Cert NAME_cert_full glue).
#   1. root  arun/cert/r8/NAME_root/AMW: symlinks to rootR8f/AMW/*.lean + the two certificate modules
#   2. FULL  tauint/assemble_am_tau.py --final6 NAME --npts 8 (only its certificate text and RiemannFail W8 … cert_AM are used)
#   3. swap  swap_cert.py into MOPX_skel.lean (asserts c ≤ 1/64 and κ > 66812491/99194876; fills the change notice)
#   4. engine_check.py (inserts a missing engine module such as PCBias; stops on a stripped or drifted one in use)
#   5. size gate: ≤ 2,000,000 B (warn above 1,900,000)
#   6. private check in specroot_r8<name>: candidate κ, record 66812491/99194876; then the stages; then the
#      stage-by-stage instruction-ratio prediction against PC8C5BF's actual 2,319 s
# Env SELFTEST=1: allow κ = the record (the PC8C5BF dry run); the private check is skipped (spec would fail strictness).
set -euo pipefail
NAME=$1; MODDIR=$(cd "$2" && pwd); WID=$3; TAG=${4:-}
B=~/work/riemann-submission/bench; A=$B/arun; lc=$(echo "$NAME$TAG" | tr A-Z a-z)
R=$A/cert/r8/${NAME}${TAG}_root; FULL=$A/R8_${NAME}${TAG}_full.lean; SW=$A/R8_${NAME}${TAG}_swap.lean; OUT=$A/R8_${NAME}${TAG}.lean
SR=specroot_r8$lc; MOD=CandR8${NAME}${TAG}
for f in "$MODDIR/${NAME}Inst.lean" "$MODDIR/${NAME}Data.lean"; do test -s "$f" || { echo "missing $f"; exit 1; }; done
for p in "$R" "$FULL" "$SW" "$OUT" "$B/$SR"; do test ! -e "$p" || { echo "exists: $p"; exit 1; }; done
mkdir -p "$R/AMW"
for f in $B/window/rootR8f/AMW/*.lean; do bn=$(basename $f); case $bn in ${NAME}Inst.lean|${NAME}Data.lean) ;; *) ln -s $f "$R/AMW/$bn";; esac; done
cp "$MODDIR/${NAME}Inst.lean" "$MODDIR/${NAME}Data.lean" "$R/AMW/"
echo "== assemble $(date +%T)"
python3 $B/window/tauint/assemble_am_tau.py "$FULL" --root "../arun/cert/r8/${NAME}${TAG}_root" --roots "${NAME}Data,AMTail,Floor,Window" \
  --final6 "$NAME" --npts 8 --csrc $B/window/tauint/CSRC_PC8C5BF.txt | tail -2
echo "== swap $(date +%T)"
ST=""; [ "${SELFTEST:-0}" = 1 ] && ST="--selftest"
python3 $A/swap_cert.py $A/MOPX_skel.lean "$FULL" "$NAME" "$WID" "$SW" $ST | tee $A/R8_${NAME}${TAG}_swap.txt
read KN KD < <(grep '^spec:' $A/R8_${NAME}${TAG}_swap.txt | sed -E 's/^spec: candidate ([0-9]+) ([0-9]+),.*/\1 \2/')
echo "== engine $(date +%T)"
python3 $A/engine_check.py "$SW" "$R" "$NAME" "$OUT"
SZ=$(wc -c < "$OUT" | tr -d ' ')
echo "SIZE $OUT $SZ B (cap 2,000,000; watch 1,900,000); candidate $KN/$KD"
[ "$SZ" -le 2000000 ] || { echo "OVER THE 2,000,000 B CAP: stop"; exit 1; }
[ "$SZ" -le 1900000 ] || echo "SIZE WARN: over 1.90 MB"
grep -c "Copyright" "$OUT" | sed 's/^/Copyright occurrences: /'
if [ "${SELFTEST:-0}" = 1 ]; then echo "SELFTEST: stop before the private check"; exit 0; fi
cd $B
echo "== private check $(date +%T)"
bash pyr/private_check_rec.sh "${OUT#$B/}" "$MOD" "$KN" "$KD" 66812491 99194876 "$SR"
grep -q "BUILD EXIT 0" "$SR/build_$MOD.log" || { echo "BUILD FAILED"; grep -m5 -A6 error "$SR/build_$MOD.log"; exit 1; }
grep -q "REPLAY EXIT 0" "$SR/replay_$MOD.log" || { echo "REPLAY FAILED"; exit 1; }
echo "== stages $(date +%T)"
bash nanoda/stage.sh "$MOD" "$B/$SR"
rm -f "nanoda/exp_$MOD.ndjson"
python3 - "$MOD" "$SR" <<'PY'
import re, sys
mod, root = sys.argv[1], sys.argv[2]
def stats(p):
    t = i = rss = None
    for ln in open(p, errors='replace'):
        m = re.match(r'\s*([\d.]+) real', ln); t = float(m.group(1)) if m else t
        m = re.match(r'\s*(\d+)\s+instructions retired', ln); i = int(m.group(1)) if m else i
        m = re.match(r'\s*(\d+)\s+maximum resident set size', ln); rss = int(m.group(1)) if m else rss
    return t, i, rss
def st(mod, root):
    return {'build': stats(f'{root}/build_{mod}.log'), 'replay': stats(f'{root}/replay_{mod}.log'),
            'export': stats(f'nanoda/export_{mod}.err'), 'nanoda': stats(f'nanoda/nanoda_{mod}.err'),
            'closure': stats(f'nanoda/replayx_{mod}.err')}
def P(s): return 157 + 2 * s['build'] + 2.46 * (s['export'] + s['nanoda'] + s['closure'])
Rf = st('CandPC8C5BFTS', 'specroot_pc8c5bfts'); O = st(mod, root)
for k in O: print(f"{k:8s} {O[k][0]:7.1f} s  {O[k][1] / 1e12:6.3f}e12 instr  max RSS {O[k][2] / 1e9:5.2f} GB")
sc = {k: Rf[k][0] * O[k][1] / Rf[k][1] for k in Rf}
print(f"PREDICTED board ≈ {2319 * P(sc) / P({k: Rf[k][0] for k in Rf}):.0f} s (instruction-ratio vs PC8C5BF actual 2,319 s)")
PY
echo "== retake8 done $(date +%T)"
