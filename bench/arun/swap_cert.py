#!/usr/bin/env python3
"""swap_cert.py SKEL.lean FULL.lean NAME WEIGHTS OUT.lean: drop a new eight-point certificate into the MOPX skeleton.

SKEL: MOPX_skel.lean (mk_skel.py), with its `-- SWAP` markers.
FULL: an assembled single file for the new certificate NAME (our run_n8 / assemble_am_tau.py output, `--final6 NAME
  --npts 8`), which contains
    * the instance and data sections `namespace AMW.Cert.NAME` … `end AMW.Cert.NAMEData`,
    * the glue `theorem NAME_G_rev / NAME_half / NAME_cert_full` in `namespace AMW.Cert`,
    * `namespace RiemannFail` with aW8, bW8, W8, W8_B, W8_a_nonneg, W8_bmin, W8_capacity, W8_adm, Fw_W8, cert_AM.
WEIGHTS: a short text for the change notice (e.g. "window-scope R8w2 (sha …)").

Steps:
  1. the certificate region between `-- SWAP BEGIN` and `-- SWAP END` is replaced by FULL's instance + data + glue
     sections and FULL's RiemannFail block cut after `cert_AM` (the τ/edge tail of FULL is not used here);
  2. B and c are read from FULL's `theorem W8_B` and `theorem cert_AM` statements, and the skeleton's `def cFloor` and
     `def pressureSum` get the same literals (so `simpa only [AMCounting.cFloor] using RiemannFail.cert_AM` still
     closes);
  3. κ = (67216841/10⁸ − B)/(1 − c) in lowest terms replaces `66812491 / 99194876` in CODE (the spaced form; notice
     blocks quote Arun's κ as `66812491/99194876` and stay verbatim);
  4. the change notice's @@W@@ / @@B@@ / @@C@@ / @@KAPPA@@ are filled.
The interface the rest of the file uses is exactly RiemannFail.{W8, W8_adm, W8_B, cert_AM}; checks: c ≤ 1/64 (needed by
AMMatching.close_pair_block_bound) and κ > 66812491/99194876 (the current record)."""
import re, sys
from fractions import Fraction as F

skel_p, full_p, NAME, WEIGHTS, out_p = sys.argv[1:6]
S = open(skel_p, encoding="utf-8").read().split("\n")
U = open(full_p, encoding="utf-8").read().split("\n")


def idx(lines, pat, start=0):
    for k in range(start, len(lines)):
        if re.match(pat, lines[k]): return k
    raise SystemExit(f"pattern not found: {pat}")


# ---- 1. the region from FULL ----
a = idx(U, rf"^namespace AMW\.Cert\.{NAME}$")
while a > 0 and re.match(r"^(set_option|noncomputable section|\s*$)", U[a - 1]): a -= 1   # blank lines too (assembler output)
d_end = idx(U, rf"^end AMW\.Cert\.{NAME}Data$", a)
g = idx(U, rf"^theorem {NAME}_cert_full\b", d_end)
g_end = idx(U, r"^end AMW\.Cert$", g)
r0 = idx(U, r"^namespace RiemannFail$", g_end)
while r0 > 0 and re.match(r"^(set_option|noncomputable section|open|\s*$)", U[r0 - 1]): r0 -= 1
c0 = idx(U, r"^theorem cert_AM\b", r0)
c1 = c0 + 1
while c1 < len(U) and not re.match(r"^(theorem|lemma|def|abbrev|end RiemannFail|noncomputable|section)\b", U[c1]): c1 += 1
code = U[a:g_end + 1] + ["end"] + U[r0:c1] + ["end RiemannFail", "end"]
# code lines only (FULL's region carries no notices of its own; comments and blank lines are dropped)
code = [l for l in code if l.strip() and not l.strip().startswith("--")]
dropc = []; depth = 0
for l in code:
    s = l.strip()
    if depth > 0 or s.startswith("/-"):
        depth += l.count("/-") - l.count("-/"); continue
    dropc.append(l)
code = dropc

wb = next(l for l in U[r0:c1] if l.startswith("theorem W8_B"))
ca = next(l for l in U[c0:c1] if l.startswith("theorem cert_AM"))
mB = re.search(r"W8\.B = \(\((\d+) : ℝ\) / (\d+)\)|W8\.B = \((\d+) : ℝ\) / (\d+)", wb)
bn, bd = [x for x in mB.groups() if x][:2]
mC = re.search(r"\(\((\d+) : ℝ\) / (\d+)\) ≤ Fw W8 g", ca)
cn, cd = mC.groups()
B, c = F(int(bn), int(bd)), F(int(cn), int(cd))
H = F(67216841, 10 ** 8)
kappa = (H - B) / (1 - c)
assert c <= F(1, 64), "c > 1/64: AMMatching.close_pair_block_bound needs c ≤ 1/64"
if "--selftest" not in sys.argv:   # the self-test re-inserts PC8C5BF itself, at κ equal to the record
    assert kappa > F(66812491, 99194876), f"κ = {kappa} does not beat the record 66812491/99194876"

b = idx(S, r"^-- SWAP BEGIN certificate")
e = idx(S, r"^-- SWAP END certificate", b)
# the skeleton's region may hold notice blocks (Arun's extraction provenance): carry them over verbatim, ahead of the code
notices = []; k = b + 1
while k < e:
    if S[k].lstrip().startswith("/-"):
        depth = 0; j = k
        while j < e:
            depth += S[j].count("/-") - S[j].count("-/")
            if depth <= 0: break
            j += 1
        notices += S[k:j + 1]; k = j + 1
    else:
        k += 1
T = S[:b + 1] + notices + code + S[e:]

# ---- 2. constants ----
txt = "\n".join(T)
txt, n1 = re.subn(r"^def cFloor : ℝ := .*$", f"def cFloor : ℝ := {cn} / {cd}", txt, flags=re.M)
txt, n2 = re.subn(r"^def pressureSum : ℝ := .*$", f"def pressureSum : ℝ := {bn} / {bd}", txt, flags=re.M)
txt, n3 = re.subn(r"^def proposedQ : ℝ := .*$", f"def proposedQ : ℝ := {kappa.numerator} / {kappa.denominator}", txt, flags=re.M)
# ---- 3. κ literals in code (spaced form) ----
txt, n4 = re.subn(r"66812491 / 99194876", f"{kappa.numerator} / {kappa.denominator}", txt)
assert (n1, n2, n3) == (1, 1, 1) and n4 >= 3, (n1, n2, n3, n4)
# ---- 4. the change notice ----
for k, v in {"@@W@@": WEIGHTS, "@@B@@": f"{bn}/{bd}", "@@C@@": f"{cn}/{cd}",
             "@@KAPPA@@": f"{kappa.numerator}/{kappa.denominator} = {float(kappa):.9f}"}.items():
    assert txt.count(k) == 1, k
    txt = txt.replace(k, v)
open(out_p, "w", encoding="utf-8").write(txt)
print(f"{out_p}: {len(txt.encode())} B; NAME {NAME}; B = {bn}/{bd}, c = {cn}/{cd}; "
      f"κ = {kappa.numerator}/{kappa.denominator} = {float(kappa):.10f} (+{float(kappa - F(66812491, 99194876)):.3e}); "
      f"code κ literals replaced: {n4}")
print(f"spec: candidate {kappa.numerator} {kappa.denominator}, record 66812491 99194876")
