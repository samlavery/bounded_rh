#!/usr/bin/env python3
"""swap_cert9.py MOPX9_skel.lean FULL.lean NAME WEIGHTS OUT.lean [--selftest]: drop an n-point certificate into the
n-generic skeleton MOPX9 (mk_skel9.py).

FULL: our assembler's single file for the certificate NAME (`assemble_am_tau.py … --final6 NAME --npts N`), containing
  `namespace AMW.Cert.NAME` … `end AMW.Cert.NAMEData`, the glue `NAME_cert_full` in `namespace AMW.Cert`, and
  `namespace RiemannFail` with `def W<N> : WCert <N>`, `W<N>_B`, `W<N>_adm` and `cert_AM`.
Steps:
  1. the certificate region (between the `-- SWAP BEGIN/END certificate` markers) is replaced by FULL's instance, data,
     glue and RiemannFail-through-cert_AM; the region's notice blocks are carried over verbatim;
  2. N, B and c are read from FULL (`def W<N> : WCert <N>`, `theorem W<N>_B`, `theorem cert_AM`);
  3. the final instantiation block (`-- SWAP final instantiation` … `end Opeth.AMFinal`) is regenerated for
     OpethN.ActualDefect at n = N with RiemannFail.W<N>, W<N>_adm, W<N>_B, cert_AM, and κ = (H⁻ − B)/(1 − c) in lowest
     terms; the κ literal of `am_export_candidate_exact` is replaced (the spaced form only: notice blocks quote Arun's
     κ verbatim);
  4. the change notice's placeholders are filled.
Checks: N ≥ 2, c ≤ 1/64 (AMMatching.close_pair_block_bound), κ > 66812491/99194876 (unless --selftest)."""
import re, sys
from fractions import Fraction as F

skel_p, full_p, NAME, WEIGHTS, out_p = sys.argv[1:6]
S = open(skel_p, encoding="utf-8").read().split("\n")
U = open(full_p, encoding="utf-8").read().split("\n")
RECORD = F(66812491, 99194876)


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
code = [l for l in code if l.strip() and not l.strip().startswith("--")]
out = []; depth = 0
for l in code:
    s = l.strip()
    if depth > 0 or s.startswith("/-"):
        depth += l.count("/-") - l.count("-/"); continue
    out.append(l)
code = out

# ---- 2. N, B, c ----
mW = next(re.match(r"^def (W(\d+)) : WCert (\d+)", l) for l in U[r0:c1] if re.match(r"^def W\d+ : WCert \d+", l))
W, N = mW.group(1), int(mW.group(3))
assert int(mW.group(2)) == N and N >= 2
wb = next(l for l in U[r0:c1] if l.startswith(f"theorem {W}_B"))
ca = U[c0]
mB = re.search(rf"{W}\.B = \(?\((\d+) : ℝ\) / (\d+)\)?", wb)
mC = re.search(rf"\(\((\d+) : ℝ\) / (\d+)\) ≤ Fw {W} g", ca)
assert mB and mC, (wb, ca)
bn, bd = mB.groups(); cn, cd = mC.groups()
B, c = F(int(bn), int(bd)), F(int(cn), int(cd))
kappa = (F(67216841, 10 ** 8) - B) / (1 - c)
assert 0 < c <= F(1, 64), "c must lie in (0, 1/64] (AMMatching.close_pair_block_bound)"
if "--selftest" not in sys.argv:
    assert kappa > RECORD, f"κ = {kappa} does not beat the record {RECORD}"
K = f"{kappa.numerator} / {kappa.denominator}"

b = idx(S, r"^-- SWAP BEGIN certificate")
e = idx(S, r"^-- SWAP END certificate", b)
notices = []; k = b + 1
while k < e:
    if S[k].lstrip().startswith("/-"):
        dd = 0; j = k
        while j < e:
            dd += S[j].count("/-") - S[j].count("-/")
            if dd <= 0: break
            j += 1
        notices += S[k:j + 1]; k = j + 1
    else:
        k += 1
S = S[:b + 1] + notices + code + S[e:]

# ---- 3. the final instantiation ----
def inst(which, lhs):
    return (f"theorem actual_{which} :\n"
            f"    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,\n"
            f"      (({K} : ℝ) - ε) * {lhs} := by\n"
            f"  have h := OpethN.ActualDefect.actual_{which} (by norm_num : 2 ≤ {N}) RiemannFail.{W} RiemannFail.{W}_adm\n"
            f"    (by norm_num : (0 : ℝ) < {cn} / {cd}) (by norm_num) RiemannFail.{W}_B RiemannFail.cert_AM\n"
            f"  have e : ((67216841 / 100000000 - ({bn} : ℝ) / {bd}) / (1 - ({cn} : ℝ) / {cd}))\n"
            f"      = {K} := by norm_num\n"
            f"  simpa only [e] using h")
FINAL = ("-- SWAP final instantiation: n, the certificate's W / W_adm / W_B / cert_AM, c, B, κ\n"
         "namespace Opeth.AMFinal\n"
         + inst("dyadic", "(Zeta23.Ncount T (2 * T) : ℝ) ≤\n        Zeta23.N0star T (2 * T)") + "\n"
         + inst("cumulative", "(Zeta23.Ncount 0 T : ℝ) ≤\n        Zeta23.N0star 0 T") + "\n"
         + "end Opeth.AMFinal")
txt = "\n".join(S)
m = re.search(r"^-- SWAP final instantiation.*?^end Opeth\.AMFinal$", txt, flags=re.M | re.S)
assert m
txt = txt[:m.start()] + FINAL + txt[m.end():]
txt, n4 = re.subn(r"candidateKappa = \(66812491 / 99194876 : ℝ\)", f"candidateKappa = ({K} : ℝ)", txt)
assert n4 == 1, n4
# ---- 4. the change notice ----
for key, v in {"@@W@@": WEIGHTS, "@@B@@": f"{bn}/{bd}", "@@C@@": f"{cn}/{cd}",
               "@@KAPPA@@": f"{kappa.numerator}/{kappa.denominator} = {float(kappa):.9f}"}.items():
    assert txt.count(key) == 1, key
    txt = txt.replace(key, v)
if N != 8:
    txt = txt.replace("re-optimised eight-point certificate", f"re-optimised {N}-point certificate", 1)
open(out_p, "w", encoding="utf-8").write(txt)
print(f"{out_p}: {len(txt.encode())} B; NAME {NAME}, n = {N}, {W}; B = {bn}/{bd}, c = {cn}/{cd}; "
      f"κ = {kappa.numerator}/{kappa.denominator} = {float(kappa):.10f} (+{float(kappa - RECORD):.3e})")
print(f"spec: candidate {kappa.numerator} {kappa.denominator}, record {RECORD.numerator} {RECORD.denominator}")
