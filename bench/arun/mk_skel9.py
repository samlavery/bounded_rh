#!/usr/bin/env python3
"""mk_skel9.py MOPX_skel.lean Gen9Test.lean OUT.lean: the n-generic skeleton MOPX9.

Arun's eight-point-specific counting layer is replaced by the n-generic copy developed in Gen9Test.lean (compiled
against the MOPX olean, standard axioms):
  * Opeth.AMSparseDefect.seven_band_close        -> OpethN.band_close_n (band width n − 1, error 4(n−1)δ per point),
    with OpethN.card_near_le_k (Knausgard's Pantera.Transfer.card_near_le with k as a parameter);
  * Opeth.AMRemainder.{pressure_le, remainder_bound, block_remainder_bound} -> OpethN.*_n (WCert n, boundary (n−1)c);
  * Opeth.AMMatching.matching_defect_bound       -> OpethN.matching_defect_bound_n;
  * Opeth.AMCounting (cFloor/pressureSum/proposedQ, ActualDefectEstimate, defect_to_dyadic)
                                                 -> OpethN.Counting (constants c, B as parameters; κ = (H⁻ − B)/(1 − c);
                                                    δ ≤ c/(8(n−1)), C = 4(n−1) + 2 + c + B);
  * Opeth.AMActualDefect                         -> OpethN.ActualDefect (any admissible WCert n, c ∈ (0, 1/64]);
  * Opeth.AMFinal                                -> the instantiation for the certificate in the swap region (SWAP block).
Every section's notice block stays where it was. The export wrapper is unchanged (it calls Opeth.AMFinal.*)."""
import re, sys

skel_p, gen_p, out_p = sys.argv[1:4]
S = open(skel_p, encoding="utf-8").read()
G = open(gen_p, encoding="utf-8").read()


def cut(text, start_pat, end_pat, keep_end=True):
    a = re.search(start_pat, text, flags=re.M)
    assert a, start_pat
    b = re.search(end_pat, text[a.start():], flags=re.M)
    assert b, end_pat
    e = a.start() + (b.start() if keep_end else b.end())
    s = a.start()
    # a docstring directly above the removed declaration goes with it (mk_skel kept some docstrings that say "retain…")
    head = text[:s]
    if head.endswith("-/\n"):
        d = head.rfind("/--")
        if d >= 0 and "-/" not in head[d:-3] and (d == 0 or head[d - 1] == "\n"):
            s = d
    return text[:s] + text[e:]


# Arun's eight-point lemmas (the notice blocks and section openers stay)
S = cut(S, r"^theorem seven_band_close\b", r"^end Opeth\.AMSparseDefect$")
S = cut(S, r"^namespace Opeth\.AMRemainder$", r"^end Opeth\.AMRemainder\n", keep_end=False)
S = cut(S, r"^theorem matching_defect_bound\b", r"^end Opeth\.AMMatching$")
S = cut(S, r"^namespace Opeth\.AMCounting$", r"^end Opeth\.AMCounting\n", keep_end=False)
S = S.replace("-- SWAP constants: cFloor = c, pressureSum = B, proposedQ = κ\n", "")
S = cut(S, r"^namespace Opeth\.AMActualDefect$", r"^end Opeth\.AMActualDefect\n", keep_end=False)

# the generic layer (Gen9Test minus its import, its eight-point Final block and the axiom prints)
g0 = G.index("noncomputable section")
g1 = G.index("/-! the current eight-point certificate through the generic chain -/")
generic = G[g0:g1].rstrip() + "\n"
generic = "\n".join(l for l in generic.split("\n") if l.strip() and not l.strip().startswith("--"))
dropc = []; depth = 0
for l in generic.split("\n"):
    s = l.strip()
    if depth > 0 or s.startswith("/-"):
        depth += l.count("/-") - l.count("-/"); continue
    dropc.append(l)
generic = "\n".join(dropc) + "\n"

FINAL = """-- SWAP final instantiation: n, the certificate's W / W_adm / W_B / cert_AM, c, B, κ
namespace Opeth.AMFinal
theorem actual_dyadic :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((66812491 / 99194876 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) := by
  have h := OpethN.ActualDefect.actual_dyadic (by norm_num : 2 ≤ 8) RiemannFail.W8 RiemannFail.W8_adm
    (by norm_num : (0 : ℝ) < 805124 / 100000000) (by norm_num) RiemannFail.W8_B RiemannFail.cert_AM
  have e : ((67216841 / 100000000 - (404350 : ℝ) / 100000000) / (1 - (805124 : ℝ) / 100000000))
      = 66812491 / 99194876 := by norm_num
  simpa only [e] using h
theorem actual_cumulative :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((66812491 / 99194876 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0star 0 T := by
  have h := OpethN.ActualDefect.actual_cumulative (by norm_num : 2 ≤ 8) RiemannFail.W8 RiemannFail.W8_adm
    (by norm_num : (0 : ℝ) < 805124 / 100000000) (by norm_num) RiemannFail.W8_B RiemannFail.cert_AM
  have e : ((67216841 / 100000000 - (404350 : ℝ) / 100000000) / (1 - (805124 : ℝ) / 100000000))
      = 66812491 / 99194876 := by norm_num
  simpa only [e] using h
end Opeth.AMFinal
"""
# Arun's AMFinal namespace -> the generic layer (in its own sections) + the instantiation
m = re.search(r"^-- SWAP κ literals in actual_dyadic / actual_cumulative\nnamespace Opeth\.AMFinal\n.*?^end Opeth\.AMFinal\n",
              S, flags=re.M | re.S)
assert m
S = S[:m.start()] + "open Zeta23Ext.BridgeW\n" + FINAL + S[m.end():]
# the generic sections go right before the section that holds Arun's AMFinal notice
k = S.index("Concrete composition of the attributed published AM certificate")
k = S.rindex("section\n/-", 0, k)
S = S[:k] + generic + "end\n" if False else S[:k] + generic + S[k:]

# change notice
S = S.replace(
    "* Counting constants unchanged: H_W ≥ 67216841/10⁸ and the matching/pinching chain, so\n",
    "* Counting chain generalised to n-point certificates (OpethN, same proofs with band width n − 1:\n"
    "  error 4(n − 1)δ per point, boundary (n − 1)c, δ ≤ c/(8(n − 1)), C = 4(n − 1) + 2 + c + B, and a\n"
    "  parametrised copy of Kristian Muri Knausgard's card_near_le); Arun's eight-point instances replaced.\n"
    "* Counting constants otherwise unchanged: H_W ≥ 67216841/10⁸ and the matching/pinching chain, so\n")
open(out_p, "w", encoding="utf-8").write(S)
print(f"{out_p}: {len(S.encode())} B")
