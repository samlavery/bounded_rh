#!/usr/bin/env python3
"""(copy of gen_tail_w.py without the header writer) Bridge glue for a weighted n-point certificate checked by checker_<NAME>: WCert data, admissibility,
Fw expansion, the certificate from <NAME>Data.cert, n_point_bound_w', the exact constant, and kappa.
Usage: gen_tail_w.py <params file> ; writes tail_<NAME>.lean and prints kappa."""
import sys, math
from fractions import Fraction as Fr
Q, SA, aN, bN, cN, NAME = open(sys.argv[1]).read().split()[:6]
import os as _os
HALF = _os.environ.get("HALF") == "1"
_QI = int(Q); _X = [f"x{r}" for r in range(_QI)]
CERTFULL = (f"""theorem G_rev ({' '.join(_X)} : ℝ) : {NAME}.G {' '.join(reversed(_X))} = {NAME}.G {' '.join(_X)} := by
  unfold {NAME}.G; ring_nf

/-- the half-space certificate, completed by reflection (the weights are symmetric) -/
theorem cert_full : ∀ {' '.join(_X)} : ℝ, {' → '.join(f'0 ≤ {v}' for v in _X)} → ({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(_X)} := by
  intro {' '.join(_X)} {' '.join(f'h{r}' for r in range(_QI))}
  rcases lt_or_ge {_X[_QI-1]} {_X[0]} with hlt | hle
  · rcases {NAME}Data.cert {' '.join(reversed(_X))} {' '.join(f'h{r}' for r in reversed(range(_QI)))} with h | h
    · rw [← G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases {NAME}Data.cert {' '.join(_X)} {' '.join(f'h{r}' for r in range(_QI))} with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)
""" if HALF else "")
Q = int(Q); SA = int(SA); aN = [int(x) for x in aN.split(",")]; bN = [int(x) for x in bN.split(",")]; cN = int(cN)
n = Q + 1
SUMN = {3: 'Fin.sum_univ_three', 4: 'Fin.sum_univ_four', 5: 'Fin.sum_univ_five', 6: 'Fin.sum_univ_six', 7: 'Fin.sum_univ_seven', 8: 'Fin.sum_univ_eight'}[n]
AWALL = ', '.join(f'aW_{i}_{j}' for i in range(n) for j in range(n))
SUMQ = {2: 'Fin.sum_univ_two', 3: 'Fin.sum_univ_three', 4: 'Fin.sum_univ_four', 5: 'Fin.sum_univ_five', 6: 'Fin.sum_univ_six', 7: 'Fin.sum_univ_seven'}[Q]
pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
c = Fr(cN, SA); B = sum(Fr(b, SA) for b in bN); m = (n - 1) + int(1 / c)
assert c * (m - (n - 1)) <= 1 < c * (m - (n - 2))
H_lo = Fr(3, 2) - Fr(8274993018, 10**10); H_hi = Fr(3, 2) - Fr(8274992907, 10**10)
# Phi_w'(n, c, m, B) = (H - B(m-(n-1))/m) / (1 - c(m-(n-1))/m) = (m H - B(m-(n-1))) / (m - c(m-(n-1)))
num_H = m; num_0 = -B * (m - (n - 1)); den = m - c * (m - (n - 1))
# as integers: Phi = (P * H - R) / D with P, R, D integers
L = math.lcm(num_0.denominator, den.denominator)
P = num_H * L; R = -num_0 * L; D = den * L
assert P.denominator == 1 and R.denominator == 1 and D.denominator == 1
P, R, D = int(P), int(R), int(D)
g = math.gcd(math.gcd(P, R), D); P //= g; R //= g; D //= g
phi = lambda H: (P * H - R) / D
kappa = Fr(int(phi(H_lo) * 10**7), 10**7)
assert kappa > H_hi and kappa < phi(H_lo)
print(f"n={n} c={c} m={m} B={B} Phi=({P}*H-{R})/{D} = {float(phi(H_lo)):.10f} kappa={kappa} = {float(kappa):.7f}")
amat = [[0] * n for _ in range(n)]
for (i, j), v in zip(pairs, aN): amat[i][j] = v
def row(i): return "![" + ", ".join(f"({amat[i][j]} : ℝ) / {SA}" if amat[i][j] else "0" for j in range(n)) + "]"
bmin = min(bN)
G = [f"(g {r})" for r in range(Q)]
def tg(i, j): return " + ".join(G[i:j])
out = f'''
/-! ###### the {n}-point weighted bound from the checked certificate `{NAME}` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW Zeta23Ext.Bridge.ThreePoint

/-- the pair weights `a_ij` (zero unless `i < j`), over `{SA}` -/
def aW : Fin {n} → Fin {n} → ℝ
{chr(10).join(f"  | {i}, {j} => ({amat[i][j]} : ℝ) / {SA}" for (i, j) in pairs)}
  | _, _ => 0

/-- the per-gap pressures, over `{SA}` -/
def bW : Fin {Q} → ℝ
{chr(10).join(f"  | {r} => ({bN[r]} : ℝ) / {SA}" for r in range(Q))}

def WW : WCert {n} := ⟨aW, bW⟩

{chr(10).join(f"theorem aW_{i}_{j} : aW {i} {j} = ({amat[i][j]} : ℝ) / {SA} := rfl" if amat[i][j] else f"theorem aW_{i}_{j} : aW {i} {j} = 0 := rfl" for i in range(n) for j in range(n))}
{chr(10).join(f"theorem bW_{r} : bW {r} = ({bN[r]} : ℝ) / {SA} := rfl" for r in range(Q))}

theorem WW_B : WW.B = ({B.numerator} : ℝ) / {B.denominator} := by
  show (∑ r : Fin {Q}, bW r) = _
  norm_num [{SUMQ}, {", ".join(f"bW_{r}" for r in range(Q))}]

theorem WW_a_nonneg : ∀ i j, 0 ≤ WW.a i j := by
  intro i j
  unfold WW
  match i, j with
{chr(10).join(f"  | {i}, {j} => show (0:ℝ) ≤ aW {i} {j}; norm_num [aW_{i}_{j}]" for i in range(n) for j in range(n))}

theorem WW_bmin : ∀ r, (({bmin} : ℝ) / {SA}) ≤ WW.b r := by
  intro r
  unfold WW
  match r with
{chr(10).join(f"  | {r} => show (({bmin} : ℝ) / {SA}) ≤ bW {r}; norm_num [bW_{r}]" for r in range(Q))}

theorem WW_capacity : ∀ s : ℕ, WW.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass WW
  rcases lt_or_ge s {n} with hs | hs
  · interval_cases s <;> simp (config := {{ decide := true }}) only [{SUMN}, {AWALL}, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin {n}, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num

theorem WW_adm : WW.Adm := ⟨WW_a_nonneg, fun r => le_trans (by norm_num) (WW_bmin r), WW_capacity⟩

private lemma sumQ (f : Fin ({n} - 1) → ℝ) : ∑ i, f i = {" + ".join(f"f {r}" for r in range(Q))} := by
  show ∑ i : Fin {Q}, f i = {" + ".join(f"f {r}" for r in range(Q))}
  exact {SUMQ} f

/-- `Fw WW` written out on the gaps: it is the checker's functional `{NAME}.G`. -/
theorem Fw_WW (g : Fin ({n} - 1) → ℝ) : Fw WW g = {NAME}.G {" ".join(G)} := by
  show (∑ r : Fin {Q}, bW r * g r) + (∑ i : Fin {n}, ∑ j : Fin {n}, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN {n} g j - ptsN {n} g i) else 0) = _
  unfold {NAME}.G ptsN
  simp only [sumQ, {SUMN}, {SUMQ}, Fin.isValue, {AWALL}, {", ".join(f"bW_{r}" for r in range(Q))}]
  norm_num [{NAME}.SA]
  try ring

{CERTFULL}
/-- the certificate hypothesis of `n_point_bound_w'` at `n = {n}` -/
theorem cert_WW : ∀ g : Fin ({n} - 1) → ℝ, (∀ i, 0 ≤ g i) → ({cN} : ℝ) / {SA} ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := {"cert_full" if HALF else NAME + "Data.cert"} {" ".join(G)} {" ".join(f"(hg {r})" for r in range(Q))}
  simp only [{NAME}.cN, {NAME}.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' {n} c {m} B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' {n} (({cN} : ℝ) / {SA}) {m} (({B.numerator} : ℝ) / {B.denominator})
    = ({P} * HD 1 - {R}) / {D} := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The {n}-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (({P} * HD 1 - {R}) / {D} - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' {n} (({cN} : ℝ) / {SA}) {m} WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < ({bmin} : ℝ) / {SA}) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ ({P} * HD 1 - {R}) / {D} := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < {D})]
  linarith [HD_one_bounds.1]

/-- The dyadic bound at the candidate rational, in the library's vocabulary. -/
theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := bound_WW ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star T (2 * T)
  have h0 : (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ (({P} * HD 1 - {R}) / {D} - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [candidateKappa_le]) hN
  linarith

/-- The cumulative form, through the library's dyadic-to-cumulative wrapper. -/
theorem cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) dyadic

/-- Strict improvement over the record.  The board pins `currentRecordKappa` as the exact rational
of the last accepted candidate, so the comparison is decided by `norm_num`; the second branch covers
the original closed form `2 - 1/cMT = HD 1`, through `cStar_one_eq_cMT` and the enclosure of `HD 1`. -/
theorem strict : currentRecordKappa < candidateKappa := by
  unfold currentRecordKappa candidateKappa
  first
    | (norm_num; done)
    | (rw [← cStar_one_eq_cMT]
       have h := HD_one_bounds.2
       unfold Zeta23.ThmD.HD at h
       linarith)

end RiemannFail

end

/-! ###### the three scored theorems, statements as generated by the trusted template ###### -/

noncomputable section

/-- The submitted bound is strictly larger than the current formal record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa :=
  RiemannFail.strict

/-- The candidate proves a larger unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  RiemannFail.dyadic

/-- The same unconditional bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  RiemannFail.cumulative

end
'''
TAIL_AX = "\n#print axioms candidate_strict_improvement\n#print axioms candidate_critical_line_bound\n#print axioms candidate_critical_line_bound_cumulative\n"
open(f"tail_{NAME}.lean", "w", encoding="utf-8").write(out + TAIL_AX)
open(f"kappa_{NAME}.txt", "w").write(f"{kappa.numerator} {kappa.denominator} {P} {R} {D}\n")
print(f"wrote tail_{NAME}.lean, kappa_{NAME}.txt")
