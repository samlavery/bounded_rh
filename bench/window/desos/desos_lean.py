#!/usr/bin/env python3
"""desos_lean.py DATA.json OUT.lean MODNAME : the Lean data module for AMW.DESOS (integer Fejér–Riesz certificate)."""
import json, sys
d = json.load(open(sys.argv[1])); out = sys.argv[2]; mod = sys.argv[3]
n, E, Y, D, A, MZ = d['n'], d['E'], d['Y'], d['D'], d['A'], d['MZ']
assert len(Y) == n and len(A) == n and MZ > 0
def lst(v): return '[' + ', '.join(str(x) for x in v) + ']'
txt = f'''import AMW.DESOS

/-! ###### AMW/{mod} — the cosine polynomial `C` and its Fejér–Riesz certificate (am-cert)

`C(θ) = y₀ + 2 Σ_{{1≤b<{n}}} y_b cos(bθ)` with `y_b = YL[b]/E` (source: `{d['source'].split('/')[-1]}`, `y₀` lifted by
{d['lift']}). The factor `a_j = AL[j]/D` (`D = 10^{len(str(D)) - 1}`) is the minimum-phase Fejér–Riesz factor of `C − {d['keep']}`
(cepstral method), rounded; the exact integer check `chk` gives `C(θ) ≥ mC = MZ/(E·D²) > 0` for every real `θ`. ###### -/

noncomputable section

open Finset Real

namespace AMW.DESOS.{mod}

/-- the degree bound: `C` has the cosines `0 … {n - 1}` -/
def nC : ℕ := {n}
/-- the common denominator of the `y_b` -/
def EC : ℕ := {E}
/-- the denominator of the factor's coefficients -/
def DC : ℕ := {D}
/-- the coefficients `y_b`, over `EC` -/
def YL : List ℤ := {lst(Y)}
/-- the Fejér–Riesz factor's coefficients `a_j`, over `DC` -/
def AL : List ℤ := {lst(A)}
/-- the certified margin, over `EC · DC²` -/
def MZC : ℤ := {MZ}

def YC (k : ℕ) : ℤ := YL.getD k 0
def AC (j : ℕ) : ℤ := AL.getD j 0

theorem AC_zero : ∀ j, nC ≤ j → AC j = 0 := by
  intro j hj
  unfold AC
  exact List.getD_eq_default _ _ (by simpa [AL, nC] using hj)

/-- **the certificate check** (exact integer arithmetic: {n * n} products) -/
theorem chk : MZC ≤ resZ YC AC EC DC nC 0 - 2 * ∑ k ∈ Ico 1 nC, |resZ YC AC EC DC nC k| := by
  decide +kernel

/-- the coefficients of `C` -/
def yC (k : ℕ) : ℝ := (YC k : ℝ) / EC

/-- **the cosine polynomial** `C(θ) = y₀ + 2 Σ_{{1≤b<{n}}} y_b cos(bθ)` -/
def Ccos (θ : ℝ) : ℝ := yC 0 + 2 * ∑ b ∈ Ico 1 {n}, yC b * cos (b * θ)

/-- the certified lower bound of `C` -/
def mC : ℝ := (MZC : ℝ) / ((EC : ℝ) * (DC : ℝ) ^ 2)

theorem mC_pos : 0 < mC := by
  unfold mC MZC EC DC; positivity

/-- **`C ≥ mC` on ℝ** -/
theorem Ccos_ge (θ : ℝ) : mC ≤ Ccos θ :=
  cos_poly_ge_int YC AC EC DC nC (by norm_num [EC]) (by norm_num [DC]) AC_zero MZC chk θ

/-- **`C > 0` on ℝ** -/
theorem Ccos_pos (θ : ℝ) : 0 < Ccos θ := mC_pos.trans_le (Ccos_ge θ)

/-- **`C ≥ 0` on ℝ** -/
theorem Ccos_nonneg (θ : ℝ) : 0 ≤ Ccos θ := (Ccos_pos θ).le

end AMW.DESOS.{mod}

end
'''
open(out, 'w').write(txt)
print(out, len(txt.encode()), 'bytes')
