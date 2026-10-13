import AMW.PCell3HR

/-! ###### an end-to-end root cover of the Q = 3 polytope layer (bridge-port), canonical-Huffman walk

`cN = 40000`, empty tables.  Each gap's one-dimensional cover of `[1/2, Smax_r)` is a single bad segment (the linear part
pays from `Smax_r` on: `cN · SC ≤ b_r · Smax_r`; the window pays below `1/2`), so there is one root cell,
`[16384, 41175] × [16384, 22243] × [16384, 41175]`, which the walk closes with one plain leaf (the linear part alone).
`cert` is the certificate on every point with nonnegative gaps. ###### -/

set_option maxRecDepth 100000

noncomputable section

namespace AMW.Cert.PCell3HRI

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PCell3HR

def TOPZ : ℕ := 0
def BKZ (_ : ℕ) : ℕ := 0
def TOPDZ : ℕ := 0
def BKDZ (_ : ℕ) : ℕ := 0
def PTZ (_ : ℕ) : ℕ := 0
def REGZ : ℕ × ℕ × List (List ℕ) :=
  (2037037919005230987192162416774720086405554702674251026342456770209302840312462675557744641, 0, [])

theorem lbZ : LBSound TOPZ BKZ := lb_sound (fun j _ => rfl) (by decide +kernel)
theorem lbDZ : LBSoundD TOPDZ BKDZ := lbDr_sound (fun j _ => rfl) (by decide +kernel)
theorem ptZ : PT3Sound PTZ := pt3_sound (fun j _ => rfl)
theorem hRZ : rgOk REGZ = true := by decide +kernel

def COV : List (List (ℕ × ℕ × Bool)) := [[(16384, 41175, false)], [(16384, 22243, false)], [(16384, 41175, false)]]
def SMAX (r : ℕ) : ℕ := [41175, 22243, 41175].getD r 0

/-- the root cell: one leaf (bit 0 clear, minorant kind, the three non-adjacent constant codes `000`, the closing `0`: 6 bits) -/
theorem root_walk : U (walk TOPZ BKZ TOPDZ BKDZ PTZ REGZ 1 1 1)
    ⟨16384, 41175, 16384, 22243, 16384, 41175, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩ = 7 := by
  decide +kernel

theorem run : ∀ idx : ℕ → ℕ, (∀ r < 3, idx r < (badOf (COV.getD r [])).length) →
    Covered (rootCl 3 3 1099511627776 COV idx) := by
  intro idx hidx
  have h0 : idx 0 = 0 := by have := hidx 0 (by norm_num); simp [COV, badOf] at this; omega
  have h1 : idx 1 = 0 := by have := hidx 1 (by norm_num); simp [COV, badOf] at this; omega
  have h2 : idx 2 = 0 := by have := hidx 2 (by norm_num); simp [COV, badOf] at this; omega
  have e : rootCl 3 3 1099511627776 COV idx =
      toCl ⟨16384, 41175, 16384, 22243, 16384, 41175, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩ := by
    simp [rootCl, List.range_succ, h0, h1, h2, COV, badOf, toCl]
  rw [e]
  exact covered_of_walk lbZ lbDZ ptZ hRZ 1 1 7 _ root_walk (by decide)

/-- the certificate on every point with nonnegative gaps -/
theorem cert : ∀ g : ℕ → ℝ, (∀ r < 3, 0 ≤ g r) → Pg cN 3 BS TS g :=
  cert_of COV SMAX (by decide) (by decide +kernel) (by decide) 1099511627776 (by decide) run

end AMW.Cert.PCell3HRI
