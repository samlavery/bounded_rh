import AMW.PCell3H

/-! ###### the Q = 3 end-to-end `decide` instance in the canonical-Huffman walk (bridge-port; HUFF.md)

`PCell3I`'s three checks re-encoded by `huffenc`'s canonical codes on the toy tables of `PCell3H`: the adjacent pairs'
term tables have one entry (the constant; length 0, no bits), the other pairs' two (the constant `0`, a PLO tangent `1`);
axis table `3 ↦ 0`, `0 ↦ 100`, `1 ↦ 101`, `2 ↦ 110`, `4 ↦ 1110`, `5 ↦ 1111`; constraint table `0 ↦ 0`, `1 ↦ 10`,
`2 ↦ 11`.  Tables for the leaf reads are the empty ones (every pyramid read `0`), as in `PCell3I`.
* The walk: `[1][0]` a split on axis 3 (`g0 + g1`), child A `[0][0][000][0]` (three constant codes, no multiplier), child
  B `[0][0][000]`, one entry `[1][0][0][Yq = 5: 12 bits]`, `[0]`: end 30 (from 1).
* The Farkas cell: `[0][1]`, entries `[1][10][1][Yq = 1: 4 bits]` (`B03`) and `[1][11][0][1]` (`A13`), `[0]`: end 20.
-/

set_option maxRecDepth 100000

noncomputable section

namespace AMW.Cert.PCell3HI

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PCell3H

def TOPZ : ℕ := 0
def BKZ (_ : ℕ) : ℕ := 0
def TOPDZ : ℕ := 0
def BKDZ (_ : ℕ) : ℕ := 0
def PTZ (_ : ℕ) : ℕ := 0
/-- sixteen empty convex regions (`rgA = 1 > rgB = 0`) -/
def REGZ : ℕ × ℕ × List (List ℕ) :=
  (2037037919005230987192162416774720086405554702674251026342456770209302840312462675557744641, 0, [])

theorem lbZ : LBSound TOPZ BKZ := lb_sound (fun j _ => rfl) (by decide +kernel)
theorem lbDZ : LBSoundD TOPDZ BKDZ := lbDr_sound (fun j _ => rfl) (by decide +kernel)
theorem ptZ : PT3Sound PTZ := pt3_sound (fun j _ => rfl)
theorem hRZ : rgOk REGZ = true := by decide +kernel

theorem root_walk : U (walk TOPZ BKZ TOPDZ BKDZ PTZ REGZ 671746 3 1) ⟨147456, 155648, 147456, 151552, 147456, 155648, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩ = 30 := by
  decide +kernel

theorem root_cov : Covered (toCl ⟨147456, 155648, 147456, 151552, 147456, 155648, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩) :=
  covered_of_walk lbZ lbDZ ptZ hRZ 671746 3 30 _ root_walk (by decide)

theorem root_box (g : ℕ → ℝ) (hb : InBox 3 (toCl ⟨147456, 155648, 147456, 151552, 147456, 155648, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩) g) : Pg cN 3 BS TS g :=
  covered_box _ 1099511627776 (by decide) (by decide) (by decide) root_cov g hb

/-- child B's leaf on its tightened cell: payload `000`, the entry at bit 3, closed at bit 18: length 19 -/
theorem childB_leaf : mleafP TOPZ BKZ TOPDZ BKDZ PTZ REGZ 328 ⟨149504, 155648, 147456, 151552, 147456, 155648, 301056, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩ = 19 := by
  decide +kernel

theorem farkas_walk : U (walk TOPZ BKZ TOPDZ BKDZ PTZ REGZ 47324 1 1)
    ⟨28672, 32768, 20480, 28672, 40960, 48128, 49706, 60096, 99528, 101701, 73848, 1099511627776, 7⟩ = 20 := by
  decide +kernel

theorem farkas_cell : Covered (toCl ⟨28672, 32768, 20480, 28672, 40960, 48128, 49706, 60096, 99528, 101701, 73848, 1099511627776, 7⟩) :=
  covered_of_walk lbZ lbDZ ptZ hRZ 47324 1 20 _ farkas_walk (by decide)

end AMW.Cert.PCell3HI
