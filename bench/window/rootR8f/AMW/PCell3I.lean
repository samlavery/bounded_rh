import AMW.PCell3

/-! ###### an end-to-end `decide` instance of the Q = 3 polytope layer (bridge-port)

Tables: the empty ones (every pyramid read is `0`, no derivative or point data, no convex region), which verify by
`decide` in any window.  So only the linear part and the multipliers carry the inequality; the instance exercises the
kernel path, not the strength of the leaf.

The box `g0, g2 ∈ [4.5, 4.75]`, `g1 ∈ [4.5, 4.625]`, root cell with every pair bound absent (`A = 0`, `B = 2^40`).  The walk
splits once on the pair distance `g0 + g1` at the midpoint `301056/SC` of its range.
* Child A (`g0 + g1 ≤ 301056/SC`) is tightened (`u0` drops from 155648 to 153600) and is a plain leaf: 14 bits.
* Child B (`g0 + g1 ≥ 301056/SC`) is tightened (`l0` rises from 147456 to 149504) and is a leaf with one multiplier
  (`Yq = 5` on `A02`, quantum `SIG = 1024 U1 SA / 2^14`): 30 bits.  The multiplier raises the certified bound from
  553662 to 557477 (units 1/SA, cN = 550000).
-/

set_option maxRecDepth 100000

noncomputable section

namespace AMW.Cert.PCell3I

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PCell3

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

/-- the walk: a split on axis 3 (`g0 + g1`), then child A (a plain minorant leaf, 15 bits), then child B (a minorant leaf with
one multiplier, 31 bits); a leaf is bit 0 clear, bit 1 the kind (minorant / Farkas), its payload from bit 2 -/
theorem root_walk : U (walk TOPZ BKZ TOPDZ BKDZ PTZ REGZ 1391569403919 3 1) ⟨147456, 155648, 147456, 151552, 147456, 155648, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩ = 51 := by
  decide +kernel

/-- the root polytope cell is covered -/
theorem root_cov : Covered (toCl ⟨147456, 155648, 147456, 151552, 147456, 155648, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩) :=
  covered_of_walk lbZ lbDZ ptZ hRZ 1391569403919 3 51 _ root_walk (by decide)

/-- the box statement: every point of the box `[147456, 155648] × [147456, 151552] × [147456, 155648] / SC` -/
theorem root_box (g : ℕ → ℝ) (hb : InBox 3 (toCl ⟨147456, 155648, 147456, 151552, 147456, 155648, 0, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩) g) : Pg cN 3 BS TS g :=
  covered_box _ 1099511627776 (by decide) (by decide) (by decide) root_cov g hb

/-- child B's leaf on its tightened cell: payload `2^12 + 5 · 2^16` (six constant minorants, then one entry at bit 12:
constraint 0, side 0, `Yq = 5` from bit 16; the list closed at bit 28) passes, with payload length 29 -/
theorem childB_leaf : mleafP TOPZ BKZ TOPDZ BKDZ PTZ REGZ 331776 ⟨149504, 155648, 147456, 151552, 147456, 155648, 301056, 1099511627776, 0, 1099511627776, 0, 1099511627776, 0⟩ = 29 := by
  decide +kernel

/-- an LP-infeasible cell that two tightening rounds do not empty: `g0 + g1 + g2 ≤ 101701/SC` and `g1 + g2 ≥ 73848/SC` force
`g0 ≤ 27853/SC < l0`.  The kernel tightens it (to `l = (28672, 26539, 45995)`, `u = (30805, 27853, 47309)`: not empty,
not reflected) and a Farkas leaf closes it: two entries, `Yq = 1` on `B03` and on `A13` (payload from bit 3, 33 bits) -/
theorem farkas_walk : U (walk TOPZ BKZ TOPDZ BKDZ PTZ REGZ 11010269 1 1)
    ⟨28672, 32768, 20480, 28672, 40960, 48128, 49706, 60096, 99528, 101701, 73848, 1099511627776, 7⟩ = 36 := by
  decide +kernel

theorem farkas_cell : Covered (toCl ⟨28672, 32768, 20480, 28672, 40960, 48128, 49706, 60096, 99528, 101701, 73848, 1099511627776, 7⟩) :=
  covered_of_walk lbZ lbDZ ptZ hRZ 11010269 1 36 _ farkas_walk (by decide)

end AMW.Cert.PCell3I
