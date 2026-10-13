import AMW.PCellIV
import AMW.PCellDK2
import AMW.PCBias
import AMW.PCellCloseB
import AMW.PCDZ

/-! ###### polytope cells for Q = 8: the instance layer with the exact closure and Z
(instance layer: bridge-port, amg/genpcell4.py; the closure splits, the closure walk and its chunk lemmas: mvt-engine,
eight/am8/genpcellC.py, TZ.md §5)

Kernel functions unrolled on the curried state (16 gap and 56 pair bounds, the mask); every proof is a link to
the generic layer `AMW.PCellGen` through `toCl : St → Cl`.  The walk is mvt-engine's fixed-width DATA layout (emit8pz.py).
Engine, tables and per-term minorants: mvt-engine's MinCore on the AM
engine (pyramid oracle adapted from five-point-pyramid-2 by typh, Apache-2.0). ###### -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace AMW.Cert.PC9HP

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

def cN : ℕ := 856382
/-- the multiplier quantum: `Y = SIG · Yq`, `Yq < 2^13` (`2^-16` per unit g) -/
def SIG : ℕ := 1562500000000000

/-- the non-adjacent pairs, in pair order -/
def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8), (4, 6), (4, 7), (4, 8), (5, 7), (5, 8), (6, 8)]
theorem hPR : PRok 8 PR := by decide
/-- the gap weights and the terms `(i, j, a, k)` of the functional `Fg` (units 1/SA) -/
def BS : List ℕ := [27130, 50593, 66037, 74577, 74577, 66037, 50593, 27130]
def TS : List Term := [(0, 1, 11540560, 0), (0, 3, 8686366, 1), (0, 4, 34265560, 2), (0, 5, 40853477, 3), (0, 6, 58252863, 4), (0, 7, 100000000, 5), (0, 8, 200000000, 6), (1, 2, 23367038, 0), (1, 3, 27290752, 7), (1, 4, 39869581, 8), (1, 5, 35315115, 9), (1, 6, 59146522, 10), (1, 7, 83494272, 11), (1, 8, 100000000, 12), (2, 3, 30853002, 0), (2, 4, 42637189, 13), (2, 5, 51444051, 14), (2, 6, 60838648, 15), (2, 7, 59146522, 16), (2, 8, 58252863, 17), (3, 4, 34239398, 0), (3, 5, 60144115, 18), (3, 6, 51444051, 19), (3, 7, 35315115, 20), (3, 8, 40853477, 21), (4, 5, 34239398, 0), (4, 6, 42637189, 22), (4, 7, 39869581, 23), (4, 8, 34265560, 24), (5, 6, 30853002, 0), (5, 7, 27290752, 25), (5, 8, 8686366, 26), (6, 7, 23367038, 0), (7, 8, 11540560, 0)]
theorem hTS : TSok 8 PR TS := by decide

/-- the slot of the pair `(a, b)`, `a < b`, at `a · 9 + b`: gap `a` when `b = a + 1`, else `8` + the pair's rank -/
def SL : List ℕ := [0, 0, 8, 9, 10, 11, 12, 13, 14, 0, 0, 1, 15, 16, 17, 18, 19, 20, 0, 0, 0, 2, 21, 22, 23, 24, 25, 0, 0, 0, 0, 3, 26, 27, 28, 29, 0, 0, 0, 0, 0, 4, 30, 31, 32, 0, 0, 0, 0, 0, 0, 5, 33, 34, 0, 0, 0, 0, 0, 0, 0, 6, 35, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem hSL : SLok 8 PR SL := by decide
/-- the convex-region boundaries, sorted (a mode-1 split cuts at the one nearest the midpoint, ≥ 64 inside; mvt-engine) -/
def BND : List ℕ := [16384, 40384, 56768, 73664, 89920, 106176, 122304, 138560, 155136, 171456, 187712, 203840, 220224, 236480, 253120, 269440, 285760, 302080, 318720, 335168, 351872, 368384, 384896, 401280, 417728, 434048, 450496, 466816, 483264, 499584, 516032, 524288]

def SA : ℕ := 100000000

/-- the weighted functional on the gaps, in real form (pair weights `a_ij` and pressures `b_r` over `SA`) -/
def G (g0 g1 g2 g3 g4 g5 g6 g7 : ℝ) : ℝ :=
  (27130 / (SA:ℝ)) * g0 + (50593 / (SA:ℝ)) * g1 + (66037 / (SA:ℝ)) * g2 + (74577 / (SA:ℝ)) * g3 + (74577 / (SA:ℝ)) * g4 + (66037 / (SA:ℝ)) * g5 + (50593 / (SA:ℝ)) * g6 + (27130 / (SA:ℝ)) * g7
    + (11540560 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (8686366 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (34265560 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (40853477 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (58252863 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6 + g7) + (23367038 / (SA:ℝ)) * wfun (g1) + (27290752 / (SA:ℝ)) * wfun (g1 + g2) + (39869581 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (35315115 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (59146522 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (83494272 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6 + g7) + (30853002 / (SA:ℝ)) * wfun (g2) + (42637189 / (SA:ℝ)) * wfun (g2 + g3) + (51444051 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (60838648 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (59146522 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (58252863 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6 + g7) + (34239398 / (SA:ℝ)) * wfun (g3) + (60144115 / (SA:ℝ)) * wfun (g3 + g4) + (51444051 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (35315115 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (40853477 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6 + g7) + (34239398 / (SA:ℝ)) * wfun (g4) + (42637189 / (SA:ℝ)) * wfun (g4 + g5) + (39869581 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (34265560 / (SA:ℝ)) * wfun (g4 + g5 + g6 + g7) + (30853002 / (SA:ℝ)) * wfun (g5) + (27290752 / (SA:ℝ)) * wfun (g5 + g6) + (8686366 / (SA:ℝ)) * wfun (g5 + g6 + g7) + (23367038 / (SA:ℝ)) * wfun (g6) + (0 / (SA:ℝ)) * wfun (g6 + g7) + (11540560 / (SA:ℝ)) * wfun (g7)

/-- the integer functional `Fg` on a tuple of gaps is `SA · G` -/
theorem Fg_G (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) : Fg 8 BS TS (fun r => [x0, x1, x2, x3, x4, x5, x6, x7].getD r 0) = (SA : ℝ) * G x0 x1 x2 x3 x4 x5 x6 x7 := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring

/-- the canonical tables (HUFF.md §3): per table the count of each code length from 0, and the symbols in table order
(16-bit fields); a term's symbol is `κ · 2^14 + j1 · 2^7 + j2`, the axis `0 … 7` a gap, `8 …` a pair (pair order),
the multiplier's `c` the pair's rank -/
-- (fixed-width fields: no tables)

abbrev Covered : Cl → Prop := CovBy 8 PR (Pg cN 8 BS TS)

/-- the kernel state -/
structure St where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M : ℕ)

def toCl (s : St) : Cl :=
  ⟨[s.l0, s.l1, s.l2, s.l3, s.l4, s.l5, s.l6, s.l7], [s.u0, s.u1, s.u2, s.u3, s.u4, s.u5, s.u6, s.u7],
   [s.A02, s.A03, s.A04, s.A05, s.A06, s.A07, s.A08, s.A13, s.A14, s.A15, s.A16, s.A17, s.A18, s.A24, s.A25, s.A26, s.A27, s.A28, s.A35, s.A36, s.A37, s.A38, s.A46, s.A47, s.A48, s.A57, s.A58, s.A68], [s.B02, s.B03, s.B04, s.B05, s.B06, s.B07, s.B08, s.B13, s.B14, s.B15, s.B16, s.B17, s.B18, s.B24, s.B25, s.B26, s.B27, s.B28, s.B35, s.B36, s.B37, s.B38, s.B46, s.B47, s.B48, s.B57, s.B58, s.B68]⟩
def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨c.L.getD 0 0, c.U.getD 0 0, c.L.getD 1 0, c.U.getD 1 0, c.L.getD 2 0, c.U.getD 2 0, c.L.getD 3 0, c.U.getD 3 0, c.L.getD 4 0, c.U.getD 4 0, c.L.getD 5 0, c.U.getD 5 0, c.L.getD 6 0, c.U.getD 6 0, c.L.getD 7 0, c.U.getD 7 0, c.A.getD 0 0, c.B.getD 0 0, c.A.getD 1 0, c.B.getD 1 0, c.A.getD 2 0, c.B.getD 2 0, c.A.getD 3 0, c.B.getD 3 0, c.A.getD 4 0, c.B.getD 4 0, c.A.getD 5 0, c.B.getD 5 0, c.A.getD 6 0, c.B.getD 6 0, c.A.getD 7 0, c.B.getD 7 0, c.A.getD 8 0, c.B.getD 8 0, c.A.getD 9 0, c.B.getD 9 0, c.A.getD 10 0, c.B.getD 10 0, c.A.getD 11 0, c.B.getD 11 0, c.A.getD 12 0, c.B.getD 12 0, c.A.getD 13 0, c.B.getD 13 0, c.A.getD 14 0, c.B.getD 14 0, c.A.getD 15 0, c.B.getD 15 0, c.A.getD 16 0, c.B.getD 16 0, c.A.getD 17 0, c.B.getD 17 0, c.A.getD 18 0, c.B.getD 18 0, c.A.getD 19 0, c.B.getD 19 0, c.A.getD 20 0, c.B.getD 20 0, c.A.getD 21 0, c.B.getD 21 0, c.A.getD 22 0, c.B.getD 22 0, c.A.getD 23 0, c.B.getD 23 0, c.A.getD 24 0, c.B.getD 24 0, c.A.getD 25 0, c.B.getD 25 0, c.A.getD 26 0, c.B.getD 26 0, c.A.getD 27 0, c.B.getD 27 0, m⟩

theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = 8) (h2 : c.U.length = 8) (h3 : c.A.length = 28) (h4 : c.B.length = 28) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]

abbrev ST : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
/-- a continuation applied to a state -/
def U (k : ST) (s : St) : ℕ := k s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.l6 s.u6 s.l7 s.u7 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A07 s.B07 s.A08 s.B08 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A17 s.B17 s.A18 s.B18 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A27 s.B27 s.A28 s.B28 s.A35 s.B35 s.A36 s.B36 s.A37 s.B37 s.A38 s.B38 s.A46 s.B46 s.A47 s.B47 s.A48 s.B48 s.A57 s.B57 s.A58 s.B58 s.A68 s.B68 s.M
def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
def zK : ST := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h

theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = 8) (h2 : c.U.length = 8) (h3 : c.A.length = 28)
    (h4 : c.B.length = 28) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h

/-- a split node's two children (`cA` from `pos`, the bit after the axis code, then `cB`) cover the cell when the split lemma does -/
theorem sp_ok {ih : WF} (hih : WalkOK ih) {s : St} {cA cB : Cl} {pos mA mB : ℕ}
    (hc : Covered cA → Covered cB → Covered (toCl s))
    (h : Bool.rec (motive := fun _ => ℕ) (U (ih (U (ih pos) (ofCl cA mA))) (ofCl cB mB)) 0
      (Nat.beq (U (ih pos) (ofCl cA mA)) 0) ≠ 0)
    (hA : cA.L.length = 8 ∧ cA.U.length = 8 ∧ cA.A.length = 28 ∧ cA.B.length = 28)
    (hB : cB.L.length = 8 ∧ cB.U.length = 8 ∧ cB.A.length = 28 ∧ cB.B.length = 28) : Covered (toCl s) := by
  cases hp : Nat.beq (U (ih pos) (ofCl cA mA)) 0
  · rw [hp] at h
    exact hc (ofCl_ok (hih _) hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 fun h0 => by rw [h0] at hp; exact absurd hp (by decide))
      (ofCl_ok (hih _) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 h)
  · rw [hp] at h; exact absurd rfl h


-- (2) split nodes: gap r at the midpoint of [l_r, u_r]; pair t at the midpoint of its (persisted) bounds

/-- the closure through the point `s` of a split's edge: `x` the column `BB + D(·, s)`, `y` the row
`BB + D(s, t) + D(t, ·)` (`PCBias.cuB`, `BB = 2^42`) -/
def cuH (k : ST) (x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  k (nmax a (Nat.sub 8796093022208 (Nat.add x1 y0)))
    (nmin b (Nat.sub (Nat.add x0 y1) 8796093022208))
    (nmax c (Nat.sub 8796093022208 (Nat.add x2 y1)))
    (nmin d (Nat.sub (Nat.add x1 y2) 8796093022208))
    (nmax e (Nat.sub 8796093022208 (Nat.add x3 y2)))
    (nmin f (Nat.sub (Nat.add x2 y3) 8796093022208))
    (nmax g (Nat.sub 8796093022208 (Nat.add x4 y3)))
    (nmin h (Nat.sub (Nat.add x3 y4) 8796093022208))
    (nmax i (Nat.sub 8796093022208 (Nat.add x5 y4)))
    (nmin j (Nat.sub (Nat.add x4 y5) 8796093022208))
    (nmax l (Nat.sub 8796093022208 (Nat.add x6 y5)))
    (nmin m (Nat.sub (Nat.add x5 y6) 8796093022208))
    (nmax n (Nat.sub 8796093022208 (Nat.add x7 y6)))
    (nmin o (Nat.sub (Nat.add x6 y7) 8796093022208))
    (nmax r (Nat.sub 8796093022208 (Nat.add x8 y7)))
    (nmin s (Nat.sub (Nat.add x7 y8) 8796093022208))
    (nmax t (Nat.sub 8796093022208 (Nat.add x2 y0)))
    (nmin u (Nat.sub (Nat.add x0 y2) 8796093022208))
    (nmax v (Nat.sub 8796093022208 (Nat.add x3 y0)))
    (nmin w (Nat.sub (Nat.add x0 y3) 8796093022208))
    (nmax x (Nat.sub 8796093022208 (Nat.add x4 y0)))
    (nmin y (Nat.sub (Nat.add x0 y4) 8796093022208))
    (nmax z (Nat.sub 8796093022208 (Nat.add x5 y0)))
    (nmin A (Nat.sub (Nat.add x0 y5) 8796093022208))
    (nmax B (Nat.sub 8796093022208 (Nat.add x6 y0)))
    (nmin C (Nat.sub (Nat.add x0 y6) 8796093022208))
    (nmax D (Nat.sub 8796093022208 (Nat.add x7 y0)))
    (nmin E (Nat.sub (Nat.add x0 y7) 8796093022208))
    (nmax F (Nat.sub 8796093022208 (Nat.add x8 y0)))
    (nmin G (Nat.sub (Nat.add x0 y8) 8796093022208))
    (nmax H (Nat.sub 8796093022208 (Nat.add x3 y1)))
    (nmin I (Nat.sub (Nat.add x1 y3) 8796093022208))
    (nmax J (Nat.sub 8796093022208 (Nat.add x4 y1)))
    (nmin K (Nat.sub (Nat.add x1 y4) 8796093022208))
    (nmax L (Nat.sub 8796093022208 (Nat.add x5 y1)))
    (nmin M (Nat.sub (Nat.add x1 y5) 8796093022208))
    (nmax N (Nat.sub 8796093022208 (Nat.add x6 y1)))
    (nmin O (Nat.sub (Nat.add x1 y6) 8796093022208))
    (nmax P (Nat.sub 8796093022208 (Nat.add x7 y1)))
    (nmin Q (Nat.sub (Nat.add x1 y7) 8796093022208))
    (nmax R (Nat.sub 8796093022208 (Nat.add x8 y1)))
    (nmin S (Nat.sub (Nat.add x1 y8) 8796093022208))
    (nmax T (Nat.sub 8796093022208 (Nat.add x4 y2)))
    (nmin U (Nat.sub (Nat.add x2 y4) 8796093022208))
    (nmax V (Nat.sub 8796093022208 (Nat.add x5 y2)))
    (nmin W (Nat.sub (Nat.add x2 y5) 8796093022208))
    (nmax X (Nat.sub 8796093022208 (Nat.add x6 y2)))
    (nmin Y (Nat.sub (Nat.add x2 y6) 8796093022208))
    (nmax Z (Nat.sub 8796093022208 (Nat.add x7 y2)))
    (nmin aa (Nat.sub (Nat.add x2 y7) 8796093022208))
    (nmax ab (Nat.sub 8796093022208 (Nat.add x8 y2)))
    (nmin ac (Nat.sub (Nat.add x2 y8) 8796093022208))
    (nmax ad (Nat.sub 8796093022208 (Nat.add x5 y3)))
    (nmin ae (Nat.sub (Nat.add x3 y5) 8796093022208))
    (nmax af (Nat.sub 8796093022208 (Nat.add x6 y3)))
    (nmin ag (Nat.sub (Nat.add x3 y6) 8796093022208))
    (nmax ah (Nat.sub 8796093022208 (Nat.add x7 y3)))
    (nmin ai (Nat.sub (Nat.add x3 y7) 8796093022208))
    (nmax aj (Nat.sub 8796093022208 (Nat.add x8 y3)))
    (nmin al (Nat.sub (Nat.add x3 y8) 8796093022208))
    (nmax am (Nat.sub 8796093022208 (Nat.add x6 y4)))
    (nmin an (Nat.sub (Nat.add x4 y6) 8796093022208))
    (nmax ao (Nat.sub 8796093022208 (Nat.add x7 y4)))
    (nmin ar (Nat.sub (Nat.add x4 y7) 8796093022208))
    (nmax au (Nat.sub 8796093022208 (Nat.add x8 y4)))
    (nmin av (Nat.sub (Nat.add x4 y8) 8796093022208))
    (nmax aw (Nat.sub 8796093022208 (Nat.add x7 y5)))
    (nmin ax (Nat.sub (Nat.add x5 y7) 8796093022208))
    (nmax ay (Nat.sub 8796093022208 (Nat.add x8 y5)))
    (nmin az (Nat.sub (Nat.add x5 y8) 8796093022208))
    (nmax ba (Nat.sub 8796093022208 (Nat.add x8 y6)))
    (nmin bb (Nat.sub (Nat.add x6 y8) 8796093022208))
    bc

/-- `cuH` on a column and a row given as lists, and a state -/
def cuL (k : ST) (X Y : List ℕ) (s : St) : ℕ :=
  cuH k (X.getD 0 0) (X.getD 1 0) (X.getD 2 0) (X.getD 3 0) (X.getD 4 0) (X.getD 5 0) (X.getD 6 0) (X.getD 7 0) (X.getD 8 0) (Y.getD 0 0) (Y.getD 1 0) (Y.getD 2 0) (Y.getD 3 0) (Y.getD 4 0) (Y.getD 5 0) (Y.getD 6 0) (Y.getD 7 0) (Y.getD 8 0)
    s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.l6 s.u6 s.l7 s.u7 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A07 s.B07 s.A08 s.B08 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A17 s.B17 s.A18 s.B18 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A27 s.B27 s.A28 s.B28 s.A35 s.B35 s.A36 s.B36 s.A37 s.B37 s.A38 s.B38 s.A46 s.B46 s.A47 s.B47 s.A48 s.B48 s.A57 s.B57 s.A58 s.B58 s.A68 s.B68 s.M

/-- `cuH` is `cuB` on the curried state -/
theorem cuL_eq (k : ST) (X Y : List ℕ) (s : St) : cuL k X Y s = U k (ofCl (cuB 8 PR (toCl s) X Y) s.M) := by
  simp only [cuL, U, ofCl, cuB, toCl, PR, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, pI, pJ]
  rfl
theorem cuH_ok {k : ST} (hk : CovK k) (X Y : List ℕ) (s : St) (h : cuL k X Y s ≠ 0) :
    Covered (cuB 8 PR (toCl s) X Y) :=
  ofCl_ok hk (by simp [cuB]) (by simp [cuB]) (by simp [cuB, PR]) (by simp [cuB, PR]) (m := s.M) (by rw [← cuL_eq]; exact h)

/-- a split on `(i, j)` at `q`: the children are `cuH` through `i → j` and `j → i` (`cov_splitB`) -/
theorem spH_ok {ih : WF} (hih : WalkOK ih) {pos : ℕ} (i j : ℕ) (hij : i < j) (hj : j ≤ 8) {s : St} {q : ℕ}
    (h : Bool.rec (motive := fun _ => ℕ)
      (cuL (ih (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s)) (colB 8 SL (toCl s) j) (rowB 8 SL (toCl s) (Nat.sub BB q) i) s) 0
      (Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0) ≠ 0) : Covered (toCl s) := by
  have hc := cov_splitB (P := Pg cN 8 BS TS) (c := toCl s) hSL hPR hij hj q
  cases hp : Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0
  · rw [hp] at h
    exact hc (cuH_ok (hih _) _ _ s fun h0 => by rw [h0] at hp; exact absurd hp (by decide)) (cuH_ok (hih _) _ _ s h)
  · rw [hp] at h; exact absurd rfl h

def gsplit0 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add a b) 1) (bcutL BND 64 a b) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe a) qe (Nat.add qe d) (Nat.add qe I) (Nat.add qe K) (Nat.add qe M) (Nat.add qe O) (Nat.add qe Q) (Nat.add qe S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def gsplit1 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add c d) 1) (bcutL BND 64 c d) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) (Nat.sub qe t) (Nat.sub qe c) qe (Nat.add qe f) (Nat.add qe U) (Nat.add qe W) (Nat.add qe Y) (Nat.add qe aa) (Nat.add qe ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) (Nat.sub qf a) qf (Nat.add qf d) (Nat.add qf I) (Nat.add qf K) (Nat.add qf M) (Nat.add qf O) (Nat.add qf Q) (Nat.add qf S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def gsplit2 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add e f) 1) (bcutL BND 64 e f) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) (Nat.sub qe v) (Nat.sub qe H) (Nat.sub qe e) qe (Nat.add qe h) (Nat.add qe ae) (Nat.add qe ag) (Nat.add qe ai) (Nat.add qe al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) (Nat.sub qf t) (Nat.sub qf c) qf (Nat.add qf f) (Nat.add qf U) (Nat.add qf W) (Nat.add qf Y) (Nat.add qf aa) (Nat.add qf ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def gsplit3 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add g h) 1) (bcutL BND 64 g h) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) (Nat.sub qe x) (Nat.sub qe J) (Nat.sub qe T) (Nat.sub qe g) qe (Nat.add qe j) (Nat.add qe an) (Nat.add qe ar) (Nat.add qe av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) (Nat.sub qf v) (Nat.sub qf H) (Nat.sub qf e) qf (Nat.add qf h) (Nat.add qf ae) (Nat.add qf ag) (Nat.add qf ai) (Nat.add qf al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def gsplit4 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add i j) 1) (bcutL BND 64 i j) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) (Nat.sub qe z) (Nat.sub qe L) (Nat.sub qe V) (Nat.sub qe ad) (Nat.sub qe i) qe (Nat.add qe m) (Nat.add qe ax) (Nat.add qe az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) (Nat.sub qf x) (Nat.sub qf J) (Nat.sub qf T) (Nat.sub qf g) qf (Nat.add qf j) (Nat.add qf an) (Nat.add qf ar) (Nat.add qf av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def gsplit5 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add l m) 1) (bcutL BND 64 l m) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) (Nat.sub qe B) (Nat.sub qe N) (Nat.sub qe X) (Nat.sub qe af) (Nat.sub qe am) (Nat.sub qe l) qe (Nat.add qe o) (Nat.add qe bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) (Nat.sub qf z) (Nat.sub qf L) (Nat.sub qf V) (Nat.sub qf ad) (Nat.sub qf i) qf (Nat.add qf m) (Nat.add qf ax) (Nat.add qf az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def gsplit6 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add n o) 1) (bcutL BND 64 n o) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) (Nat.sub qe D) (Nat.sub qe P) (Nat.sub qe Z) (Nat.sub qe ah) (Nat.sub qe ao) (Nat.sub qe aw) (Nat.sub qe n) qe (Nat.add qe s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) (Nat.sub qf B) (Nat.sub qf N) (Nat.sub qf X) (Nat.sub qf af) (Nat.sub qf am) (Nat.sub qf l) qf (Nat.add qf o) (Nat.add qf bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def gsplit7 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add r s) 1) (bcutL BND 64 r s) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb (Nat.sub qf D) (Nat.sub qf P) (Nat.sub qf Z) (Nat.sub qf ah) (Nat.sub qf ao) (Nat.sub qf aw) (Nat.sub qf n) qf (Nat.add qf s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit02 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add t u) 1) (bcutL BND 64 t u) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe t) (Nat.sub qe c) qe (Nat.add qe f) (Nat.add qe U) (Nat.add qe W) (Nat.add qe Y) (Nat.add qe aa) (Nat.add qe ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit03 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add v w) 1) (bcutL BND 64 v w) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe v) (Nat.sub qe H) (Nat.sub qe e) qe (Nat.add qe h) (Nat.add qe ae) (Nat.add qe ag) (Nat.add qe ai) (Nat.add qe al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit04 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add x y) 1) (bcutL BND 64 x y) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe x) (Nat.sub qe J) (Nat.sub qe T) (Nat.sub qe g) qe (Nat.add qe j) (Nat.add qe an) (Nat.add qe ar) (Nat.add qe av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit05 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add z A) 1) (bcutL BND 64 z A) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe z) (Nat.sub qe L) (Nat.sub qe V) (Nat.sub qe ad) (Nat.sub qe i) qe (Nat.add qe m) (Nat.add qe ax) (Nat.add qe az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit06 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add B C) 1) (bcutL BND 64 B C) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe B) (Nat.sub qe N) (Nat.sub qe X) (Nat.sub qe af) (Nat.sub qe am) (Nat.sub qe l) qe (Nat.add qe o) (Nat.add qe bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit07 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add D E) 1) (bcutL BND 64 D E) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe D) (Nat.sub qe P) (Nat.sub qe Z) (Nat.sub qe ah) (Nat.sub qe ao) (Nat.sub qe aw) (Nat.sub qe n) qe (Nat.add qe s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit08 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add F G) 1) (bcutL BND 64 F G) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb qf (Nat.add qf b) (Nat.add qf u) (Nat.add qf w) (Nat.add qf y) (Nat.add qf A) (Nat.add qf C) (Nat.add qf E) (Nat.add qf G) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit13 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add H I) 1) (bcutL BND 64 H I) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) (Nat.sub qe v) (Nat.sub qe H) (Nat.sub qe e) qe (Nat.add qe h) (Nat.add qe ae) (Nat.add qe ag) (Nat.add qe ai) (Nat.add qe al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) (Nat.sub qf a) qf (Nat.add qf d) (Nat.add qf I) (Nat.add qf K) (Nat.add qf M) (Nat.add qf O) (Nat.add qf Q) (Nat.add qf S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit14 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add J K) 1) (bcutL BND 64 J K) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) (Nat.sub qe x) (Nat.sub qe J) (Nat.sub qe T) (Nat.sub qe g) qe (Nat.add qe j) (Nat.add qe an) (Nat.add qe ar) (Nat.add qe av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) (Nat.sub qf a) qf (Nat.add qf d) (Nat.add qf I) (Nat.add qf K) (Nat.add qf M) (Nat.add qf O) (Nat.add qf Q) (Nat.add qf S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit15 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add L M) 1) (bcutL BND 64 L M) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) (Nat.sub qe z) (Nat.sub qe L) (Nat.sub qe V) (Nat.sub qe ad) (Nat.sub qe i) qe (Nat.add qe m) (Nat.add qe ax) (Nat.add qe az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) (Nat.sub qf a) qf (Nat.add qf d) (Nat.add qf I) (Nat.add qf K) (Nat.add qf M) (Nat.add qf O) (Nat.add qf Q) (Nat.add qf S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit16 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add N O) 1) (bcutL BND 64 N O) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) (Nat.sub qe B) (Nat.sub qe N) (Nat.sub qe X) (Nat.sub qe af) (Nat.sub qe am) (Nat.sub qe l) qe (Nat.add qe o) (Nat.add qe bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) (Nat.sub qf a) qf (Nat.add qf d) (Nat.add qf I) (Nat.add qf K) (Nat.add qf M) (Nat.add qf O) (Nat.add qf Q) (Nat.add qf S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit17 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add P Q) 1) (bcutL BND 64 P Q) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) (Nat.sub qe D) (Nat.sub qe P) (Nat.sub qe Z) (Nat.sub qe ah) (Nat.sub qe ao) (Nat.sub qe aw) (Nat.sub qe n) qe (Nat.add qe s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) (Nat.sub qf a) qf (Nat.add qf d) (Nat.add qf I) (Nat.add qf K) (Nat.add qf M) (Nat.add qf O) (Nat.add qf Q) (Nat.add qf S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit18 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add R S) 1) (bcutL BND 64 R S) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb (Nat.sub qf a) qf (Nat.add qf d) (Nat.add qf I) (Nat.add qf K) (Nat.add qf M) (Nat.add qf O) (Nat.add qf Q) (Nat.add qf S) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit24 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add T U) 1) (bcutL BND 64 T U) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) (Nat.sub qe x) (Nat.sub qe J) (Nat.sub qe T) (Nat.sub qe g) qe (Nat.add qe j) (Nat.add qe an) (Nat.add qe ar) (Nat.add qe av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) (Nat.sub qf t) (Nat.sub qf c) qf (Nat.add qf f) (Nat.add qf U) (Nat.add qf W) (Nat.add qf Y) (Nat.add qf aa) (Nat.add qf ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit25 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add V W) 1) (bcutL BND 64 V W) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) (Nat.sub qe z) (Nat.sub qe L) (Nat.sub qe V) (Nat.sub qe ad) (Nat.sub qe i) qe (Nat.add qe m) (Nat.add qe ax) (Nat.add qe az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) (Nat.sub qf t) (Nat.sub qf c) qf (Nat.add qf f) (Nat.add qf U) (Nat.add qf W) (Nat.add qf Y) (Nat.add qf aa) (Nat.add qf ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit26 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add X Y) 1) (bcutL BND 64 X Y) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) (Nat.sub qe B) (Nat.sub qe N) (Nat.sub qe X) (Nat.sub qe af) (Nat.sub qe am) (Nat.sub qe l) qe (Nat.add qe o) (Nat.add qe bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) (Nat.sub qf t) (Nat.sub qf c) qf (Nat.add qf f) (Nat.add qf U) (Nat.add qf W) (Nat.add qf Y) (Nat.add qf aa) (Nat.add qf ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit27 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add Z aa) 1) (bcutL BND 64 Z aa) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) (Nat.sub qe D) (Nat.sub qe P) (Nat.sub qe Z) (Nat.sub qe ah) (Nat.sub qe ao) (Nat.sub qe aw) (Nat.sub qe n) qe (Nat.add qe s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) (Nat.sub qf t) (Nat.sub qf c) qf (Nat.add qf f) (Nat.add qf U) (Nat.add qf W) (Nat.add qf Y) (Nat.add qf aa) (Nat.add qf ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit28 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ab ac) 1) (bcutL BND 64 ab ac) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb (Nat.sub qf t) (Nat.sub qf c) qf (Nat.add qf f) (Nat.add qf U) (Nat.add qf W) (Nat.add qf Y) (Nat.add qf aa) (Nat.add qf ac) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit35 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ad ae) 1) (bcutL BND 64 ad ae) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) (Nat.sub qe z) (Nat.sub qe L) (Nat.sub qe V) (Nat.sub qe ad) (Nat.sub qe i) qe (Nat.add qe m) (Nat.add qe ax) (Nat.add qe az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) (Nat.sub qf v) (Nat.sub qf H) (Nat.sub qf e) qf (Nat.add qf h) (Nat.add qf ae) (Nat.add qf ag) (Nat.add qf ai) (Nat.add qf al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit36 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add af ag) 1) (bcutL BND 64 af ag) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) (Nat.sub qe B) (Nat.sub qe N) (Nat.sub qe X) (Nat.sub qe af) (Nat.sub qe am) (Nat.sub qe l) qe (Nat.add qe o) (Nat.add qe bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) (Nat.sub qf v) (Nat.sub qf H) (Nat.sub qf e) qf (Nat.add qf h) (Nat.add qf ae) (Nat.add qf ag) (Nat.add qf ai) (Nat.add qf al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit37 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ah ai) 1) (bcutL BND 64 ah ai) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) (Nat.sub qe D) (Nat.sub qe P) (Nat.sub qe Z) (Nat.sub qe ah) (Nat.sub qe ao) (Nat.sub qe aw) (Nat.sub qe n) qe (Nat.add qe s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) (Nat.sub qf v) (Nat.sub qf H) (Nat.sub qf e) qf (Nat.add qf h) (Nat.add qf ae) (Nat.add qf ag) (Nat.add qf ai) (Nat.add qf al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit38 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add aj al) 1) (bcutL BND 64 aj al) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb (Nat.sub qf v) (Nat.sub qf H) (Nat.sub qf e) qf (Nat.add qf h) (Nat.add qf ae) (Nat.add qf ag) (Nat.add qf ai) (Nat.add qf al) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit46 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add am an) 1) (bcutL BND 64 am an) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) (Nat.sub qe B) (Nat.sub qe N) (Nat.sub qe X) (Nat.sub qe af) (Nat.sub qe am) (Nat.sub qe l) qe (Nat.add qe o) (Nat.add qe bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) (Nat.sub qf x) (Nat.sub qf J) (Nat.sub qf T) (Nat.sub qf g) qf (Nat.add qf j) (Nat.add qf an) (Nat.add qf ar) (Nat.add qf av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit47 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ao ar) 1) (bcutL BND 64 ao ar) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) (Nat.sub qe D) (Nat.sub qe P) (Nat.sub qe Z) (Nat.sub qe ah) (Nat.sub qe ao) (Nat.sub qe aw) (Nat.sub qe n) qe (Nat.add qe s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) (Nat.sub qf x) (Nat.sub qf J) (Nat.sub qf T) (Nat.sub qf g) qf (Nat.add qf j) (Nat.add qf an) (Nat.add qf ar) (Nat.add qf av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit48 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add au av) 1) (bcutL BND 64 au av) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb (Nat.sub qf x) (Nat.sub qf J) (Nat.sub qf T) (Nat.sub qf g) qf (Nat.add qf j) (Nat.add qf an) (Nat.add qf ar) (Nat.add qf av) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit57 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add aw ax) 1) (bcutL BND 64 aw ax) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) (Nat.sub qe D) (Nat.sub qe P) (Nat.sub qe Z) (Nat.sub qe ah) (Nat.sub qe ao) (Nat.sub qe aw) (Nat.sub qe n) qe (Nat.add qe s) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r) (Nat.sub qf z) (Nat.sub qf L) (Nat.sub qf V) (Nat.sub qf ad) (Nat.sub qf i) qf (Nat.add qf m) (Nat.add qf ax) (Nat.add qf az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit58 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ay az) 1) (bcutL BND 64 ay az) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb (Nat.sub qf z) (Nat.sub qf L) (Nat.sub qf V) (Nat.sub qf ad) (Nat.sub qf i) qf (Nat.add qf m) (Nat.add qf ax) (Nat.add qf az) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

def ssplit68 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ba bb) 1) (bcutL BND 64 ba bb) (Nat.beq md 1); let qb := 4398046511104; let qe := Nat.add qb q; let qf := Nat.sub qb q;
  let p := cuH (ih pos) (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba) (Nat.sub qe F) (Nat.sub qe R) (Nat.sub qe ab) (Nat.sub qe aj) (Nat.sub qe au) (Nat.sub qe ay) (Nat.sub qe ba) (Nat.sub qe r) qe a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cuH (ih p) (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb (Nat.sub qf B) (Nat.sub qf N) (Nat.sub qf X) (Nat.sub qf af) (Nat.sub qf am) (Nat.sub qf l) qf (Nat.add qf o) (Nat.add qf bb) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq p 0)

section
variable {ih : WF} (hih : WalkOK ih) (md pos : ℕ)
include hih
theorem gsplit0_ok : CovK (gsplit0 ih md pos) := fun s h => spH_ok hih 0 1 (by decide) (by decide) (s := s) h
theorem gsplit1_ok : CovK (gsplit1 ih md pos) := fun s h => spH_ok hih 1 2 (by decide) (by decide) (s := s) h
theorem gsplit2_ok : CovK (gsplit2 ih md pos) := fun s h => spH_ok hih 2 3 (by decide) (by decide) (s := s) h
theorem gsplit3_ok : CovK (gsplit3 ih md pos) := fun s h => spH_ok hih 3 4 (by decide) (by decide) (s := s) h
theorem gsplit4_ok : CovK (gsplit4 ih md pos) := fun s h => spH_ok hih 4 5 (by decide) (by decide) (s := s) h
theorem gsplit5_ok : CovK (gsplit5 ih md pos) := fun s h => spH_ok hih 5 6 (by decide) (by decide) (s := s) h
theorem gsplit6_ok : CovK (gsplit6 ih md pos) := fun s h => spH_ok hih 6 7 (by decide) (by decide) (s := s) h
theorem gsplit7_ok : CovK (gsplit7 ih md pos) := fun s h => spH_ok hih 7 8 (by decide) (by decide) (s := s) h
theorem ssplit02_ok : CovK (ssplit02 ih md pos) := fun s h => spH_ok hih 0 2 (by decide) (by decide) (s := s) h
theorem ssplit03_ok : CovK (ssplit03 ih md pos) := fun s h => spH_ok hih 0 3 (by decide) (by decide) (s := s) h
theorem ssplit04_ok : CovK (ssplit04 ih md pos) := fun s h => spH_ok hih 0 4 (by decide) (by decide) (s := s) h
theorem ssplit05_ok : CovK (ssplit05 ih md pos) := fun s h => spH_ok hih 0 5 (by decide) (by decide) (s := s) h
theorem ssplit06_ok : CovK (ssplit06 ih md pos) := fun s h => spH_ok hih 0 6 (by decide) (by decide) (s := s) h
theorem ssplit07_ok : CovK (ssplit07 ih md pos) := fun s h => spH_ok hih 0 7 (by decide) (by decide) (s := s) h
theorem ssplit08_ok : CovK (ssplit08 ih md pos) := fun s h => spH_ok hih 0 8 (by decide) (by decide) (s := s) h
theorem ssplit13_ok : CovK (ssplit13 ih md pos) := fun s h => spH_ok hih 1 3 (by decide) (by decide) (s := s) h
theorem ssplit14_ok : CovK (ssplit14 ih md pos) := fun s h => spH_ok hih 1 4 (by decide) (by decide) (s := s) h
theorem ssplit15_ok : CovK (ssplit15 ih md pos) := fun s h => spH_ok hih 1 5 (by decide) (by decide) (s := s) h
theorem ssplit16_ok : CovK (ssplit16 ih md pos) := fun s h => spH_ok hih 1 6 (by decide) (by decide) (s := s) h
theorem ssplit17_ok : CovK (ssplit17 ih md pos) := fun s h => spH_ok hih 1 7 (by decide) (by decide) (s := s) h
theorem ssplit18_ok : CovK (ssplit18 ih md pos) := fun s h => spH_ok hih 1 8 (by decide) (by decide) (s := s) h
theorem ssplit24_ok : CovK (ssplit24 ih md pos) := fun s h => spH_ok hih 2 4 (by decide) (by decide) (s := s) h
theorem ssplit25_ok : CovK (ssplit25 ih md pos) := fun s h => spH_ok hih 2 5 (by decide) (by decide) (s := s) h
theorem ssplit26_ok : CovK (ssplit26 ih md pos) := fun s h => spH_ok hih 2 6 (by decide) (by decide) (s := s) h
theorem ssplit27_ok : CovK (ssplit27 ih md pos) := fun s h => spH_ok hih 2 7 (by decide) (by decide) (s := s) h
theorem ssplit28_ok : CovK (ssplit28 ih md pos) := fun s h => spH_ok hih 2 8 (by decide) (by decide) (s := s) h
theorem ssplit35_ok : CovK (ssplit35 ih md pos) := fun s h => spH_ok hih 3 5 (by decide) (by decide) (s := s) h
theorem ssplit36_ok : CovK (ssplit36 ih md pos) := fun s h => spH_ok hih 3 6 (by decide) (by decide) (s := s) h
theorem ssplit37_ok : CovK (ssplit37 ih md pos) := fun s h => spH_ok hih 3 7 (by decide) (by decide) (s := s) h
theorem ssplit38_ok : CovK (ssplit38 ih md pos) := fun s h => spH_ok hih 3 8 (by decide) (by decide) (s := s) h
theorem ssplit46_ok : CovK (ssplit46 ih md pos) := fun s h => spH_ok hih 4 6 (by decide) (by decide) (s := s) h
theorem ssplit47_ok : CovK (ssplit47 ih md pos) := fun s h => spH_ok hih 4 7 (by decide) (by decide) (s := s) h
theorem ssplit48_ok : CovK (ssplit48 ih md pos) := fun s h => spH_ok hih 4 8 (by decide) (by decide) (s := s) h
theorem ssplit57_ok : CovK (ssplit57 ih md pos) := fun s h => spH_ok hih 5 7 (by decide) (by decide) (s := s) h
theorem ssplit58_ok : CovK (ssplit58 ih md pos) := fun s h => spH_ok hih 5 8 (by decide) (by decide) (s := s) h
theorem ssplit68_ok : CovK (ssplit68 ih md pos) := fun s h => spH_ok hih 6 8 (by decide) (by decide) (s := s) h
end

/-- a split node: axis `0 … 7` a gap, `8 … 35` a pair (pair order) -/
def splitAx (ih : WF) (md pos ax : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (zK) (ssplit68 ih md pos) (Nat.beq ax 35)) (ssplit58 ih md pos) (Nat.beq ax 34)) (ssplit57 ih md pos) (Nat.beq ax 33)) (ssplit48 ih md pos) (Nat.beq ax 32)) (ssplit47 ih md pos) (Nat.beq ax 31)) (ssplit46 ih md pos) (Nat.beq ax 30)) (ssplit38 ih md pos) (Nat.beq ax 29)) (ssplit37 ih md pos) (Nat.beq ax 28)) (ssplit36 ih md pos) (Nat.beq ax 27)) (ssplit35 ih md pos) (Nat.beq ax 26)) (ssplit28 ih md pos) (Nat.beq ax 25)) (ssplit27 ih md pos) (Nat.beq ax 24)) (ssplit26 ih md pos) (Nat.beq ax 23)) (ssplit25 ih md pos) (Nat.beq ax 22)) (ssplit24 ih md pos) (Nat.beq ax 21)) (ssplit18 ih md pos) (Nat.beq ax 20)) (ssplit17 ih md pos) (Nat.beq ax 19)) (ssplit16 ih md pos) (Nat.beq ax 18)) (ssplit15 ih md pos) (Nat.beq ax 17)) (ssplit14 ih md pos) (Nat.beq ax 16)) (ssplit13 ih md pos) (Nat.beq ax 15)) (ssplit08 ih md pos) (Nat.beq ax 14)) (ssplit07 ih md pos) (Nat.beq ax 13)) (ssplit06 ih md pos) (Nat.beq ax 12)) (ssplit05 ih md pos) (Nat.beq ax 11)) (ssplit04 ih md pos) (Nat.beq ax 10)) (ssplit03 ih md pos) (Nat.beq ax 9)) (ssplit02 ih md pos) (Nat.beq ax 8)) (gsplit7 ih md pos) (Nat.beq ax 7)) (gsplit6 ih md pos) (Nat.beq ax 6)) (gsplit5 ih md pos) (Nat.beq ax 5)) (gsplit4 ih md pos) (Nat.beq ax 4)) (gsplit3 ih md pos) (Nat.beq ax 3)) (gsplit2 ih md pos) (Nat.beq ax 2)) (gsplit1 ih md pos) (Nat.beq ax 1)) (gsplit0 ih md pos) (Nat.beq ax 0)

theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) :=
  brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => zK_ok) (fun _ => ssplit68_ok hih md pos)) (fun _ => ssplit58_ok hih md pos)) (fun _ => ssplit57_ok hih md pos)) (fun _ => ssplit48_ok hih md pos)) (fun _ => ssplit47_ok hih md pos)) (fun _ => ssplit46_ok hih md pos)) (fun _ => ssplit38_ok hih md pos)) (fun _ => ssplit37_ok hih md pos)) (fun _ => ssplit36_ok hih md pos)) (fun _ => ssplit35_ok hih md pos)) (fun _ => ssplit28_ok hih md pos)) (fun _ => ssplit27_ok hih md pos)) (fun _ => ssplit26_ok hih md pos)) (fun _ => ssplit25_ok hih md pos)) (fun _ => ssplit24_ok hih md pos)) (fun _ => ssplit18_ok hih md pos)) (fun _ => ssplit17_ok hih md pos)) (fun _ => ssplit16_ok hih md pos)) (fun _ => ssplit15_ok hih md pos)) (fun _ => ssplit14_ok hih md pos)) (fun _ => ssplit13_ok hih md pos)) (fun _ => ssplit08_ok hih md pos)) (fun _ => ssplit07_ok hih md pos)) (fun _ => ssplit06_ok hih md pos)) (fun _ => ssplit05_ok hih md pos)) (fun _ => ssplit04_ok hih md pos)) (fun _ => ssplit03_ok hih md pos)) (fun _ => ssplit02_ok hih md pos)) (fun _ => gsplit7_ok hih md pos)) (fun _ => gsplit6_ok hih md pos)) (fun _ => gsplit5_ok hih md pos)) (fun _ => gsplit4_ok hih md pos)) (fun _ => gsplit3_ok hih md pos)) (fun _ => gsplit2_ok hih md pos)) (fun _ => gsplit1_ok hih md pos)) (fun _ => gsplit0_ok hih md pos)

-- (5) the root: the box sums written into the pair bounds (`matC`), once, which closes the root box (TZ.md §5)

def tm (k : ST) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  forceR (nmax t (Nat.add a c)) fun t' => forceR (nmin u (Nat.add b d)) fun u' =>
  forceR (nmax v (Nat.add (Nat.add a c) e)) fun v' => forceR (nmin w (Nat.add (Nat.add b d) f)) fun w' =>
  forceR (nmax x (Nat.add (Nat.add (Nat.add a c) e) g)) fun x' => forceR (nmin y (Nat.add (Nat.add (Nat.add b d) f) h)) fun y' =>
  forceR (nmax z (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i)) fun z' => forceR (nmin A (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j)) fun A' =>
  forceR (nmax B (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l)) fun B' => forceR (nmin C (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m)) fun C' =>
  forceR (nmax D (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l) n)) fun D' => forceR (nmin E (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m) o)) fun E' =>
  forceR (nmax F (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l) n) r)) fun F' => forceR (nmin G (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m) o) s)) fun G' =>
  forceR (nmax H (Nat.add c e)) fun H' => forceR (nmin I (Nat.add d f)) fun I' =>
  forceR (nmax J (Nat.add (Nat.add c e) g)) fun J' => forceR (nmin K (Nat.add (Nat.add d f) h)) fun K' =>
  forceR (nmax L (Nat.add (Nat.add (Nat.add c e) g) i)) fun L' => forceR (nmin M (Nat.add (Nat.add (Nat.add d f) h) j)) fun M' =>
  forceR (nmax N (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l)) fun N' => forceR (nmin O (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m)) fun O' =>
  forceR (nmax P (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l) n)) fun P' => forceR (nmin Q (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m) o)) fun Q' =>
  forceR (nmax R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l) n) r)) fun R' => forceR (nmin S (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m) o) s)) fun S' =>
  forceR (nmax T (Nat.add e g)) fun T' => forceR (nmin U (Nat.add f h)) fun U' =>
  forceR (nmax V (Nat.add (Nat.add e g) i)) fun V' => forceR (nmin W (Nat.add (Nat.add f h) j)) fun W' =>
  forceR (nmax X (Nat.add (Nat.add (Nat.add e g) i) l)) fun X' => forceR (nmin Y (Nat.add (Nat.add (Nat.add f h) j) m)) fun Y' =>
  forceR (nmax Z (Nat.add (Nat.add (Nat.add (Nat.add e g) i) l) n)) fun Z' => forceR (nmin aa (Nat.add (Nat.add (Nat.add (Nat.add f h) j) m) o)) fun aa' =>
  forceR (nmax ab (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add e g) i) l) n) r)) fun ab' => forceR (nmin ac (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add f h) j) m) o) s)) fun ac' =>
  forceR (nmax ad (Nat.add g i)) fun ad' => forceR (nmin ae (Nat.add h j)) fun ae' =>
  forceR (nmax af (Nat.add (Nat.add g i) l)) fun af' => forceR (nmin ag (Nat.add (Nat.add h j) m)) fun ag' =>
  forceR (nmax ah (Nat.add (Nat.add (Nat.add g i) l) n)) fun ah' => forceR (nmin ai (Nat.add (Nat.add (Nat.add h j) m) o)) fun ai' =>
  forceR (nmax aj (Nat.add (Nat.add (Nat.add (Nat.add g i) l) n) r)) fun aj' => forceR (nmin al (Nat.add (Nat.add (Nat.add (Nat.add h j) m) o) s)) fun al' =>
  forceR (nmax am (Nat.add i l)) fun am' => forceR (nmin an (Nat.add j m)) fun an' =>
  forceR (nmax ao (Nat.add (Nat.add i l) n)) fun ao' => forceR (nmin ar (Nat.add (Nat.add j m) o)) fun ar' =>
  forceR (nmax au (Nat.add (Nat.add (Nat.add i l) n) r)) fun au' => forceR (nmin av (Nat.add (Nat.add (Nat.add j m) o) s)) fun av' =>
  forceR (nmax aw (Nat.add l n)) fun aw' => forceR (nmin ax (Nat.add m o)) fun ax' =>
  forceR (nmax ay (Nat.add (Nat.add l n) r)) fun ay' => forceR (nmin az (Nat.add (Nat.add m o) s)) fun az' =>
  forceR (nmax ba (Nat.add n r)) fun ba' => forceR (nmin bb (Nat.add o s)) fun bb' =>
  k a b c d e f g h i j l m n o r s t' u' v' w' x' y' z' A' B' C' D' E' F' G' H' I' J' K' L' M' N' O' P' Q' R' S' T' U' V' W' X' Y' Z' aa' ab' ac' ad' ae' af' ag' ah' ai' aj' al' am' an' ao' ar' au' av' aw' ax' ay' az' ba' bb' bc

theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2

-- (3) multipliers (HUFF.md §5.2): entries `[1][c code][side][Yq: qb bits]`, closed by `[0]`
structure YA where
  (o P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ)

def MulOK (s : St) (y : YA) : Prop :=
  MulOKg 8 PR (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7] y.Cp y.Cm

def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) ⟨(Nat.add o 1), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.Cp, y.Cm⟩
    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) 31) fun c => forceT (Nat.add o 6) fun o1 =>
     Bool.rec (motive := fun _ => YA) ⟨(Nat.add o1 (Nat.add qb 1)), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.Cp, y.Cm⟩
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih ⟨(Nat.add o1 (Nat.add qb 1)), (Nat.add y.P0 (Nat.mul Ylo (ind (inr 0 i j)))), (Nat.add y.P1 (Nat.mul Ylo (ind (inr 1 i j)))), (Nat.add y.P2 (Nat.mul Ylo (ind (inr 2 i j)))), (Nat.add y.P3 (Nat.mul Ylo (ind (inr 3 i j)))), (Nat.add y.P4 (Nat.mul Ylo (ind (inr 4 i j)))), (Nat.add y.P5 (Nat.mul Ylo (ind (inr 5 i j)))), (Nat.add y.P6 (Nat.mul Ylo (ind (inr 6 i j)))), (Nat.add y.P7 (Nat.mul Ylo (ind (inr 7 i j)))), (Nat.add y.S0 (Nat.mul Yhi (ind (inr 0 i j)))), (Nat.add y.S1 (Nat.mul Yhi (ind (inr 1 i j)))), (Nat.add y.S2 (Nat.mul Yhi (ind (inr 2 i j)))), (Nat.add y.S3 (Nat.mul Yhi (ind (inr 3 i j)))), (Nat.add y.S4 (Nat.mul Yhi (ind (inr 4 i j)))), (Nat.add y.S5 (Nat.mul Yhi (ind (inr 5 i j)))), (Nat.add y.S6 (Nat.mul Yhi (ind (inr 6 i j)))), (Nat.add y.S7 (Nat.mul Yhi (ind (inr 7 i j)))), (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))), (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0))))⟩)
      (Nat.blt c 28))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)

def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel

theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := fun _ _ => by simp

theorem ystep_ok (s : St) (qb w : ℕ) {ih : YA → YA} (hih : ∀ y, MulOK s y → MulOK s (ih y)) (y : YA) (h : MulOK s y) :
    MulOK s (ystep (toCl s).L (toCl s).A (toCl s).B qb w ih y) := by
  unfold ystep
  simp only [forceT_eq]
  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => h) fun hc => hih _ (mul_step hPR rfl rfl h (Nat.blt_eq.mp hc) _ _)

theorem ydec_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOK s y → MulOK s (ydec (toCl s).L (toCl s).A (toCl s).B qb w fuel y)
  | 0, _, h => h
  | n + 1, y, h => ystep_ok s qb w (ydec_ok s qb w n) y h

/-- (3) the minorant leaf on the polytope cell (`mcheckG` unrolled): per term its kind, weight and points on its
effective range; the accumulated multipliers `P, S, Cp, Cm` -/
def mcheckP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 : ℕ) (P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 11540560 (mcK (tf f) false s.l0 k01 m01 p01 r01))) (Nat.mul 8686366 (mcK (tf f) false (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 34265560 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 40853477 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 58252863 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 100000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 200000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k08 m08 p08 r08))) (Nat.mul 23367038 (mcK (tf f) false s.l1 k12 m12 p12 r12))) (Nat.mul 27290752 (mcK (tf f) false (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 39869581 (mcK (tf f) false (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 35315115 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 59146522 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 83494272 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 100000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k18 m18 p18 r18))) (Nat.mul 30853002 (mcK (tf f) false s.l2 k23 m23 p23 r23))) (Nat.mul 42637189 (mcK (tf f) false (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 51444051 (mcK (tf f) false (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 60838648 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 59146522 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 58252863 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7) k28 m28 p28 r28))) (Nat.mul 34239398 (mcK (tf f) false s.l3 k34 m34 p34 r34))) (Nat.mul 60144115 (mcK (tf f) false (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 51444051 (mcK (tf f) false (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 35315115 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 40853477 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7) k38 m38 p38 r38))) (Nat.mul 34239398 (mcK (tf f) false s.l4 k45 m45 p45 r45))) (Nat.mul 42637189 (mcK (tf f) false (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 39869581 (mcK (tf f) false (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 34265560 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7) k48 m48 p48 r48))) (Nat.mul 30853002 (mcK (tf f) false s.l5 k56 m56 p56 r56))) (Nat.mul 27290752 (mcK (tf f) false (Nat.add s.l5 s.l6) k57 m57 p57 r57))) (Nat.mul 8686366 (mcK (tf f) false (Nat.add (Nat.add s.l5 s.l6) s.l7) k58 m58 p58 r58))) (Nat.mul 23367038 (mcK (tf f) false s.l6 k67 m67 p67 r67))) (Nat.mul 11540560 (mcK (tf f) false s.l7 k78 m78 p78 r78))) Cp) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub s.u0 s.l0) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 11540560 (mwT k01 m01))) (Nat.mul 8686366 (mwT k03 m03))) (Nat.mul 34265560 (mwT k04 m04))) (Nat.mul 40853477 (mwT k05 m05))) (Nat.mul 58252863 (mwT k06 m06))) (Nat.mul 100000000 (mwT k07 m07))) (Nat.mul 200000000 (mwT k08 m08)))) P0) (Nat.add (Nat.add (Nat.mul 1024000000000 27130) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 11540560 (mslK (tf f) k01 m01 p01 r01))) (Nat.mul 8686366 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 34265560 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 40853477 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 58252863 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08)))) S0)))) (Nat.mul (Nat.sub s.u1 s.l1) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8686366 (mwT k03 m03))) (Nat.mul 34265560 (mwT k04 m04))) (Nat.mul 40853477 (mwT k05 m05))) (Nat.mul 58252863 (mwT k06 m06))) (Nat.mul 100000000 (mwT k07 m07))) (Nat.mul 200000000 (mwT k08 m08))) (Nat.mul 23367038 (mwT k12 m12))) (Nat.mul 27290752 (mwT k13 m13))) (Nat.mul 39869581 (mwT k14 m14))) (Nat.mul 35315115 (mwT k15 m15))) (Nat.mul 59146522 (mwT k16 m16))) (Nat.mul 83494272 (mwT k17 m17))) (Nat.mul 100000000 (mwT k18 m18)))) P1) (Nat.add (Nat.add (Nat.mul 1024000000000 50593) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8686366 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 34265560 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 40853477 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 58252863 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 23367038 (mslK (tf f) k12 m12 p12 r12))) (Nat.mul 27290752 (mslK (tf f) k13 m13 p13 r13))) (Nat.mul 39869581 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 35315115 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 59146522 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 83494272 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000 (mslK (tf f) k18 m18 p18 r18)))) S1)))) (Nat.mul (Nat.sub s.u2 s.l2) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8686366 (mwT k03 m03))) (Nat.mul 34265560 (mwT k04 m04))) (Nat.mul 40853477 (mwT k05 m05))) (Nat.mul 58252863 (mwT k06 m06))) (Nat.mul 100000000 (mwT k07 m07))) (Nat.mul 200000000 (mwT k08 m08))) (Nat.mul 27290752 (mwT k13 m13))) (Nat.mul 39869581 (mwT k14 m14))) (Nat.mul 35315115 (mwT k15 m15))) (Nat.mul 59146522 (mwT k16 m16))) (Nat.mul 83494272 (mwT k17 m17))) (Nat.mul 100000000 (mwT k18 m18))) (Nat.mul 30853002 (mwT k23 m23))) (Nat.mul 42637189 (mwT k24 m24))) (Nat.mul 51444051 (mwT k25 m25))) (Nat.mul 60838648 (mwT k26 m26))) (Nat.mul 59146522 (mwT k27 m27))) (Nat.mul 58252863 (mwT k28 m28)))) P2) (Nat.add (Nat.add (Nat.mul 1024000000000 66037) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8686366 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 34265560 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 40853477 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 58252863 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 27290752 (mslK (tf f) k13 m13 p13 r13))) (Nat.mul 39869581 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 35315115 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 59146522 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 83494272 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 30853002 (mslK (tf f) k23 m23 p23 r23))) (Nat.mul 42637189 (mslK (tf f) k24 m24 p24 r24))) (Nat.mul 51444051 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 60838648 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 59146522 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 58252863 (mslK (tf f) k28 m28 p28 r28)))) S2)))) (Nat.mul (Nat.sub s.u3 s.l3) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 34265560 (mwT k04 m04))) (Nat.mul 40853477 (mwT k05 m05))) (Nat.mul 58252863 (mwT k06 m06))) (Nat.mul 100000000 (mwT k07 m07))) (Nat.mul 200000000 (mwT k08 m08))) (Nat.mul 39869581 (mwT k14 m14))) (Nat.mul 35315115 (mwT k15 m15))) (Nat.mul 59146522 (mwT k16 m16))) (Nat.mul 83494272 (mwT k17 m17))) (Nat.mul 100000000 (mwT k18 m18))) (Nat.mul 42637189 (mwT k24 m24))) (Nat.mul 51444051 (mwT k25 m25))) (Nat.mul 60838648 (mwT k26 m26))) (Nat.mul 59146522 (mwT k27 m27))) (Nat.mul 58252863 (mwT k28 m28))) (Nat.mul 34239398 (mwT k34 m34))) (Nat.mul 60144115 (mwT k35 m35))) (Nat.mul 51444051 (mwT k36 m36))) (Nat.mul 35315115 (mwT k37 m37))) (Nat.mul 40853477 (mwT k38 m38)))) P3) (Nat.add (Nat.add (Nat.mul 1024000000000 74577) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 34265560 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 40853477 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 58252863 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 39869581 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 35315115 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 59146522 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 83494272 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 42637189 (mslK (tf f) k24 m24 p24 r24))) (Nat.mul 51444051 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 60838648 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 59146522 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 58252863 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 34239398 (mslK (tf f) k34 m34 p34 r34))) (Nat.mul 60144115 (mslK (tf f) k35 m35 p35 r35))) (Nat.mul 51444051 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 35315115 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 40853477 (mslK (tf f) k38 m38 p38 r38)))) S3)))) (Nat.mul (Nat.sub s.u4 s.l4) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 40853477 (mwT k05 m05))) (Nat.mul 58252863 (mwT k06 m06))) (Nat.mul 100000000 (mwT k07 m07))) (Nat.mul 200000000 (mwT k08 m08))) (Nat.mul 35315115 (mwT k15 m15))) (Nat.mul 59146522 (mwT k16 m16))) (Nat.mul 83494272 (mwT k17 m17))) (Nat.mul 100000000 (mwT k18 m18))) (Nat.mul 51444051 (mwT k25 m25))) (Nat.mul 60838648 (mwT k26 m26))) (Nat.mul 59146522 (mwT k27 m27))) (Nat.mul 58252863 (mwT k28 m28))) (Nat.mul 60144115 (mwT k35 m35))) (Nat.mul 51444051 (mwT k36 m36))) (Nat.mul 35315115 (mwT k37 m37))) (Nat.mul 40853477 (mwT k38 m38))) (Nat.mul 34239398 (mwT k45 m45))) (Nat.mul 42637189 (mwT k46 m46))) (Nat.mul 39869581 (mwT k47 m47))) (Nat.mul 34265560 (mwT k48 m48)))) P4) (Nat.add (Nat.add (Nat.mul 1024000000000 74577) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 40853477 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 58252863 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 35315115 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 59146522 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 83494272 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 51444051 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 60838648 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 59146522 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 58252863 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 60144115 (mslK (tf f) k35 m35 p35 r35))) (Nat.mul 51444051 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 35315115 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 40853477 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 34239398 (mslK (tf f) k45 m45 p45 r45))) (Nat.mul 42637189 (mslK (tf f) k46 m46 p46 r46))) (Nat.mul 39869581 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 34265560 (mslK (tf f) k48 m48 p48 r48)))) S4)))) (Nat.mul (Nat.sub s.u5 s.l5) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 58252863 (mwT k06 m06))) (Nat.mul 100000000 (mwT k07 m07))) (Nat.mul 200000000 (mwT k08 m08))) (Nat.mul 59146522 (mwT k16 m16))) (Nat.mul 83494272 (mwT k17 m17))) (Nat.mul 100000000 (mwT k18 m18))) (Nat.mul 60838648 (mwT k26 m26))) (Nat.mul 59146522 (mwT k27 m27))) (Nat.mul 58252863 (mwT k28 m28))) (Nat.mul 51444051 (mwT k36 m36))) (Nat.mul 35315115 (mwT k37 m37))) (Nat.mul 40853477 (mwT k38 m38))) (Nat.mul 42637189 (mwT k46 m46))) (Nat.mul 39869581 (mwT k47 m47))) (Nat.mul 34265560 (mwT k48 m48))) (Nat.mul 30853002 (mwT k56 m56))) (Nat.mul 27290752 (mwT k57 m57))) (Nat.mul 8686366 (mwT k58 m58)))) P5) (Nat.add (Nat.add (Nat.mul 1024000000000 66037) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 58252863 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 59146522 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 83494272 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 60838648 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 59146522 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 58252863 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 51444051 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 35315115 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 40853477 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 42637189 (mslK (tf f) k46 m46 p46 r46))) (Nat.mul 39869581 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 34265560 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 30853002 (mslK (tf f) k56 m56 p56 r56))) (Nat.mul 27290752 (mslK (tf f) k57 m57 p57 r57))) (Nat.mul 8686366 (mslK (tf f) k58 m58 p58 r58)))) S5)))) (Nat.mul (Nat.sub s.u6 s.l6) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000 (mwT k07 m07))) (Nat.mul 200000000 (mwT k08 m08))) (Nat.mul 83494272 (mwT k17 m17))) (Nat.mul 100000000 (mwT k18 m18))) (Nat.mul 59146522 (mwT k27 m27))) (Nat.mul 58252863 (mwT k28 m28))) (Nat.mul 35315115 (mwT k37 m37))) (Nat.mul 40853477 (mwT k38 m38))) (Nat.mul 39869581 (mwT k47 m47))) (Nat.mul 34265560 (mwT k48 m48))) (Nat.mul 27290752 (mwT k57 m57))) (Nat.mul 8686366 (mwT k58 m58))) (Nat.mul 23367038 (mwT k67 m67)))) P6) (Nat.add (Nat.add (Nat.mul 1024000000000 50593) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 83494272 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 59146522 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 58252863 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 35315115 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 40853477 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 39869581 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 34265560 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 27290752 (mslK (tf f) k57 m57 p57 r57))) (Nat.mul 8686366 (mslK (tf f) k58 m58 p58 r58))) (Nat.mul 23367038 (mslK (tf f) k67 m67 p67 r67)))) S6)))) (Nat.mul (Nat.sub s.u7 s.l7) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000 (mwT k08 m08))) (Nat.mul 100000000 (mwT k18 m18))) (Nat.mul 58252863 (mwT k28 m28))) (Nat.mul 40853477 (mwT k38 m38))) (Nat.mul 34265560 (mwT k48 m48))) (Nat.mul 8686366 (mwT k58 m58))) (Nat.mul 11540560 (mwT k78 m78)))) P7) (Nat.add (Nat.add (Nat.mul 1024000000000 27130) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 100000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 58252863 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 40853477 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 34265560 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 8686366 (mslK (tf f) k58 m58 p58 r58))) (Nat.mul 11540560 (mslK (tf f) k78 m78 p78 r78)))) S7))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 27130 s.l0)) (Nat.mul 50593 s.l1)) (Nat.mul 66037 s.l2)) (Nat.mul 74577 s.l3)) (Nat.mul 74577 s.l4)) (Nat.mul 66037 s.l5)) (Nat.mul 50593 s.l6)) (Nat.mul 27130 s.l7))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 11540560 (mvKF top bk (tf f) s.l0 (uc s.l0 s.u0) k01 m01 p01 r01))) (Nat.mul 8686366 (mvKF top bk (tf f) (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (uc (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2))) k03 m03 p03 r03))) (Nat.mul 34265560 (mvKF top bk (tf f) (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (uc (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3))) k04 m04 p04 r04))) (Nat.mul 40853477 (mvKF top bk (tf f) (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (uc (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4))) k05 m05 p05 r05))) (Nat.mul 58252863 (mvKF top bk (tf f) (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5))) k06 m06 p06 r06))) (Nat.mul 100000000 (mvKF top bk (tf f) (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6))) k07 m07 p07 r07))) (Nat.mul 200000000 (mvKF top bk (tf f) (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7))) k08 m08 p08 r08))) (Nat.mul 23367038 (mvKF top bk (tf f) s.l1 (uc s.l1 s.u1) k12 m12 p12 r12))) (Nat.mul 27290752 (mvKF top bk (tf f) (nmax s.A13 (Nat.add s.l1 s.l2)) (uc (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2))) k13 m13 p13 r13))) (Nat.mul 39869581 (mvKF top bk (tf f) (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (uc (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3))) k14 m14 p14 r14))) (Nat.mul 35315115 (mvKF top bk (tf f) (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (uc (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4))) k15 m15 p15 r15))) (Nat.mul 59146522 (mvKF top bk (tf f) (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5))) k16 m16 p16 r16))) (Nat.mul 83494272 (mvKF top bk (tf f) (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6))) k17 m17 p17 r17))) (Nat.mul 100000000 (mvKF top bk (tf f) (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7))) k18 m18 p18 r18))) (Nat.mul 30853002 (mvKF top bk (tf f) s.l2 (uc s.l2 s.u2) k23 m23 p23 r23))) (Nat.mul 42637189 (mvKF top bk (tf f) (nmax s.A24 (Nat.add s.l2 s.l3)) (uc (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3))) k24 m24 p24 r24))) (Nat.mul 51444051 (mvKF top bk (tf f) (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (uc (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4))) k25 m25 p25 r25))) (Nat.mul 60838648 (mvKF top bk (tf f) (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (uc (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5))) k26 m26 p26 r26))) (Nat.mul 59146522 (mvKF top bk (tf f) (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6))) k27 m27 p27 r27))) (Nat.mul 58252863 (mvKF top bk (tf f) (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7))) k28 m28 p28 r28))) (Nat.mul 34239398 (mvKF top bk (tf f) s.l3 (uc s.l3 s.u3) k34 m34 p34 r34))) (Nat.mul 60144115 (mvKF top bk (tf f) (nmax s.A35 (Nat.add s.l3 s.l4)) (uc (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4))) k35 m35 p35 r35))) (Nat.mul 51444051 (mvKF top bk (tf f) (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (uc (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5))) k36 m36 p36 r36))) (Nat.mul 35315115 (mvKF top bk (tf f) (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (uc (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6))) k37 m37 p37 r37))) (Nat.mul 40853477 (mvKF top bk (tf f) (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7))) k38 m38 p38 r38))) (Nat.mul 34239398 (mvKF top bk (tf f) s.l4 (uc s.l4 s.u4) k45 m45 p45 r45))) (Nat.mul 42637189 (mvKF top bk (tf f) (nmax s.A46 (Nat.add s.l4 s.l5)) (uc (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5))) k46 m46 p46 r46))) (Nat.mul 39869581 (mvKF top bk (tf f) (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (uc (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6))) k47 m47 p47 r47))) (Nat.mul 34265560 (mvKF top bk (tf f) (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (uc (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7))) k48 m48 p48 r48))) (Nat.mul 30853002 (mvKF top bk (tf f) s.l5 (uc s.l5 s.u5) k56 m56 p56 r56))) (Nat.mul 27290752 (mvKF top bk (tf f) (nmax s.A57 (Nat.add s.l5 s.l6)) (uc (nmax s.A57 (Nat.add s.l5 s.l6)) (nmin s.B57 (Nat.add s.u5 s.u6))) k57 m57 p57 r57))) (Nat.mul 8686366 (mvKF top bk (tf f) (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (uc (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7))) k58 m58 p58 r58))) (Nat.mul 23367038 (mvKF top bk (tf f) s.l6 (uc s.l6 s.u6) k67 m67 p67 r67))) (Nat.mul 11540560 (mvKF top bk (tf f) s.l7 (uc s.l7 s.u7) k78 m78 p78 r78))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 11540560 (mcK (tf f) true s.l0 k01 m01 p01 r01))) (Nat.mul 8686366 (mcK (tf f) true (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 34265560 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 40853477 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 58252863 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 100000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 200000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k08 m08 p08 r08))) (Nat.mul 23367038 (mcK (tf f) true s.l1 k12 m12 p12 r12))) (Nat.mul 27290752 (mcK (tf f) true (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 39869581 (mcK (tf f) true (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 35315115 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 59146522 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 83494272 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 100000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k18 m18 p18 r18))) (Nat.mul 30853002 (mcK (tf f) true s.l2 k23 m23 p23 r23))) (Nat.mul 42637189 (mcK (tf f) true (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 51444051 (mcK (tf f) true (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 60838648 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 59146522 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 58252863 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7) k28 m28 p28 r28))) (Nat.mul 34239398 (mcK (tf f) true s.l3 k34 m34 p34 r34))) (Nat.mul 60144115 (mcK (tf f) true (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 51444051 (mcK (tf f) true (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 35315115 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 40853477 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7) k38 m38 p38 r38))) (Nat.mul 34239398 (mcK (tf f) true s.l4 k45 m45 p45 r45))) (Nat.mul 42637189 (mcK (tf f) true (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 39869581 (mcK (tf f) true (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 34265560 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7) k48 m48 p48 r48))) (Nat.mul 30853002 (mcK (tf f) true s.l5 k56 m56 p56 r56))) (Nat.mul 27290752 (mcK (tf f) true (Nat.add s.l5 s.l6) k57 m57 p57 r57))) (Nat.mul 8686366 (mcK (tf f) true (Nat.add (Nat.add s.l5 s.l6) s.l7) k58 m58 p58 r58))) (Nat.mul 23367038 (mcK (tf f) true s.l6 k67 m67 p67 r67))) (Nat.mul 11540560 (mcK (tf f) true s.l7 k78 m78 p78 r78))) Cm)))) (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (mokI f s.l7 s.u7 k78 m78 p78 r78) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l6 s.u6 k67 m67 p67 r67) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7)) k58 m58 p58 r58) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A57 (Nat.add s.l5 s.l6)) (nmin s.B57 (Nat.add s.u5 s.u6)) k57 m57 p57 r57) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l5 s.u5 k56 m56 p56 r56) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7)) k48 m48 p48 r48) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) k47 m47 p47 r47) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5)) k46 m46 p46 r46) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l4 s.u4 k45 m45 p45 r45) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7)) k38 m38 p38 r38) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) k37 m37 p37 r37) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) k36 m36 p36 r36) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4)) k35 m35 p35 r35) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l3 s.u3 k34 m34 p34 r34) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7)) k28 m28 p28 r28) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) k27 m27 p27 r27) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) k26 m26 p26 r26) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) k25 m25 p25 r25) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3)) k24 m24 p24 r24) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l2 s.u2 k23 m23 p23 r23) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) k18 m18 p18 r18) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) k17 m17 p17 r17) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) k16 m16 p16 r16) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) k15 m15 p15 r15) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) k14 m14 p14 r14) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2)) k13 m13 p13 r13) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l1 s.u1 k12 m12 p12 r12) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) k08 m08 p08 r08) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) k07 m07 p07 r07) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) k06 m06 p06 r06) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) k05 m05 p05 r05) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) k04 m04 p04 r04) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) k03 m03 p03 r03) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l0 s.u0 k01 m01 p01 r01) (true))))))))))))))))))))))))))))))))))) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l7 s.u7) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l6 s.u6) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l5 s.u5) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l4 s.u4) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l3 s.u3) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l2 s.u2) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l1 s.u1) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l0 s.u0) (true))))))))))

theorem mcheckP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 : ℕ) (P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm = true) :
    mcheckGX (mokI f) top bk (tf f) 8 BS TS cN (toCl s) [(k01, m01, p01, r01), (k03, m03, p03, r03), (k04, m04, p04, r04), (k05, m05, p05, r05), (k06, m06, p06, r06), (k07, m07, p07, r07), (k08, m08, p08, r08), (k12, m12, p12, r12), (k13, m13, p13, r13), (k14, m14, p14, r14), (k15, m15, p15, r15), (k16, m16, p16, r16), (k17, m17, p17, r17), (k18, m18, p18, r18), (k23, m23, p23, r23), (k24, m24, p24, r24), (k25, m25, p25, r25), (k26, m26, p26, r26), (k27, m27, p27, r27), (k28, m28, p28, r28), (k34, m34, p34, r34), (k35, m35, p35, r35), (k36, m36, p36, r36), (k37, m37, p37, r37), (k38, m38, p38, r38), (k45, m45, p45, r45), (k46, m46, p46, r46), (k47, m47, p47, r47), (k48, m48, p48, r48), (k56, m56, p56, r56), (k57, m57, p57, r57), (k58, m58, p58, r58), (k67, m67, p67, r67), (k78, m78, p78, r78)]
      [P0, P1, P2, P3, P4, P5, P6, P7] [S0, S1, S2, S3, S4, S5, S6, S7] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq, mvKF_eq] at h; exact h

/-- (bench) the point-index table, 7 bits per entry -/
def JTAB : ℕ := 0x176e21b712d428716cc18d62bd68f56651a940fc89b4e7cea47a5c9007504a38102830418d8134643982e20b1522386121a40a131e2458a

/-- the polytope minorant leaf (HUFF.md §5): the payload length when the check passes, else `0` -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  forceR (nmax s.A02 (Nat.add s.l0 s.l1)) fun L02 => forceR (nmin s.B02 (Nat.add s.u0 s.u1)) fun U02 =>
  forceR (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) fun L03 => forceR (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) fun U03 =>
  forceR (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) fun L04 => forceR (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) fun U04 =>
  forceR (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) fun L05 => forceR (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) fun U05 =>
  forceR (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) fun L06 => forceR (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) fun U06 =>
  forceR (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) fun L07 => forceR (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) fun U07 =>
  forceR (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) fun L08 => forceR (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) fun U08 =>
  forceR (nmax s.A13 (Nat.add s.l1 s.l2)) fun L13 => forceR (nmin s.B13 (Nat.add s.u1 s.u2)) fun U13 =>
  forceR (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) fun L14 => forceR (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) fun U14 =>
  forceR (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) fun L15 => forceR (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) fun U15 =>
  forceR (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) fun L16 => forceR (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) fun U16 =>
  forceR (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) fun L17 => forceR (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) fun U17 =>
  forceR (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) fun L18 => forceR (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) fun U18 =>
  forceR (nmax s.A24 (Nat.add s.l2 s.l3)) fun L24 => forceR (nmin s.B24 (Nat.add s.u2 s.u3)) fun U24 =>
  forceR (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) fun L25 => forceR (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) fun U25 =>
  forceR (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) fun L26 => forceR (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) fun U26 =>
  forceR (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) fun L27 => forceR (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) fun U27 =>
  forceR (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) fun L28 => forceR (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7)) fun U28 =>
  forceR (nmax s.A35 (Nat.add s.l3 s.l4)) fun L35 => forceR (nmin s.B35 (Nat.add s.u3 s.u4)) fun U35 =>
  forceR (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) fun L36 => forceR (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) fun U36 =>
  forceR (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) fun L37 => forceR (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) fun U37 =>
  forceR (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) fun L38 => forceR (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7)) fun U38 =>
  forceR (nmax s.A46 (Nat.add s.l4 s.l5)) fun L46 => forceR (nmin s.B46 (Nat.add s.u4 s.u5)) fun U46 =>
  forceR (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) fun L47 => forceR (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) fun U47 =>
  forceR (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) fun L48 => forceR (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7)) fun U48 =>
  forceR (nmax s.A57 (Nat.add s.l5 s.l6)) fun L57 => forceR (nmin s.B57 (Nat.add s.u5 s.u6)) fun U57 =>
  forceR (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) fun L58 => forceR (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7)) fun U58 =>
  forceR (nmax s.A68 (Nat.add s.l6 s.l7)) fun L68 => forceR (nmin s.B68 (Nat.add s.u6 s.u7)) fun U68 =>
  forceR 0 fun o0 =>
  dec4P 10 w o0 s.l0 s.u0 fun k01 m01 p01 r01 o1 =>
  dec4P 10 w o1 L03 U03 fun k03 m03 p03 r03 o2 =>
  dec4P 10 w o2 L04 U04 fun k04 m04 p04 r04 o3 =>
  dec4P 10 w o3 L05 U05 fun k05 m05 p05 r05 o4 =>
  dec4P 10 w o4 L06 U06 fun k06 m06 p06 r06 o5 =>
  dec4P 10 w o5 L07 U07 fun k07 m07 p07 r07 o6 =>
  dec4P 10 w o6 L08 U08 fun k08 m08 p08 r08 o7 =>
  dec4P 10 w o7 s.l1 s.u1 fun k12 m12 p12 r12 o8 =>
  dec4P 10 w o8 L13 U13 fun k13 m13 p13 r13 o9 =>
  dec4P 10 w o9 L14 U14 fun k14 m14 p14 r14 o10 =>
  dec4P 10 w o10 L15 U15 fun k15 m15 p15 r15 o11 =>
  dec4P 10 w o11 L16 U16 fun k16 m16 p16 r16 o12 =>
  dec4P 10 w o12 L17 U17 fun k17 m17 p17 r17 o13 =>
  dec4P 10 w o13 L18 U18 fun k18 m18 p18 r18 o14 =>
  dec4P 10 w o14 s.l2 s.u2 fun k23 m23 p23 r23 o15 =>
  dec4P 10 w o15 L24 U24 fun k24 m24 p24 r24 o16 =>
  dec4P 10 w o16 L25 U25 fun k25 m25 p25 r25 o17 =>
  dec4P 10 w o17 L26 U26 fun k26 m26 p26 r26 o18 =>
  dec4P 10 w o18 L27 U27 fun k27 m27 p27 r27 o19 =>
  dec4P 10 w o19 L28 U28 fun k28 m28 p28 r28 o20 =>
  dec4P 10 w o20 s.l3 s.u3 fun k34 m34 p34 r34 o21 =>
  dec4P 10 w o21 L35 U35 fun k35 m35 p35 r35 o22 =>
  dec4P 10 w o22 L36 U36 fun k36 m36 p36 r36 o23 =>
  dec4P 10 w o23 L37 U37 fun k37 m37 p37 r37 o24 =>
  dec4P 10 w o24 L38 U38 fun k38 m38 p38 r38 o25 =>
  dec4P 10 w o25 s.l4 s.u4 fun k45 m45 p45 r45 o26 =>
  dec4P 10 w o26 L46 U46 fun k46 m46 p46 r46 o27 =>
  dec4P 10 w o27 L47 U47 fun k47 m47 p47 r47 o28 =>
  dec4P 10 w o28 L48 U48 fun k48 m48 p48 r48 o29 =>
  dec4P 10 w o29 s.l5 s.u5 fun k56 m56 p56 r56 o30 =>
  dec4P 10 w o30 L57 U57 fun k57 m57 p57 r57 o31 =>
  dec4P 10 w o31 L58 U58 fun k58 m58 p58 r58 o32 =>
  dec4P 10 w o32 s.l6 s.u6 fun k67 m67 p67 r67 o33 =>
  dec4P 10 w o33 s.l7 s.u7 fun k78 m78 p78 r78 o34 =>
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 y.P0 y.P1 y.P2 y.P3 y.P4 y.P5 y.P6 y.P7 y.S0 y.S1 y.S2 y.S3 y.S4 y.S5 y.S6 y.S7 y.Cp y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 13 w 42 ⟨o34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  unfold mleafP at h
  simp (config := { maxSteps := 4000000 }) only [dec4P, forceR_eq] at h
  exact mcheckGX_sound (f := tf pb) (mtermTI hlb hpt) hPR hTS (ydec_ok s 13 w 42 _ (MulOK_zero s _)) (mcheckP_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h))

/-- (kind 8) the Farkas leaf (HUFF.md §6): the multiplier list only (`Yq` in 13 bits), accepted when the multiplier form
is negative on the whole box -/
def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7] 8)) y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 13 w 42 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

/-- a leaf (bit 0 clear): the reflected half-space (`u7 < l0`, no further bits), else bit 1 the kind (minorant leaf, or
Farkas leaf) with its payload from bit 2 -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M => Bool.rec (motive := fun _ => ℕ)
    (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩)
        (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1) (Nat.blt u7 l0)

theorem fleaf_ok (w : ℕ) (s : St) (h : fleaf w s ≠ 0) : Covered (toCl s) :=
  farkas_cov (ydec_ok s 13 w 42 _ (MulOK_zero s 0)) (brec_ne h)

theorem leafStep_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (pos w : ℕ) :
    CovK (leafStep top bk tD bD pb R pos w) := by
  intro s h
  have h' : Bool.rec (motive := fun _ => ℕ) (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)
      (fleaf (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) (Nat.add pos 1) (Nat.blt s.u7 s.l0) ≠ 0 := h
  cases hs : Nat.blt s.u7 s.l0
  · rw [hs, forceR_eq] at h'
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h'; exact h' rfl
    · rw [hk] at h'; exact fleaf_ok _ s fun h0 => by rw [h0] at h'; exact h' rfl
  · intro g hg
    right
    have h1 : g 7 ≤ (s.u7 : ℝ) / SC := (hg.1 7 (by norm_num)).2
    have h2 : (s.l0 : ℝ) / SC ≤ g 0 := (hg.1 0 (by norm_num)).1
    have : (s.u7 : ℝ) / SC < (s.l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast Nat.blt_eq.mp hs) SC_pos
    show g 7 < g 0
    linarith

/-- the leaf's window: a leaf word is at most 480 bits, so its fields are read from a 480-bit slice -/
def WMASK : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

/-- (limb-table walks) the WIN-bit window at `pos` of a walk stored as overlapping limbs (`f k` holds bits
`[k·32768, k·32768 + 33248)`) -/
def rdw (f : ℕ → ℕ) (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (f (Nat.div pos 32768)) (Nat.mod pos 32768)) WMASK

/-- a node: bit `pos` selects split (`[1]`, then the axis codeword; the children from the bit after it) or leaf (`[0]`) -/
def node (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos (bits pos))
    (splitAx ih (Nat.land (Nat.shiftRight (bits pos) 7) 1) (Nat.add pos 8) (Nat.land (Nat.shiftRight (bits pos) 1) 63))
    (Nat.beq (Nat.land (bits pos) 1) 1)

/-- the walk on closed cells: no node tightening, the splits close their children (TZ.md §5) -/
def walkC (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => node top bk tD bD pb R bits ih pos) fuel

/-- the walk from a root box: the box sums close it (`tm`, once), then `walkC` -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (fuel : ℕ) : WF :=
  fun pos => tm (walkC top bk tD bD pb R bits fuel pos)

theorem forceT_cov {x : ℕ} {k : ℕ → ST} (h : CovK (k x)) : CovK (forceT x k) := by rw [forceT_eq]; exact h

theorem walkC_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) :
    ∀ fuel, WalkOK (walkC top bk tD bD pb R bits fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => show CovK (node top bk tD bD pb R bits (walkC top bk tD bD pb R bits n) pos) from
      brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
      (splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _ _)

theorem walk_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) :=
  fun fuel pos => tm_ok (walkC_ok hlb hD hpt hR bits fuel pos)

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) (fuel e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)

/-- (chunked walks) field-wise equality of two states -/
def stEq (a b : St) : Bool := Nat.beq a.l0 b.l0 && Nat.beq a.u0 b.u0 && Nat.beq a.l1 b.l1 && Nat.beq a.u1 b.u1 && Nat.beq a.l2 b.l2 && Nat.beq a.u2 b.u2 && Nat.beq a.l3 b.l3 && Nat.beq a.u3 b.u3 && Nat.beq a.l4 b.l4 && Nat.beq a.u4 b.u4 && Nat.beq a.l5 b.l5 && Nat.beq a.u5 b.u5 && Nat.beq a.l6 b.l6 && Nat.beq a.u6 b.u6 && Nat.beq a.l7 b.l7 && Nat.beq a.u7 b.u7 && Nat.beq a.A02 b.A02 && Nat.beq a.B02 b.B02 && Nat.beq a.A03 b.A03 && Nat.beq a.B03 b.B03 && Nat.beq a.A04 b.A04 && Nat.beq a.B04 b.B04 && Nat.beq a.A05 b.A05 && Nat.beq a.B05 b.B05 && Nat.beq a.A06 b.A06 && Nat.beq a.B06 b.B06 && Nat.beq a.A07 b.A07 && Nat.beq a.B07 b.B07 && Nat.beq a.A08 b.A08 && Nat.beq a.B08 b.B08 && Nat.beq a.A13 b.A13 && Nat.beq a.B13 b.B13 && Nat.beq a.A14 b.A14 && Nat.beq a.B14 b.B14 && Nat.beq a.A15 b.A15 && Nat.beq a.B15 b.B15 && Nat.beq a.A16 b.A16 && Nat.beq a.B16 b.B16 && Nat.beq a.A17 b.A17 && Nat.beq a.B17 b.B17 && Nat.beq a.A18 b.A18 && Nat.beq a.B18 b.B18 && Nat.beq a.A24 b.A24 && Nat.beq a.B24 b.B24 && Nat.beq a.A25 b.A25 && Nat.beq a.B25 b.B25 && Nat.beq a.A26 b.A26 && Nat.beq a.B26 b.B26 && Nat.beq a.A27 b.A27 && Nat.beq a.B27 b.B27 && Nat.beq a.A28 b.A28 && Nat.beq a.B28 b.B28 && Nat.beq a.A35 b.A35 && Nat.beq a.B35 b.B35 && Nat.beq a.A36 b.A36 && Nat.beq a.B36 b.B36 && Nat.beq a.A37 b.A37 && Nat.beq a.B37 b.B37 && Nat.beq a.A38 b.A38 && Nat.beq a.B38 b.B38 && Nat.beq a.A46 b.A46 && Nat.beq a.B46 b.B46 && Nat.beq a.A47 b.A47 && Nat.beq a.B47 b.B47 && Nat.beq a.A48 b.A48 && Nat.beq a.B48 b.B48 && Nat.beq a.A57 b.A57 && Nat.beq a.B57 b.B57 && Nat.beq a.A58 b.A58 && Nat.beq a.B58 b.B58 && Nat.beq a.A68 b.A68 && Nat.beq a.B68 b.B68 && Nat.beq a.M b.M
theorem St_eq {a b : St} (h : stEq a b = true) : a = b := by
  cases a; cases b
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩, h36⟩, h37⟩, h38⟩, h39⟩, h40⟩, h41⟩, h42⟩, h43⟩, h44⟩, h45⟩, h46⟩, h47⟩, h48⟩, h49⟩, h50⟩, h51⟩, h52⟩, h53⟩, h54⟩, h55⟩, h56⟩, h57⟩, h58⟩, h59⟩, h60⟩, h61⟩, h62⟩, h63⟩, h64⟩, h65⟩, h66⟩, h67⟩, h68⟩, h69⟩, h70⟩, h71⟩, h72⟩ := h
  subst_vars; rfl
/-- the continuation that accepts exactly the state `t` -/
def kEq (t : St) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M => Bool.rec (motive := fun _ => ℕ) 0 1 (stEq ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩ t)
theorem kEq_ok {t : St} (h : Covered (toCl t)) : CovK (kEq t) := fun s hs => by
  have e : U (kEq t) s = Bool.rec (motive := fun _ => ℕ) 0 1 (stEq s t) := rfl
  rw [e] at hs
  cases hb : stEq s t
  · rw [hb] at hs; exact absurd rfl hs
  · rw [St_eq hb]; exact h
/-- a chunked root: `tm` takes the root box `s` to its closed state `t` (computed) -/
theorem tm_to {s t : St} (hT : U (tm (kEq t)) s = 1) (h : Covered (toCl t)) : Covered (toCl s) :=
  tm_ok (kEq_ok h) s (by rw [hT]; decide)
/-- a chunk boundary's split on gap `r` at its midpoint, the children closed (`cuB`, PCBias) -/
theorem gsplit_to (r : ℕ) (hr : r < 8) {t sA sB : St}
    (eA : toCl sA = cuB 8 PR (toCl t) (colB 8 SL (toCl t) r) (rowB 8 SL (toCl t) (Nat.add BB (qG (toCl t) r)) (r + 1)))
    (eB : toCl sB = cuB 8 PR (toCl t) (colB 8 SL (toCl t) (r + 1)) (rowB 8 SL (toCl t) (Nat.sub BB (qG (toCl t) r)) r))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_splitB hSL hPR (Nat.lt_succ_self r) hr _ (eA ▸ hA) (eB ▸ hB)
/-- a chunk boundary's split on pair `k` at the raw midpoint of its bounds, the children closed (`cuB`, PCBias) -/
theorem ssplit_to (k : ℕ) (hk : k < 28) {t sA sB : St}
    (eA : toCl sA = cuB 8 PR (toCl t) (colB 8 SL (toCl t) (pI PR k)) (rowB 8 SL (toCl t) (Nat.add BB (qR (toCl t) k)) (pJ PR k)))
    (eB : toCl sB = cuB 8 PR (toCl t) (colB 8 SL (toCl t) (pJ PR k)) (rowB 8 SL (toCl t) (Nat.sub BB (qR (toCl t) k)) (pI PR k)))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_splitB hSL hPR (by have := hPR k hk; omega) (hPR k hk).2 _ (eA ▸ hA) (eB ▸ hB)
/-- (am-cert, BSPLIT chunks) a chunk boundary's split on gap `r` at the walk's cut `q` (midpoint or region boundary; any
`q` is sound), the children closed (`cuB`, PCBias) -/
theorem gsplitq_to (r q : ℕ) (hr : r < 8) {t sA sB : St}
    (eA : toCl sA = cuB 8 PR (toCl t) (colB 8 SL (toCl t) r) (rowB 8 SL (toCl t) (Nat.add BB q) (r + 1)))
    (eB : toCl sB = cuB 8 PR (toCl t) (colB 8 SL (toCl t) (r + 1)) (rowB 8 SL (toCl t) (Nat.sub BB q) r))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_splitB hSL hPR (Nat.lt_succ_self r) hr q (eA ▸ hA) (eB ▸ hB)
/-- (am-cert, BSPLIT chunks) a chunk boundary's split on pair `k` at the walk's cut `q`, the children closed (`cuB`) -/
theorem ssplitq_to (k q : ℕ) (hk : k < 28) {t sA sB : St}
    (eA : toCl sA = cuB 8 PR (toCl t) (colB 8 SL (toCl t) (pI PR k)) (rowB 8 SL (toCl t) (Nat.add BB q) (pJ PR k)))
    (eB : toCl sB = cuB 8 PR (toCl t) (colB 8 SL (toCl t) (pJ PR k)) (rowB 8 SL (toCl t) (Nat.sub BB q) (pI PR k)))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_splitB hSL hPR (by have := hPR k hk; omega) (hPR k hk).2 q (eA ▸ hA) (eB ▸ hB)
/-- (am-cert, compact boundaries) the closed child through the edge `i → j` at cut `q` (side A: `BB + q`), as the walk's
split computes it (`cuL`): no state literal is written -/
def chA (t : St) (i j q : ℕ) : St :=
  ofCl (cuB 8 PR (toCl t) (colB 8 SL (toCl t) i) (rowB 8 SL (toCl t) (Nat.add BB q) j)) t.M
/-- (am-cert, compact boundaries) the closed child through the edge `i → j` at cut `q` (side B: `BB − q`) -/
def chB (t : St) (i j q : ℕ) : St :=
  ofCl (cuB 8 PR (toCl t) (colB 8 SL (toCl t) i) (rowB 8 SL (toCl t) (Nat.sub BB q) j)) t.M
theorem toCl_cuS (t : St) (X Y : List ℕ) : toCl (ofCl (cuB 8 PR (toCl t) X Y) t.M) = cuB 8 PR (toCl t) X Y :=
  toCl_ofCl _ _ (by simp [cuB]) (by simp [cuB]) (by simp [cuB, PR]) (by simp [cuB, PR])
theorem toCl_chA (t : St) (i j q : ℕ) :
    toCl (chA t i j q) = cuB 8 PR (toCl t) (colB 8 SL (toCl t) i) (rowB 8 SL (toCl t) (Nat.add BB q) j) := toCl_cuS t _ _
theorem toCl_chB (t : St) (i j q : ℕ) :
    toCl (chB t i j q) = cuB 8 PR (toCl t) (colB 8 SL (toCl t) i) (rowB 8 SL (toCl t) (Nat.sub BB q) j) := toCl_cuS t _ _
/-- (am-cert, compact boundaries) a chunk boundary's split on gap `r` at cut `q`, children `chA`/`chB` (no state check) -/
theorem gsplitc_to (r q : ℕ) (hr : r < 8) {t : St} (hA : Covered (toCl (chA t r (r + 1) q)))
    (hB : Covered (toCl (chB t (r + 1) r q))) : Covered (toCl t) :=
  cov_splitB hSL hPR (Nat.lt_succ_self r) hr q (toCl_chA t _ _ _ ▸ hA) (toCl_chB t _ _ _ ▸ hB)
/-- (am-cert, compact boundaries) a chunk boundary's split on pair `k` at cut `q`, children `chA`/`chB` -/
theorem ssplitc_to (k q : ℕ) (hk : k < 28) {t : St} (hA : Covered (toCl (chA t (pI PR k) (pJ PR k) q)))
    (hB : Covered (toCl (chB t (pJ PR k) (pI PR k) q))) : Covered (toCl t) :=
  cov_splitB hSL hPR (by have := hPR k hk; omega) (hPR k hk).2 q (toCl_chA t _ _ _ ▸ hA) (toCl_chB t _ _ _ ▸ hB)
/-- (am-cert, chunks) a chunk's walk from any bit position on its closed incoming state, as the whole walk reaches it
(`walkC`, no root closure) -/
theorem covered_of_walkCP {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) (fuel pos e : ℕ) (s : St)
    (h : U (walkC top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walkC_ok hlb hD hpt hR bits fuel pos s (h ▸ he)
/-- a walk from any bit position -/
theorem covered_of_walkP {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) (fuel pos e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel pos s (h ▸ he)

/-- the adjacent term of each gap (its index in `TS`) -/
def ADJ : List ℕ := [0, 7, 14, 20, 25, 29, 32, 33]
theorem hADJ : ∀ r < 8, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide

/-- (root) the certificate on every point with nonnegative gaps, from the per-gap covers (`coverChk`) and the walks over
the root cells (`rootCl`: a bad segment per gap, pair bounds absent) -/
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < 8, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < 8, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 8, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : 8 * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < 8, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl 8 28 W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < 8, 0 ≤ g r) → Pg cN 8 BS TS g :=
  root_cover hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun

/-- the root: every pair bound absent (`A = 0`, `B = W ≥ Σ u`) -/
theorem covered_box (s : St) (W : ℕ) (hA : ∀ k < 28, (toCl s).A.getD k 0 = 0) (hB : ∀ k < 28, (toCl s).B.getD k 0 = W)
    (hW : sumR (toCl s).U 0 8 ≤ W) (h : Covered (toCl s)) (g : ℕ → ℝ) (hb : InBox 8 (toCl s) g) : Pg cN 8 BS TS g :=
  h g (incell_root hPR hA hB hW hb)


end AMW.Cert.PC9HP
