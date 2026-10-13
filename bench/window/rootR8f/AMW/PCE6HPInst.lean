import AMW.PCellNoRefl
import AMW.PCellCloseB
import AMW.PCDZ

/-! ###### polytope cells for Q = 6: the instance layer with the exact closure and Z
(instance layer: bridge-port, amg/genpcell4.py; the closure splits, the closure walk and its chunk lemmas: mvt-engine,
eight/am8/genpcellC.py, TZ.md §5)

Kernel functions unrolled on the curried state (12 gap and 30 pair bounds, the mask); every proof is a link to
the generic layer `AMW.PCellGen` through `toCl : St → Cl`.  The walk is mvt-engine's fixed-width DATA layout (emit8pz.py).
Engine, tables and per-term minorants: mvt-engine's MinCore on the AM
engine (pyramid oracle adapted from five-point-pyramid-2 by typh, Apache-2.0). ###### -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace AMW.Cert.PCE6HP

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

def cN : ℕ := 714135
/-- the multiplier quantum: `Y = SIG · Yq`, `Yq < 2^12` (`2^-14` per unit g) -/
def SIG : ℕ := 6250000000000000

/-- the non-adjacent pairs, in pair order -/
def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (4, 6)]
theorem hPR : PRok 6 PR := by decide
/-- the gap weights and the terms `(i, j, a, k)` of the functional `Fg` (units 1/SA) -/
def BS : List ℕ := [28898, 57272, 75526, 80958, 75526, 57272]
def TS : List Term := [(0, 1, 13630830, 0), (0, 3, 19565904, 1), (0, 4, 20317441, 2), (0, 5, 45030671, 3), (0, 6, 100000000, 4), (1, 2, 29997996, 0), (1, 3, 30621878, 5), (1, 4, 47766489, 6), (1, 5, 79682558, 7), (1, 6, 109938656, 8), (2, 3, 37356140, 0), (2, 4, 69378121, 9), (2, 5, 65335210, 10), (2, 6, 79682558, 11), (3, 4, 38030065, 0), (3, 5, 69378121, 12), (3, 6, 47766489, 13), (4, 5, 37356140, 0), (4, 6, 30621878, 14), (5, 6, 29997996, 0)]
theorem hTS : TSok 6 PR TS := by decide

/-- the slot of the pair `(a, b)`, `a < b`, at `a · 7 + b`: gap `a` when `b = a + 1`, else `6` + the pair's rank -/
def SL : List ℕ := [0, 0, 6, 7, 8, 9, 10, 0, 0, 1, 11, 12, 13, 14, 0, 0, 0, 2, 15, 16, 17, 0, 0, 0, 0, 3, 18, 19, 0, 0, 0, 0, 0, 4, 20, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0]
theorem hSL : SLok 6 PR SL := by decide

/-- the convex-region boundaries, sorted (the boundary split cuts at the one nearest the midpoint, ≥ BMARG = 64 inside) -/
def BND : List ℕ := [16384, 40384, 56768, 73664, 89920, 106176, 122304, 138560, 155136, 171456, 187712, 203840, 220224, 236480, 253120, 269440, 285760, 302080, 318720, 335168, 351872, 368384, 384896, 401280, 417728, 434048, 450496, 466816, 483264, 499584, 516032, 524288]

def SA : ℕ := 100000000

/-- the weighted functional on the gaps, in real form (pair weights `a_ij` and pressures `b_r` over `SA`) -/
def G (g0 g1 g2 g3 g4 g5 : ℝ) : ℝ :=
  (28898 / (SA:ℝ)) * g0 + (57272 / (SA:ℝ)) * g1 + (75526 / (SA:ℝ)) * g2 + (80958 / (SA:ℝ)) * g3 + (75526 / (SA:ℝ)) * g4 + (57272 / (SA:ℝ)) * g5
    + (13630830 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (19565904 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (20317441 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (45030671 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (29997996 / (SA:ℝ)) * wfun (g1) + (30621878 / (SA:ℝ)) * wfun (g1 + g2) + (47766489 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (79682558 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (109938656 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (37356140 / (SA:ℝ)) * wfun (g2) + (69378121 / (SA:ℝ)) * wfun (g2 + g3) + (65335210 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (79682558 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (38030065 / (SA:ℝ)) * wfun (g3) + (69378121 / (SA:ℝ)) * wfun (g3 + g4) + (47766489 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (37356140 / (SA:ℝ)) * wfun (g4) + (30621878 / (SA:ℝ)) * wfun (g4 + g5) + (29997996 / (SA:ℝ)) * wfun (g5)

/-- the integer functional `Fg` on a tuple of gaps is `SA · G` -/
theorem Fg_G (x0 x1 x2 x3 x4 x5 : ℝ) : Fg 6 BS TS (fun r => [x0, x1, x2, x3, x4, x5].getD r 0) = (SA : ℝ) * G x0 x1 x2 x3 x4 x5 := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring

/-- the canonical tables (HUFF.md §3): per table the count of each code length from 0, and the symbols in table order
(16-bit fields); a term's symbol is `κ · 2^14 + j1 · 2^7 + j2`, the axis `0 … 5` a gap, `6 …` a pair (pair order),
the multiplier's `c` the pair's rank -/
-- (fixed-width fields: no tables)

abbrev Covered : Cl → Prop := CovBy 6 PR (PgL cN 6 BS TS)

/-- the kernel state -/
structure St where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A13 B13 A14 B14 A15 B15 A16 B16 A24 B24 A25 B25 A26 B26 A35 B35 A36 B36 A46 B46 M : ℕ)

def toCl (s : St) : Cl :=
  ⟨[s.l0, s.l1, s.l2, s.l3, s.l4, s.l5], [s.u0, s.u1, s.u2, s.u3, s.u4, s.u5],
   [s.A02, s.A03, s.A04, s.A05, s.A06, s.A13, s.A14, s.A15, s.A16, s.A24, s.A25, s.A26, s.A35, s.A36, s.A46], [s.B02, s.B03, s.B04, s.B05, s.B06, s.B13, s.B14, s.B15, s.B16, s.B24, s.B25, s.B26, s.B35, s.B36, s.B46]⟩
def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨c.L.getD 0 0, c.U.getD 0 0, c.L.getD 1 0, c.U.getD 1 0, c.L.getD 2 0, c.U.getD 2 0, c.L.getD 3 0, c.U.getD 3 0, c.L.getD 4 0, c.U.getD 4 0, c.L.getD 5 0, c.U.getD 5 0, c.A.getD 0 0, c.B.getD 0 0, c.A.getD 1 0, c.B.getD 1 0, c.A.getD 2 0, c.B.getD 2 0, c.A.getD 3 0, c.B.getD 3 0, c.A.getD 4 0, c.B.getD 4 0, c.A.getD 5 0, c.B.getD 5 0, c.A.getD 6 0, c.B.getD 6 0, c.A.getD 7 0, c.B.getD 7 0, c.A.getD 8 0, c.B.getD 8 0, c.A.getD 9 0, c.B.getD 9 0, c.A.getD 10 0, c.B.getD 10 0, c.A.getD 11 0, c.B.getD 11 0, c.A.getD 12 0, c.B.getD 12 0, c.A.getD 13 0, c.B.getD 13 0, c.A.getD 14 0, c.B.getD 14 0, m⟩

theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = 6) (h2 : c.U.length = 6) (h3 : c.A.length = 15) (h4 : c.B.length = 15) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]

abbrev ST : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
/-- a continuation applied to a state -/
def U (k : ST) (s : St) : ℕ := k s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A35 s.B35 s.A36 s.B36 s.A46 s.B46 s.M
def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
def zK : ST := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h

theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = 6) (h2 : c.U.length = 6) (h3 : c.A.length = 15)
    (h4 : c.B.length = 15) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h

/-- a split node's two children (`cA` from `pos`, the bit after the axis code, then `cB`) cover the cell when the split lemma does -/
theorem sp_ok {ih : WF} (hih : WalkOK ih) {s : St} {cA cB : Cl} {pos mA mB : ℕ}
    (hc : Covered cA → Covered cB → Covered (toCl s))
    (h : Bool.rec (motive := fun _ => ℕ) (U (ih (U (ih pos) (ofCl cA mA))) (ofCl cB mB)) 0
      (Nat.beq (U (ih pos) (ofCl cA mA)) 0) ≠ 0)
    (hA : cA.L.length = 6 ∧ cA.U.length = 6 ∧ cA.A.length = 15 ∧ cA.B.length = 15)
    (hB : cB.L.length = 6 ∧ cB.U.length = 6 ∧ cB.A.length = 15 ∧ cB.B.length = 15) : Covered (toCl s) := by
  cases hp : Nat.beq (U (ih pos) (ofCl cA mA)) 0
  · rw [hp] at h
    exact hc (ofCl_ok (hih _) hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 fun h0 => by rw [h0] at hp; exact absurd hp (by decide))
      (ofCl_ok (hih _) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 h)
  · rw [hp] at h; exact absurd rfl h


-- (2) split nodes: gap r at the midpoint of [l_r, u_r]; pair t at the midpoint of its (persisted) bounds

-- (2) the split, generic: axis `0 … 5` a gap, `6 … 20` a pair; the cut by mode (`qB`/`qBr`), both children closed (`cupd`)
def splitC (ih : WF) (md pos ax : ℕ) (c : Cl) (M : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) 0
      (let p := U (ih pos) (ofCl (cupd 6 PR SL ⟨c.L, c.U, c.A, c.B.set (Nat.sub ax 6) (qBr BND 64 c (Nat.sub ax 6) md)⟩
          (pI PR (Nat.sub ax 6)) (pJ PR (Nat.sub ax 6))) M)
       Bool.rec (motive := fun _ => ℕ) (U (ih p) (ofCl (cupd 6 PR SL ⟨c.L, c.U, c.A.set (Nat.sub ax 6) (qBr BND 64 c (Nat.sub ax 6) md), c.B⟩
          (pJ PR (Nat.sub ax 6)) (pI PR (Nat.sub ax 6))) M)) 0 (Nat.beq p 0))
      (Nat.blt ax 21))
    (let p := U (ih pos) (ofCl (cupd 6 PR SL ⟨c.L, c.U.set ax (qB BND 64 c ax md), c.A, c.B⟩ ax (ax + 1)) M)
     Bool.rec (motive := fun _ => ℕ) (U (ih p) (ofCl (cupd 6 PR SL ⟨c.L.set ax (qB BND 64 c ax md), c.U, c.A, c.B⟩ (ax + 1) ax) M)) 0 (Nat.beq p 0))
    (Nat.blt ax 6)
/-- a split node -/
def splitAx (ih : WF) (md pos ax : ℕ) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A13 B13 A14 B14 A15 B15 A16 B16 A24 B24 A25 B25 A26 B26 A35 B35 A36 B36 A46 B46 M => splitC ih md pos ax ⟨[l0, l1, l2, l3, l4, l5], [u0, u1, u2, u3, u4, u5], [A02, A03, A04, A05, A06, A13, A14, A15, A16, A24, A25, A26, A35, A36, A46], [B02, B03, B04, B05, B06, B13, B14, B15, B16, B24, B25, B26, B35, B36, B46]⟩ M

theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) := by
  intro s h
  have h' : splitC ih md pos ax (toCl s) s.M ≠ 0 := h
  unfold splitC at h'
  cases hq : Nat.blt ax 6
  · rw [hq] at h'
    cases hr : Nat.blt ax 21
    · rw [hr] at h'; exact absurd rfl h'
    · rw [hr] at h'
      have hk : ax - 6 < 15 := by
        have h1 := Nat.blt_eq.mp hr; have h2 : ¬ ax < 6 := fun e => absurd (Nat.blt_eq.mpr e) (by rw [hq]; decide)
        omega
      exact sp_ok hih (cov_ssplitQ hSL hPR (ax - 6) (qBr BND 64 (toCl s) (ax - 6) md) rfl rfl hk) h'
        (cupd_len _ _ _ _ _ _) (cupd_len _ _ _ _ _ _)
  · rw [hq] at h'
    exact sp_ok hih (cov_gsplitQ hSL hPR ax (qB BND 64 (toCl s) ax md) rfl rfl (Nat.blt_eq.mp hq)) h'
      (cupd_len _ _ _ _ _ _) (cupd_len _ _ _ _ _ _)

-- (5) the root: the box sums written into the pair bounds (`matC`), once, which closes the root box (TZ.md §5)

def tm (k : ST) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A13 B13 A14 B14 A15 B15 A16 B16 A24 B24 A25 B25 A26 B26 A35 B35 A36 B36 A46 B46 M => U k (ofCl (matC PR ⟨[l0, l1, l2, l3, l4, l5], [u0, u1, u2, u3, u4, u5], [A02, A03, A04, A05, A06, A13, A14, A15, A16, A24, A25, A26, A35, A36, A46], [B02, B03, B04, B05, B06, B13, B14, B15, B16, B24, B25, B26, B35, B36, B46]⟩) M)

theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2

-- (3) multipliers (HUFF.md §5.2): entries `[1][c code][side][Yq: qb bits]`, closed by `[0]`
structure YA where
  (o P0 P1 P2 P3 P4 P5 S0 S1 S2 S3 S4 S5 Cp Cm : ℕ)

def MulOK (s : St) (y : YA) : Prop :=
  MulOKg 6 PR (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5] y.Cp y.Cm

def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) ⟨(Nat.add o 1), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.Cp, y.Cm⟩
    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) 31) fun c => forceT (Nat.add o 6) fun o1 =>
     Bool.rec (motive := fun _ => YA) ⟨(Nat.add o1 (Nat.add qb 1)), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.Cp, y.Cm⟩
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih ⟨(Nat.add o1 (Nat.add qb 1)), (Nat.add y.P0 (Nat.mul Ylo (ind (inr 0 i j)))), (Nat.add y.P1 (Nat.mul Ylo (ind (inr 1 i j)))), (Nat.add y.P2 (Nat.mul Ylo (ind (inr 2 i j)))), (Nat.add y.P3 (Nat.mul Ylo (ind (inr 3 i j)))), (Nat.add y.P4 (Nat.mul Ylo (ind (inr 4 i j)))), (Nat.add y.P5 (Nat.mul Ylo (ind (inr 5 i j)))), (Nat.add y.S0 (Nat.mul Yhi (ind (inr 0 i j)))), (Nat.add y.S1 (Nat.mul Yhi (ind (inr 1 i j)))), (Nat.add y.S2 (Nat.mul Yhi (ind (inr 2 i j)))), (Nat.add y.S3 (Nat.mul Yhi (ind (inr 3 i j)))), (Nat.add y.S4 (Nat.mul Yhi (ind (inr 4 i j)))), (Nat.add y.S5 (Nat.mul Yhi (ind (inr 5 i j)))), (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))), (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0))))⟩)
      (Nat.blt c 15))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)

def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel

theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := fun _ _ => by simp

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
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k45 m45 p45 r45 k46 m46 p46 r46 k56 m56 p56 r56 : ℕ) (P0 P1 P2 P3 P4 P5 S0 S1 S2 S3 S4 S5 Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mcK f false s.l0 k01 m01 p01 r01))) (Nat.mul 19565904 (mcK f false (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 20317441 (mcK f false (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 45030671 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 100000000 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 29997996 (mcK f false s.l1 k12 m12 p12 r12))) (Nat.mul 30621878 (mcK f false (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 47766489 (mcK f false (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 79682558 (mcK f false (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 109938656 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 37356140 (mcK f false s.l2 k23 m23 p23 r23))) (Nat.mul 69378121 (mcK f false (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 65335210 (mcK f false (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 79682558 (mcK f false (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 38030065 (mcK f false s.l3 k34 m34 p34 r34))) (Nat.mul 69378121 (mcK f false (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 47766489 (mcK f false (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 37356140 (mcK f false s.l4 k45 m45 p45 r45))) (Nat.mul 30621878 (mcK f false (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 29997996 (mcK f false s.l5 k56 m56 p56 r56))) Cp) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub s.u0 s.l0) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mwT k01 m01))) (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06)))) P0) (Nat.add (Nat.add (Nat.mul 1024000000000 28898) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mslK f k01 m01 p01 r01))) (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06)))) S0)))) (Nat.mul (Nat.sub s.u1 s.l1) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 29997996 (mwT k12 m12))) (Nat.mul 30621878 (mwT k13 m13))) (Nat.mul 47766489 (mwT k14 m14))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16)))) P1) (Nat.add (Nat.add (Nat.mul 1024000000000 57272) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 29997996 (mslK f k12 m12 p12 r12))) (Nat.mul 30621878 (mslK f k13 m13 p13 r13))) (Nat.mul 47766489 (mslK f k14 m14 p14 r14))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16)))) S1)))) (Nat.mul (Nat.sub s.u2 s.l2) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 30621878 (mwT k13 m13))) (Nat.mul 47766489 (mwT k14 m14))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 37356140 (mwT k23 m23))) (Nat.mul 69378121 (mwT k24 m24))) (Nat.mul 65335210 (mwT k25 m25))) (Nat.mul 79682558 (mwT k26 m26)))) P2) (Nat.add (Nat.add (Nat.mul 1024000000000 75526) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 30621878 (mslK f k13 m13 p13 r13))) (Nat.mul 47766489 (mslK f k14 m14 p14 r14))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 37356140 (mslK f k23 m23 p23 r23))) (Nat.mul 69378121 (mslK f k24 m24 p24 r24))) (Nat.mul 65335210 (mslK f k25 m25 p25 r25))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26)))) S2)))) (Nat.mul (Nat.sub s.u3 s.l3) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 47766489 (mwT k14 m14))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 69378121 (mwT k24 m24))) (Nat.mul 65335210 (mwT k25 m25))) (Nat.mul 79682558 (mwT k26 m26))) (Nat.mul 38030065 (mwT k34 m34))) (Nat.mul 69378121 (mwT k35 m35))) (Nat.mul 47766489 (mwT k36 m36)))) P3) (Nat.add (Nat.add (Nat.mul 1024000000000 80958) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 47766489 (mslK f k14 m14 p14 r14))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 69378121 (mslK f k24 m24 p24 r24))) (Nat.mul 65335210 (mslK f k25 m25 p25 r25))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26))) (Nat.mul 38030065 (mslK f k34 m34 p34 r34))) (Nat.mul 69378121 (mslK f k35 m35 p35 r35))) (Nat.mul 47766489 (mslK f k36 m36 p36 r36)))) S3)))) (Nat.mul (Nat.sub s.u4 s.l4) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 65335210 (mwT k25 m25))) (Nat.mul 79682558 (mwT k26 m26))) (Nat.mul 69378121 (mwT k35 m35))) (Nat.mul 47766489 (mwT k36 m36))) (Nat.mul 37356140 (mwT k45 m45))) (Nat.mul 30621878 (mwT k46 m46)))) P4) (Nat.add (Nat.add (Nat.mul 1024000000000 75526) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 65335210 (mslK f k25 m25 p25 r25))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26))) (Nat.mul 69378121 (mslK f k35 m35 p35 r35))) (Nat.mul 47766489 (mslK f k36 m36 p36 r36))) (Nat.mul 37356140 (mslK f k45 m45 p45 r45))) (Nat.mul 30621878 (mslK f k46 m46 p46 r46)))) S4)))) (Nat.mul (Nat.sub s.u5 s.l5) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 79682558 (mwT k26 m26))) (Nat.mul 47766489 (mwT k36 m36))) (Nat.mul 30621878 (mwT k46 m46))) (Nat.mul 29997996 (mwT k56 m56)))) P5) (Nat.add (Nat.add (Nat.mul 1024000000000 57272) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26))) (Nat.mul 47766489 (mslK f k36 m36 p36 r36))) (Nat.mul 30621878 (mslK f k46 m46 p46 r46))) (Nat.mul 29997996 (mslK f k56 m56 p56 r56)))) S5))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 28898 s.l0)) (Nat.mul 57272 s.l1)) (Nat.mul 75526 s.l2)) (Nat.mul 80958 s.l3)) (Nat.mul 75526 s.l4)) (Nat.mul 57272 s.l5))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mvKF top bk f s.l0 (uc s.l0 s.u0) k01 m01 p01 r01))) (Nat.mul 19565904 (mvKF top bk f (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (uc (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2))) k03 m03 p03 r03))) (Nat.mul 20317441 (mvKF top bk f (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (uc (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3))) k04 m04 p04 r04))) (Nat.mul 45030671 (mvKF top bk f (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (uc (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4))) k05 m05 p05 r05))) (Nat.mul 100000000 (mvKF top bk f (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5))) k06 m06 p06 r06))) (Nat.mul 29997996 (mvKF top bk f s.l1 (uc s.l1 s.u1) k12 m12 p12 r12))) (Nat.mul 30621878 (mvKF top bk f (nmax s.A13 (Nat.add s.l1 s.l2)) (uc (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2))) k13 m13 p13 r13))) (Nat.mul 47766489 (mvKF top bk f (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (uc (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3))) k14 m14 p14 r14))) (Nat.mul 79682558 (mvKF top bk f (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (uc (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4))) k15 m15 p15 r15))) (Nat.mul 109938656 (mvKF top bk f (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5))) k16 m16 p16 r16))) (Nat.mul 37356140 (mvKF top bk f s.l2 (uc s.l2 s.u2) k23 m23 p23 r23))) (Nat.mul 69378121 (mvKF top bk f (nmax s.A24 (Nat.add s.l2 s.l3)) (uc (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3))) k24 m24 p24 r24))) (Nat.mul 65335210 (mvKF top bk f (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (uc (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4))) k25 m25 p25 r25))) (Nat.mul 79682558 (mvKF top bk f (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (uc (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5))) k26 m26 p26 r26))) (Nat.mul 38030065 (mvKF top bk f s.l3 (uc s.l3 s.u3) k34 m34 p34 r34))) (Nat.mul 69378121 (mvKF top bk f (nmax s.A35 (Nat.add s.l3 s.l4)) (uc (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4))) k35 m35 p35 r35))) (Nat.mul 47766489 (mvKF top bk f (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (uc (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5))) k36 m36 p36 r36))) (Nat.mul 37356140 (mvKF top bk f s.l4 (uc s.l4 s.u4) k45 m45 p45 r45))) (Nat.mul 30621878 (mvKF top bk f (nmax s.A46 (Nat.add s.l4 s.l5)) (uc (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5))) k46 m46 p46 r46))) (Nat.mul 29997996 (mvKF top bk f s.l5 (uc s.l5 s.u5) k56 m56 p56 r56))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mcK f true s.l0 k01 m01 p01 r01))) (Nat.mul 19565904 (mcK f true (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 20317441 (mcK f true (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 45030671 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 100000000 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 29997996 (mcK f true s.l1 k12 m12 p12 r12))) (Nat.mul 30621878 (mcK f true (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 47766489 (mcK f true (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 79682558 (mcK f true (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 109938656 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 37356140 (mcK f true s.l2 k23 m23 p23 r23))) (Nat.mul 69378121 (mcK f true (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 65335210 (mcK f true (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 79682558 (mcK f true (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 38030065 (mcK f true s.l3 k34 m34 p34 r34))) (Nat.mul 69378121 (mcK f true (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 47766489 (mcK f true (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 37356140 (mcK f true s.l4 k45 m45 p45 r45))) (Nat.mul 30621878 (mcK f true (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 29997996 (mcK f true s.l5 k56 m56 p56 r56))) Cm)))) (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l5 s.u5 k56 m56 p56 r56) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5)) k46 m46 p46 r46) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l4 s.u4 k45 m45 p45 r45) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) k36 m36 p36 r36) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4)) k35 m35 p35 r35) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l3 s.u3 k34 m34 p34 r34) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) k26 m26 p26 r26) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) k25 m25 p25 r25) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3)) k24 m24 p24 r24) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l2 s.u2 k23 m23 p23 r23) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) k16 m16 p16 r16) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) k15 m15 p15 r15) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) k14 m14 p14 r14) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2)) k13 m13 p13 r13) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l1 s.u1 k12 m12 p12 r12) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) k06 m06 p06 r06) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) k05 m05 p05 r05) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) k04 m04 p04 r04) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) k03 m03 p03 r03) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l0 s.u0 k01 m01 p01 r01) (true))))))))))))))))))))) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l5 s.u5) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l4 s.u4) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l3 s.u3) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l2 s.u2) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l1 s.u1) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l0 s.u0) (true))))))))

theorem mcheckP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k45 m45 p45 r45 k46 m46 p46 r46 k56 m56 p56 r56 : ℕ) (P0 P1 P2 P3 P4 P5 S0 S1 S2 S3 S4 S5 Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k45 m45 p45 r45 k46 m46 p46 r46 k56 m56 p56 r56 P0 P1 P2 P3 P4 P5 S0 S1 S2 S3 S4 S5 Cp Cm = true) :
    mcheckGX (mokTZC R top bk tD bD f 8 3) top bk f 6 BS TS cN (toCl s) [(k01, m01, p01, r01), (k03, m03, p03, r03), (k04, m04, p04, r04), (k05, m05, p05, r05), (k06, m06, p06, r06), (k12, m12, p12, r12), (k13, m13, p13, r13), (k14, m14, p14, r14), (k15, m15, p15, r15), (k16, m16, p16, r16), (k23, m23, p23, r23), (k24, m24, p24, r24), (k25, m25, p25, r25), (k26, m26, p26, r26), (k34, m34, p34, r34), (k35, m35, p35, r35), (k36, m36, p36, r36), (k45, m45, p45, r45), (k46, m46, p46, r46), (k56, m56, p56, r56)]
      [P0, P1, P2, P3, P4, P5] [S0, S1, S2, S3, S4, S5] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq, mvKF_eq] at h; exact h

/-- the polytope minorant leaf (HUFF.md §5): the payload length when the check passes, else `0` -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  forceR (nmax s.A02 (Nat.add s.l0 s.l1)) fun L02 => forceR (nmin s.B02 (Nat.add s.u0 s.u1)) fun U02 =>
  forceR (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) fun L03 => forceR (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) fun U03 =>
  forceR (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) fun L04 => forceR (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) fun U04 =>
  forceR (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) fun L05 => forceR (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) fun U05 =>
  forceR (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) fun L06 => forceR (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) fun U06 =>
  forceR (nmax s.A13 (Nat.add s.l1 s.l2)) fun L13 => forceR (nmin s.B13 (Nat.add s.u1 s.u2)) fun U13 =>
  forceR (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) fun L14 => forceR (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) fun U14 =>
  forceR (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) fun L15 => forceR (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) fun U15 =>
  forceR (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) fun L16 => forceR (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) fun U16 =>
  forceR (nmax s.A24 (Nat.add s.l2 s.l3)) fun L24 => forceR (nmin s.B24 (Nat.add s.u2 s.u3)) fun U24 =>
  forceR (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) fun L25 => forceR (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) fun U25 =>
  forceR (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) fun L26 => forceR (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) fun U26 =>
  forceR (nmax s.A35 (Nat.add s.l3 s.l4)) fun L35 => forceR (nmin s.B35 (Nat.add s.u3 s.u4)) fun U35 =>
  forceR (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) fun L36 => forceR (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) fun U36 =>
  forceR (nmax s.A46 (Nat.add s.l4 s.l5)) fun L46 => forceR (nmin s.B46 (Nat.add s.u4 s.u5)) fun U46 =>
  forceR 0 fun o0 =>
  dec4F 8 w o0 s.l0 s.u0 fun k01 m01 p01 r01 o1 =>
  dec4F 8 w o1 L03 U03 fun k03 m03 p03 r03 o2 =>
  dec4F 8 w o2 L04 U04 fun k04 m04 p04 r04 o3 =>
  dec4F 8 w o3 L05 U05 fun k05 m05 p05 r05 o4 =>
  dec4F 8 w o4 L06 U06 fun k06 m06 p06 r06 o5 =>
  dec4F 8 w o5 s.l1 s.u1 fun k12 m12 p12 r12 o6 =>
  dec4F 8 w o6 L13 U13 fun k13 m13 p13 r13 o7 =>
  dec4F 8 w o7 L14 U14 fun k14 m14 p14 r14 o8 =>
  dec4F 8 w o8 L15 U15 fun k15 m15 p15 r15 o9 =>
  dec4F 8 w o9 L16 U16 fun k16 m16 p16 r16 o10 =>
  dec4F 8 w o10 s.l2 s.u2 fun k23 m23 p23 r23 o11 =>
  dec4F 8 w o11 L24 U24 fun k24 m24 p24 r24 o12 =>
  dec4F 8 w o12 L25 U25 fun k25 m25 p25 r25 o13 =>
  dec4F 8 w o13 L26 U26 fun k26 m26 p26 r26 o14 =>
  dec4F 8 w o14 s.l3 s.u3 fun k34 m34 p34 r34 o15 =>
  dec4F 8 w o15 L35 U35 fun k35 m35 p35 r35 o16 =>
  dec4F 8 w o16 L36 U36 fun k36 m36 p36 r36 o17 =>
  dec4F 8 w o17 s.l4 s.u4 fun k45 m45 p45 r45 o18 =>
  dec4F 8 w o18 L46 U46 fun k46 m46 p46 r46 o19 =>
  dec4F 8 w o19 s.l5 s.u5 fun k56 m56 p56 r56 o20 =>
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k45 m45 p45 r45 k46 m46 p46 r46 k56 m56 p56 r56 y.P0 y.P1 y.P2 y.P3 y.P4 y.P5 y.S0 y.S1 y.S2 y.S3 y.S4 y.S5 y.Cp y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨o20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  unfold mleafP at h
  simp only [dec4F, forceR_eq] at h
  exact mcheckGX_soundL (f := pb) (mtermTZC hlb hD hpt hR (by decide : 0 < 8)) hPR hTS (ydec_ok s 12 w 42 _ (MulOK_zero s _)) (mcheckP_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h))

/-- (kind 8) the Farkas leaf (HUFF.md §6): the multiplier list only (`Yq` in 12 bits), accepted when the multiplier form
is negative on the whole box -/
def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5] 6)) y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

/-- a leaf (bit 0 clear): the reflected half-space (`u5 < l0`, no further bits), else bit 1 the kind (minorant leaf, or
Farkas leaf) with its payload from bit 2 -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A13 B13 A14 B14 A15 B15 A16 B16 A24 B24 A25 B25 A26 B26 A35 B35 A36 B36 A46 B46 M =>
    forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A13, B13, A14, B14, A15, B15, A16, B16, A24, B24, A25, B25, A26, B26, A35, B35, A36, B36, A46, B46, M⟩)
        (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A13, B13, A14, B14, A15, B15, A16, B16, A24, B24, A25, B25, A26, B26, A35, B35, A36, B36, A46, B46, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)

theorem fleaf_ok (w : ℕ) (s : St) (h : fleaf w s ≠ 0) : Covered (toCl s) :=
  farkas_cov (ydec_ok s 12 w 42 _ (MulOK_zero s 0)) (brec_ne h)

theorem leafStep_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (pos w : ℕ) :
    CovK (leafStep top bk tD bD pb R pos w) := by
  intro s h
  have h' : forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)
      (fleaf (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) (fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) ≠ 0 := h
  rw [forceR_eq] at h'
  cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
  · rw [hk] at h'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h'; exact h' rfl
  · rw [hk] at h'; exact fleaf_ok _ s fun h0 => by rw [h0] at h'; exact h' rfl

/-- a node: bit `pos` selects split (`[1]`, then the axis codeword; the children from the bit after it) or leaf (`[0]`) -/
def node (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos (Nat.shiftRight bits pos))
    (splitAx ih (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 6) 1) (Nat.add pos 7) (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 31))
    (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1)

/-- the walk on closed cells: no node tightening, the splits close their children (TZ.md §5) -/
def walkC (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => node top bk tD bD pb R bits ih pos) fuel

/-- the walk from a root box: the box sums close it (`tm`, once), then `walkC` -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits fuel : ℕ) : WF :=
  fun pos => tm (walkC top bk tD bD pb R bits fuel pos)

theorem forceT_cov {x : ℕ} {k : ℕ → ST} (h : CovK (k x)) : CovK (forceT x k) := by rw [forceT_eq]; exact h

theorem walkC_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walkC top bk tD bD pb R bits fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => show CovK (node top bk tD bD pb R bits (walkC top bk tD bD pb R bits n) pos) from
      brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
      (splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _ _)

theorem walk_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) :=
  fun fuel pos => tm_ok (walkC_ok hlb hD hpt hR bits fuel pos)

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits fuel e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)


/-- the adjacent term of each gap (its index in `TS`) -/
def ADJ : List ℕ := [0, 5, 10, 14, 17, 19]
theorem hADJ : ∀ r < 6, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide

/-- (root) the certificate on every point with nonnegative gaps, from the per-gap covers (`coverChk`) and the walks over
the root cells (`rootCl`: a bad segment per gap, pair bounds absent) -/
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < 6, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < 6, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 6, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : 6 * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < 6, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl 6 15 W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < 6, 0 ≤ g r) → PgL cN 6 BS TS g :=
  root_coverL hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun

/-- the root: every pair bound absent (`A = 0`, `B = W ≥ Σ u`) -/
theorem covered_box (s : St) (W : ℕ) (hA : ∀ k < 15, (toCl s).A.getD k 0 = 0) (hB : ∀ k < 15, (toCl s).B.getD k 0 = W)
    (hW : sumR (toCl s).U 0 6 ≤ W) (h : Covered (toCl s)) (g : ℕ → ℝ) (hb : InBox 6 (toCl s) g) : PgL cN 6 BS TS g :=
  h g (incell_root hPR hA hB hW hb)


end AMW.Cert.PCE6HP
