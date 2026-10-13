import AMW.PCellNoRefl
import AMW.PCellCloseB
import AMW.PCDZ

/-! ###### polytope cells for Q = 4: the instance layer with the exact closure and Z
(instance layer: bridge-port, amg/genpcell4.py; the closure splits, the closure walk and its chunk lemmas: mvt-engine,
eight/am8/genpcellC.py, TZ.md §5)

Kernel functions unrolled on the curried state (8 gap and 12 pair bounds, the mask); every proof is a link to
the generic layer `AMW.PCellGen` through `toCl : St → Cl`.  The walk is mvt-engine's fixed-width DATA layout (emit8pz.py).
Engine, tables and per-term minorants: mvt-engine's MinCore on the AM
engine (pyramid oracle adapted from five-point-pyramid-2 by typh, Apache-2.0). ###### -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace AMW.Cert.PCE4G

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

def cN : ℕ := 371951
/-- the multiplier quantum: `Y = SIG · Yq`, `Yq < 2^12` (`2^-14` per unit g) -/
def SIG : ℕ := 6250000000000000

/-- the non-adjacent pairs, in pair order -/
def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 4)]
theorem hPR : PRok 4 PR := by decide
/-- the gap weights and the terms `(i, j, a, k)` of the functional `Fg` (units 1/SA) -/
def BS : List ℕ := [28898, 57272, 75526, 80958]
def TS : List Term := [(0, 1, 13630830, 0), (0, 3, 19565904, 1), (0, 4, 20317441, 2), (1, 2, 29997996, 0), (1, 3, 30621878, 3), (1, 4, 47766489, 4), (2, 3, 37356140, 0), (2, 4, 69378121, 5), (3, 4, 38030065, 0)]
theorem hTS : TSok 4 PR TS := by decide

/-- the slot of the pair `(a, b)`, `a < b`, at `a · 5 + b`: gap `a` when `b = a + 1`, else `4` + the pair's rank -/
def SL : List ℕ := [0, 0, 4, 5, 6, 0, 0, 1, 7, 8, 0, 0, 0, 2, 9, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0]
theorem hSL : SLok 4 PR SL := by decide

/-- the convex-region boundaries, sorted (the boundary split cuts at the one nearest the midpoint, ≥ BMARG = 64 inside) -/
def BND : List ℕ := [16384, 40384, 56768, 73664, 89920, 106176, 122304, 138560, 155136, 171456, 187712, 203840, 220224, 236480, 253120, 269440, 285760, 302080, 318720, 335168, 351872, 368384, 384896, 401280, 417728, 434048, 450496, 466816, 483264, 499584, 516032, 524288]

def SA : ℕ := 100000000

/-- the weighted functional on the gaps, in real form (pair weights `a_ij` and pressures `b_r` over `SA`) -/
def G (g0 g1 g2 g3 : ℝ) : ℝ :=
  (28898 / (SA:ℝ)) * g0 + (57272 / (SA:ℝ)) * g1 + (75526 / (SA:ℝ)) * g2 + (80958 / (SA:ℝ)) * g3
    + (13630830 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (19565904 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (20317441 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (29997996 / (SA:ℝ)) * wfun (g1) + (30621878 / (SA:ℝ)) * wfun (g1 + g2) + (47766489 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (37356140 / (SA:ℝ)) * wfun (g2) + (69378121 / (SA:ℝ)) * wfun (g2 + g3) + (38030065 / (SA:ℝ)) * wfun (g3)

/-- the integer functional `Fg` on a tuple of gaps is `SA · G` -/
theorem Fg_G (x0 x1 x2 x3 : ℝ) : Fg 4 BS TS (fun r => [x0, x1, x2, x3].getD r 0) = (SA : ℝ) * G x0 x1 x2 x3 := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring

/-- the canonical tables (HUFF.md §3): per table the count of each code length from 0, and the symbols in table order
(16-bit fields); a term's symbol is `κ · 2^14 + j1 · 2^7 + j2`, the axis `0 … 3` a gap, `4 …` a pair (pair order),
the multiplier's `c` the pair's rank -/
-- (fixed-width fields: no tables)

abbrev Covered : Cl → Prop := CovBy 4 PR (PgL cN 4 BS TS)

/-- the kernel state -/
structure St where
  (l0 u0 l1 u1 l2 u2 l3 u3 A02 B02 A03 B03 A04 B04 A13 B13 A14 B14 A24 B24 M : ℕ)

def toCl (s : St) : Cl :=
  ⟨[s.l0, s.l1, s.l2, s.l3], [s.u0, s.u1, s.u2, s.u3],
   [s.A02, s.A03, s.A04, s.A13, s.A14, s.A24], [s.B02, s.B03, s.B04, s.B13, s.B14, s.B24]⟩
def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨c.L.getD 0 0, c.U.getD 0 0, c.L.getD 1 0, c.U.getD 1 0, c.L.getD 2 0, c.U.getD 2 0, c.L.getD 3 0, c.U.getD 3 0, c.A.getD 0 0, c.B.getD 0 0, c.A.getD 1 0, c.B.getD 1 0, c.A.getD 2 0, c.B.getD 2 0, c.A.getD 3 0, c.B.getD 3 0, c.A.getD 4 0, c.B.getD 4 0, c.A.getD 5 0, c.B.getD 5 0, m⟩

theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = 4) (h2 : c.U.length = 4) (h3 : c.A.length = 6) (h4 : c.B.length = 6) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]

abbrev ST : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
/-- a continuation applied to a state -/
def U (k : ST) (s : St) : ℕ := k s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A13 s.B13 s.A14 s.B14 s.A24 s.B24 s.M
def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
def zK : ST := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h

theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = 4) (h2 : c.U.length = 4) (h3 : c.A.length = 6)
    (h4 : c.B.length = 6) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h

/-- a split node's two children (`cA` from `pos`, the bit after the axis code, then `cB`) cover the cell when the split lemma does -/
theorem sp_ok {ih : WF} (hih : WalkOK ih) {s : St} {cA cB : Cl} {pos mA mB : ℕ}
    (hc : Covered cA → Covered cB → Covered (toCl s))
    (h : Bool.rec (motive := fun _ => ℕ) (U (ih (U (ih pos) (ofCl cA mA))) (ofCl cB mB)) 0
      (Nat.beq (U (ih pos) (ofCl cA mA)) 0) ≠ 0)
    (hA : cA.L.length = 4 ∧ cA.U.length = 4 ∧ cA.A.length = 6 ∧ cA.B.length = 6)
    (hB : cB.L.length = 4 ∧ cB.U.length = 4 ∧ cB.A.length = 6 ∧ cB.B.length = 6) : Covered (toCl s) := by
  cases hp : Nat.beq (U (ih pos) (ofCl cA mA)) 0
  · rw [hp] at h
    exact hc (ofCl_ok (hih _) hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 fun h0 => by rw [h0] at hp; exact absurd hp (by decide))
      (ofCl_ok (hih _) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 h)
  · rw [hp] at h; exact absurd rfl h


-- (2) split nodes: gap r at the midpoint of [l_r, u_r]; pair t at the midpoint of its (persisted) bounds

-- (2) the split, generic: axis `0 … 3` a gap, `4 … 9` a pair; the cut by mode (`qB`/`qBr`), both children closed (`cupd`)
def splitC (ih : WF) (md pos ax : ℕ) (c : Cl) (M : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) 0
      (let p := U (ih pos) (ofCl (cupd 4 PR SL ⟨c.L, c.U, c.A, c.B.set (Nat.sub ax 4) (qBr BND 64 c (Nat.sub ax 4) md)⟩
          (pI PR (Nat.sub ax 4)) (pJ PR (Nat.sub ax 4))) M)
       Bool.rec (motive := fun _ => ℕ) (U (ih p) (ofCl (cupd 4 PR SL ⟨c.L, c.U, c.A.set (Nat.sub ax 4) (qBr BND 64 c (Nat.sub ax 4) md), c.B⟩
          (pJ PR (Nat.sub ax 4)) (pI PR (Nat.sub ax 4))) M)) 0 (Nat.beq p 0))
      (Nat.blt ax 10))
    (let p := U (ih pos) (ofCl (cupd 4 PR SL ⟨c.L, c.U.set ax (qB BND 64 c ax md), c.A, c.B⟩ ax (ax + 1)) M)
     Bool.rec (motive := fun _ => ℕ) (U (ih p) (ofCl (cupd 4 PR SL ⟨c.L.set ax (qB BND 64 c ax md), c.U, c.A, c.B⟩ (ax + 1) ax) M)) 0 (Nat.beq p 0))
    (Nat.blt ax 4)
/-- a split node -/
def splitAx (ih : WF) (md pos ax : ℕ) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 A02 B02 A03 B03 A04 B04 A13 B13 A14 B14 A24 B24 M => splitC ih md pos ax ⟨[l0, l1, l2, l3], [u0, u1, u2, u3], [A02, A03, A04, A13, A14, A24], [B02, B03, B04, B13, B14, B24]⟩ M

theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) := by
  intro s h
  have h' : splitC ih md pos ax (toCl s) s.M ≠ 0 := h
  unfold splitC at h'
  cases hq : Nat.blt ax 4
  · rw [hq] at h'
    cases hr : Nat.blt ax 10
    · rw [hr] at h'; exact absurd rfl h'
    · rw [hr] at h'
      have hk : ax - 4 < 6 := by
        have h1 := Nat.blt_eq.mp hr; have h2 : ¬ ax < 4 := fun e => absurd (Nat.blt_eq.mpr e) (by rw [hq]; decide)
        omega
      exact sp_ok hih (cov_ssplitQ hSL hPR (ax - 4) (qBr BND 64 (toCl s) (ax - 4) md) rfl rfl hk) h'
        (cupd_len _ _ _ _ _ _) (cupd_len _ _ _ _ _ _)
  · rw [hq] at h'
    exact sp_ok hih (cov_gsplitQ hSL hPR ax (qB BND 64 (toCl s) ax md) rfl rfl (Nat.blt_eq.mp hq)) h'
      (cupd_len _ _ _ _ _ _) (cupd_len _ _ _ _ _ _)

-- (5) the root: the box sums written into the pair bounds (`matC`), once, which closes the root box (TZ.md §5)

def tm (k : ST) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 A02 B02 A03 B03 A04 B04 A13 B13 A14 B14 A24 B24 M => U k (ofCl (matC PR ⟨[l0, l1, l2, l3], [u0, u1, u2, u3], [A02, A03, A04, A13, A14, A24], [B02, B03, B04, B13, B14, B24]⟩) M)

theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2

-- (3) multipliers (HUFF.md §5.2): entries `[1][c code][side][Yq: qb bits]`, closed by `[0]`
structure YA where
  (o P0 P1 P2 P3 S0 S1 S2 S3 Cp Cm : ℕ)

def MulOK (s : St) (y : YA) : Prop :=
  MulOKg 4 PR (toCl s) [y.P0, y.P1, y.P2, y.P3] [y.S0, y.S1, y.S2, y.S3] y.Cp y.Cm

def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) ⟨(Nat.add o 1), y.P0, y.P1, y.P2, y.P3, y.S0, y.S1, y.S2, y.S3, y.Cp, y.Cm⟩
    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) 31) fun c => forceT (Nat.add o 6) fun o1 =>
     Bool.rec (motive := fun _ => YA) ⟨(Nat.add o1 (Nat.add qb 1)), y.P0, y.P1, y.P2, y.P3, y.S0, y.S1, y.S2, y.S3, y.Cp, y.Cm⟩
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih ⟨(Nat.add o1 (Nat.add qb 1)), (Nat.add y.P0 (Nat.mul Ylo (ind (inr 0 i j)))), (Nat.add y.P1 (Nat.mul Ylo (ind (inr 1 i j)))), (Nat.add y.P2 (Nat.mul Ylo (ind (inr 2 i j)))), (Nat.add y.P3 (Nat.mul Ylo (ind (inr 3 i j)))), (Nat.add y.S0 (Nat.mul Yhi (ind (inr 0 i j)))), (Nat.add y.S1 (Nat.mul Yhi (ind (inr 1 i j)))), (Nat.add y.S2 (Nat.mul Yhi (ind (inr 2 i j)))), (Nat.add y.S3 (Nat.mul Yhi (ind (inr 3 i j)))), (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))), (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0))))⟩)
      (Nat.blt c 6))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)

def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel

theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := fun _ _ => by simp

theorem ystep_ok (s : St) (qb w : ℕ) {ih : YA → YA} (hih : ∀ y, MulOK s y → MulOK s (ih y)) (y : YA) (h : MulOK s y) :
    MulOK s (ystep (toCl s).L (toCl s).A (toCl s).B qb w ih y) := by
  unfold ystep
  simp only [forceT_eq]
  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => h) fun hc => hih _ (mul_step hPR rfl rfl h (Nat.blt_eq.mp hc) _ _)

theorem ydec_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOK s y → MulOK s (ydec (toCl s).L (toCl s).A (toCl s).B qb w fuel y)
  | 0, _, h => h
  | n + 1, y, h => ystep_ok s qb w (ydec_ok s qb w n) y h

/-- (generic) one term's fixed-width fields at bit `o`, as `dec4F` reads them: the term `(κ, m, p, r)` and the next bit -/
def fld4 (w o L U : ℕ) : Term × ℕ :=
  ((Nat.land (Nat.shiftRight w o) 3,
    Nat.shiftLeft (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0
        (Nat.land (Nat.shiftRight w (Nat.add o 16)) 255) (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 3))
      (Nat.land (Nat.shiftRight w (Nat.add o 9)) 255) (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 2)) 2,
    Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 127)) 0 (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 0),
    Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 9)) 127)) (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 3)),
   Nat.add o (plenF 8 (Nat.land (Nat.shiftRight w o) 3)))
/-- (generic) every term's fields in term order, each on its effective range -/
def decAll (w : ℕ) (c : Cl) : List ℕ → ℕ → List Term × ℕ :=
  List.rec (motive := fun _ => ℕ → List Term × ℕ) (fun o => ([], o))
    (fun n _ ih o => (fun t : Term × ℕ => (fun r : List Term × ℕ => (t.1 :: r.1, r.2)) (ih t.2)) (fld4 w o (eL TS c n) (eU TS c n)))
/-- the minorant leaf (generic): decode, multipliers, then `mcheckGX` with the coarse-first term check -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  (fun d : List Term × ℕ => (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
      (mcheckGX (mokTZC R top bk tD bD pb 8 3) top bk pb 4 BS TS cN (toCl s) d.1
        [y.P0, y.P1, y.P2, y.P3] [y.S0, y.S1, y.S2, y.S3] y.Cp y.Cm))
    (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨d.2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩))
  (decAll w (toCl s) (List.range TS.length) 0)

theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) :=
  mcheckGX_soundL (f := pb) (mtermTZC hlb hD hpt hR (by decide : 0 < 8)) hPR hTS
    (ydec_ok s 12 w 42 _ (MulOK_zero s _)) (brec_ne h)

/-- (kind 8) the Farkas leaf (HUFF.md §6): the multiplier list only (`Yq` in 12 bits), accepted when the multiplier form
is negative on the whole box -/
def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [y.P0, y.P1, y.P2, y.P3] [y.S0, y.S1, y.S2, y.S3] 4)) y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

/-- a leaf (bit 0 clear): the reflected half-space (`u3 < l0`, no further bits), else bit 1 the kind (minorant leaf, or
Farkas leaf) with its payload from bit 2 -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun l0 u0 l1 u1 l2 u2 l3 u3 A02 B02 A03 B03 A04 B04 A13 B13 A14 B14 A24 B24 M =>
    forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, A02, B02, A03, B03, A04, B04, A13, B13, A14, B14, A24, B24, M⟩)
        (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, A02, B02, A03, B03, A04, B04, A13, B13, A14, B14, A24, B24, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
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
def ADJ : List ℕ := [0, 3, 6, 8]
theorem hADJ : ∀ r < 4, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide

/-- (root) the certificate on every point with nonnegative gaps, from the per-gap covers (`coverChk`) and the walks over
the root cells (`rootCl`: a bad segment per gap, pair bounds absent) -/
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < 4, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < 4, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 4, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : 4 * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < 4, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl 4 6 W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < 4, 0 ≤ g r) → PgL cN 4 BS TS g :=
  root_coverL hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun

/-- the root: every pair bound absent (`A = 0`, `B = W ≥ Σ u`) -/
theorem covered_box (s : St) (W : ℕ) (hA : ∀ k < 6, (toCl s).A.getD k 0 = 0) (hB : ∀ k < 6, (toCl s).B.getD k 0 = W)
    (hW : sumR (toCl s).U 0 4 ≤ W) (h : Covered (toCl s)) (g : ℕ → ℝ) (hb : InBox 4 (toCl s) g) : PgL cN 4 BS TS g :=
  h g (incell_root hPR hA hB hW hb)


end AMW.Cert.PCE4G
