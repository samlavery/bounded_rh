import AMW.PCellNoRefl
import AMW.PCellCloseB
import AMW.PCDZ

/-! ###### polytope cells for Q = 3: the instance layer with the exact closure and Z
(instance layer: bridge-port, amg/genpcell4.py; the closure splits, the closure walk and its chunk lemmas: mvt-engine,
eight/am8/genpcellC.py, TZ.md §5)

Kernel functions unrolled on the curried state (6 gap and 6 pair bounds, the mask); every proof is a link to
the generic layer `AMW.PCellGen` through `toCl : St → Cl`.  The walk is mvt-engine's fixed-width DATA layout (emit8pz.py).
Engine, tables and per-term minorants: mvt-engine's MinCore on the AM
engine (pyramid oracle adapted from five-point-pyramid-2 by typh, Apache-2.0). ###### -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace AMW.Cert.PCE3

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

def cN : ℕ := 210530
/-- the multiplier quantum: `Y = SIG · Yq`, `Yq < 2^12` (`2^-14` per unit g) -/
def SIG : ℕ := 6250000000000000

/-- the non-adjacent pairs, in pair order -/
def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 3)]
theorem hPR : PRok 3 PR := by decide
/-- the gap weights and the terms `(i, j, a, k)` of the functional `Fg` (units 1/SA) -/
def BS : List ℕ := [28898, 57272, 75526]
def TS : List Term := [(0, 1, 13630830, 0), (0, 3, 19565904, 1), (1, 2, 29997996, 0), (1, 3, 30621878, 2), (2, 3, 37356140, 0)]
theorem hTS : TSok 3 PR TS := by decide

/-- the slot of the pair `(a, b)`, `a < b`, at `a · 4 + b`: gap `a` when `b = a + 1`, else `3` + the pair's rank -/
def SL : List ℕ := [0, 0, 3, 4, 0, 0, 1, 5, 0, 0, 0, 2, 0, 0, 0, 0]
theorem hSL : SLok 3 PR SL := by decide

/-- the convex-region boundaries, sorted (the boundary split cuts at the one nearest the midpoint, ≥ BMARG = 64 inside) -/
def BND : List ℕ := [16384, 40384, 56768, 73664, 89920, 106176, 122304, 138560, 155136, 171456, 187712, 203840, 220224, 236480, 253120, 269440, 285760, 302080, 318720, 335168, 351872, 368384, 384896, 401280, 417728, 434048, 450496, 466816, 483264, 499584, 516032, 524288]

def SA : ℕ := 100000000

/-- the weighted functional on the gaps, in real form (pair weights `a_ij` and pressures `b_r` over `SA`) -/
def G (g0 g1 g2 : ℝ) : ℝ :=
  (28898 / (SA:ℝ)) * g0 + (57272 / (SA:ℝ)) * g1 + (75526 / (SA:ℝ)) * g2
    + (13630830 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (19565904 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (29997996 / (SA:ℝ)) * wfun (g1) + (30621878 / (SA:ℝ)) * wfun (g1 + g2) + (37356140 / (SA:ℝ)) * wfun (g2)

/-- the integer functional `Fg` on a tuple of gaps is `SA · G` -/
theorem Fg_G (x0 x1 x2 : ℝ) : Fg 3 BS TS (fun r => [x0, x1, x2].getD r 0) = (SA : ℝ) * G x0 x1 x2 := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring

/-- the canonical tables (HUFF.md §3): per table the count of each code length from 0, and the symbols in table order
(16-bit fields); a term's symbol is `κ · 2^14 + j1 · 2^7 + j2`, the axis `0 … 2` a gap, `3 …` a pair (pair order),
the multiplier's `c` the pair's rank -/
-- (fixed-width fields: no tables)

abbrev Covered : Cl → Prop := CovBy 3 PR (PgL cN 3 BS TS)

/-- the kernel state -/
structure St where
  (l0 u0 l1 u1 l2 u2 A02 B02 A03 B03 A13 B13 M : ℕ)

def toCl (s : St) : Cl :=
  ⟨[s.l0, s.l1, s.l2], [s.u0, s.u1, s.u2],
   [s.A02, s.A03, s.A13], [s.B02, s.B03, s.B13]⟩
def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨c.L.getD 0 0, c.U.getD 0 0, c.L.getD 1 0, c.U.getD 1 0, c.L.getD 2 0, c.U.getD 2 0, c.A.getD 0 0, c.B.getD 0 0, c.A.getD 1 0, c.B.getD 1 0, c.A.getD 2 0, c.B.getD 2 0, m⟩

theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = 3) (h2 : c.U.length = 3) (h3 : c.A.length = 3) (h4 : c.B.length = 3) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]

abbrev ST : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
/-- a continuation applied to a state -/
def U (k : ST) (s : St) : ℕ := k s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.A02 s.B02 s.A03 s.B03 s.A13 s.B13 s.M
def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
def zK : ST := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h

theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = 3) (h2 : c.U.length = 3) (h3 : c.A.length = 3)
    (h4 : c.B.length = 3) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h

/-- a split node's two children (`cA` from `pos`, the bit after the axis code, then `cB`) cover the cell when the split lemma does -/
theorem sp_ok {ih : WF} (hih : WalkOK ih) {s : St} {cA cB : Cl} {pos mA mB : ℕ}
    (hc : Covered cA → Covered cB → Covered (toCl s))
    (h : Bool.rec (motive := fun _ => ℕ) (U (ih (U (ih pos) (ofCl cA mA))) (ofCl cB mB)) 0
      (Nat.beq (U (ih pos) (ofCl cA mA)) 0) ≠ 0)
    (hA : cA.L.length = 3 ∧ cA.U.length = 3 ∧ cA.A.length = 3 ∧ cA.B.length = 3)
    (hB : cB.L.length = 3 ∧ cB.U.length = 3 ∧ cB.A.length = 3 ∧ cB.B.length = 3) : Covered (toCl s) := by
  cases hp : Nat.beq (U (ih pos) (ofCl cA mA)) 0
  · rw [hp] at h
    exact hc (ofCl_ok (hih _) hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 fun h0 => by rw [h0] at hp; exact absurd hp (by decide))
      (ofCl_ok (hih _) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 h)
  · rw [hp] at h; exact absurd rfl h


-- (2) split nodes: gap r at the midpoint of [l_r, u_r]; pair t at the midpoint of its (persisted) bounds

def gsplit0 (ih : WF) (md pos a b c d e f g h i j l m n : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add a b) 1) (bcutL BND 64 a b) (Nat.beq md 1);
  let ka0 := nmin q q;
  let ka1 := nmax c (Nat.sub g q);
  let ka2 := nmax e (Nat.sub i (Nat.add q d));
  let ka3 := nmin f (Nat.sub (Nat.add q m) g);
  let ka4 := nmin h (Nat.add q d);
  let ka5 := nmin j (Nat.add q m);
  let ka6 := nmax l (Nat.sub i q);
  let p := ih pos a ka0 ka1 d ka2 ka3 g ka4 i ka5 ka6 m n
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax q q;
    let kb1 := nmin d (Nat.sub h q);
    let kb2 := nmax e (Nat.sub (Nat.add l q) h);
    let kb3 := nmin f (Nat.sub j (Nat.add c q));
    let kb4 := nmax g (Nat.add c q);
    let kb5 := nmax i (Nat.add l q);
    let kb6 := nmin m (Nat.sub j q);
    ih p kb0 b c kb1 kb2 kb3 kb4 h kb5 j l kb6 n) 0 (Nat.beq p 0)

def gsplit1 (ih : WF) (md pos a b c d e f g h i j l m n : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add c d) 1) (bcutL BND 64 c d) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub g q);
  let ka1 := nmin q q;
  let ka2 := nmax e (Nat.sub l q);
  let ka3 := nmin h (Nat.add b q);
  let ka4 := nmax i (Nat.sub (Nat.add l g) q);
  let ka5 := nmin j (Nat.add (Nat.add b q) f);
  let ka6 := nmin m (Nat.add q f);
  let p := ih pos ka0 b c ka1 ka2 f g ka3 ka4 ka5 l ka6 n
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub h q);
    let kb1 := nmax q q;
    let kb2 := nmin f (Nat.sub m q);
    let kb3 := nmax g (Nat.add q a);
    let kb4 := nmax i (Nat.add (Nat.add e q) a);
    let kb5 := nmin j (Nat.sub (Nat.add h m) q);
    let kb6 := nmax l (Nat.add e q);
    ih p a kb0 kb1 d e kb2 kb3 h kb4 kb5 kb6 m n) 0 (Nat.beq p 0)

def gsplit2 (ih : WF) (md pos a b c d e f g h i j l m n : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add e f) 1) (bcutL BND 64 e f) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub i (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add h q) l);
  let ka2 := nmax c (Nat.sub l q);
  let ka3 := nmin q q;
  let ka4 := nmax g (Nat.sub i q);
  let ka5 := nmin j (Nat.add h q);
  let ka6 := nmin m (Nat.add d q);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 h i ka5 l ka6 n
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q g) m);
    let kb1 := nmin b (Nat.sub j (Nat.add q c));
    let kb2 := nmin d (Nat.sub m q);
    let kb3 := nmax q q;
    let kb4 := nmin h (Nat.sub j q);
    let kb5 := nmax i (Nat.add q g);
    let kb6 := nmax l (Nat.add q c);
    ih p kb0 kb1 c kb2 kb3 f g kb4 kb5 j kb6 m n) 0 (Nat.beq p 0)

def ssplit02 (ih : WF) (md pos a b c d e f g h i j l m n : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add g h) 1) (bcutL BND 64 g h) (Nat.beq md 1);
  let ka0 := nmin b (Nat.sub q c);
  let ka1 := nmin d (Nat.sub q a);
  let ka2 := nmax e (Nat.sub i q);
  let ka3 := nmin q q;
  let ka4 := nmin j (Nat.add q f);
  let ka5 := nmax l (Nat.sub (Nat.add i c) q);
  let ka6 := nmin m (Nat.sub (Nat.add q f) a);
  let p := ih pos a ka0 c ka1 ka2 f g ka3 i ka4 ka5 ka6 n
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q d);
    let kb1 := nmax c (Nat.sub q b);
    let kb2 := nmin f (Nat.sub j q);
    let kb3 := nmax q q;
    let kb4 := nmax i (Nat.add e q);
    let kb5 := nmax l (Nat.sub (Nat.add e q) b);
    let kb6 := nmin m (Nat.sub (Nat.add d j) q);
    ih p kb0 b kb1 d e kb2 kb3 h kb4 j kb5 kb6 n) 0 (Nat.beq p 0)

def ssplit03 (ih : WF) (md pos a b c d e f g h i j l m n : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add i j) 1) (bcutL BND 64 i j) (Nat.beq md 1);
  let ka0 := nmin b (Nat.sub q l);
  let ka1 := nmax c (Nat.sub (Nat.add g l) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a e));
  let ka3 := nmin f (Nat.sub q g);
  let ka4 := nmin h (Nat.sub q e);
  let ka5 := nmin q q;
  let ka6 := nmin m (Nat.sub q a);
  let p := ih pos a ka0 ka1 ka2 e ka3 g ka4 i ka5 l ka6 n
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q m);
    let kb1 := nmax c (Nat.sub q (Nat.add f b));
    let kb2 := nmin d (Nat.sub (Nat.add m h) q);
    let kb3 := nmax e (Nat.sub q h);
    let kb4 := nmax g (Nat.sub q f);
    let kb5 := nmax q q;
    let kb6 := nmax l (Nat.sub q b);
    ih p kb0 b kb1 kb2 kb3 f kb4 h kb5 j kb6 m n) 0 (Nat.beq p 0)

def ssplit13 (ih : WF) (md pos a b c d e f g h i j l m n : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add l m) 1) (bcutL BND 64 l m) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub i q);
  let ka1 := nmin d (Nat.sub q e);
  let ka2 := nmin f (Nat.sub q c);
  let ka3 := nmax g (Nat.sub (Nat.add c i) q);
  let ka4 := nmin h (Nat.sub (Nat.add b q) e);
  let ka5 := nmin j (Nat.add b q);
  let ka6 := nmin q q;
  let p := ih pos ka0 b c ka1 e ka2 ka3 ka4 i ka5 l ka6 n
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub j q);
    let kb1 := nmax c (Nat.sub q f);
    let kb2 := nmax e (Nat.sub q d);
    let kb3 := nmax g (Nat.sub (Nat.add q a) f);
    let kb4 := nmin h (Nat.sub (Nat.add j d) q);
    let kb5 := nmax i (Nat.add q a);
    let kb6 := nmax q q;
    ih p a kb0 kb1 d kb2 f kb3 kb4 kb5 j kb6 m n) 0 (Nat.beq p 0)

section
variable {ih : WF} (hih : WalkOK ih) (md pos : ℕ)
include hih
set_option hygiene false in
/-- a split node's link: unfold, then the generic midpoint split -/
macro "pc_spl " n:ident c:term : term =>
  `(fun s h => by simp only [U, $n:ident] at h; exact sp_ok hih (pos := pos) $c h ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩)
theorem gsplit0_ok : CovK (gsplit0 ih md pos) := pc_spl gsplit0 (cov_gsplitQ hSL hPR 0 (qB BND 64 (toCl s) 0 md) rfl rfl (by decide))
theorem gsplit1_ok : CovK (gsplit1 ih md pos) := pc_spl gsplit1 (cov_gsplitQ hSL hPR 1 (qB BND 64 (toCl s) 1 md) rfl rfl (by decide))
theorem gsplit2_ok : CovK (gsplit2 ih md pos) := pc_spl gsplit2 (cov_gsplitQ hSL hPR 2 (qB BND 64 (toCl s) 2 md) rfl rfl (by decide))
theorem ssplit02_ok : CovK (ssplit02 ih md pos) := pc_spl ssplit02 (cov_ssplitQ hSL hPR 0 (qBr BND 64 (toCl s) 0 md) rfl rfl (by decide))
theorem ssplit03_ok : CovK (ssplit03 ih md pos) := pc_spl ssplit03 (cov_ssplitQ hSL hPR 1 (qBr BND 64 (toCl s) 1 md) rfl rfl (by decide))
theorem ssplit13_ok : CovK (ssplit13 ih md pos) := pc_spl ssplit13 (cov_ssplitQ hSL hPR 2 (qBr BND 64 (toCl s) 2 md) rfl rfl (by decide))
end

/-- a split node: axis `0 … 2` a gap, `3 … 5` a pair (pair order) -/
def splitAx (ih : WF) (md pos ax : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (zK) (ssplit13 ih md pos) (Nat.beq ax 5)) (ssplit03 ih md pos) (Nat.beq ax 4)) (ssplit02 ih md pos) (Nat.beq ax 3)) (gsplit2 ih md pos) (Nat.beq ax 2)) (gsplit1 ih md pos) (Nat.beq ax 1)) (gsplit0 ih md pos) (Nat.beq ax 0)

theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) :=
  brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => zK_ok) (fun _ => ssplit13_ok hih md pos)) (fun _ => ssplit03_ok hih md pos)) (fun _ => ssplit02_ok hih md pos)) (fun _ => gsplit2_ok hih md pos)) (fun _ => gsplit1_ok hih md pos)) (fun _ => gsplit0_ok hih md pos)

-- (5) the root: the box sums written into the pair bounds (`matC`), once, which closes the root box (TZ.md §5)

def tm (k : ST) (a b c d e f g h i j l m n : ℕ) : ℕ :=
  forceR (nmax g (Nat.add a c)) fun g' => forceR (nmin h (Nat.add b d)) fun h' =>
  forceR (nmax i (Nat.add (Nat.add a c) e)) fun i' => forceR (nmin j (Nat.add (Nat.add b d) f)) fun j' =>
  forceR (nmax l (Nat.add c e)) fun l' => forceR (nmin m (Nat.add d f)) fun m' =>
  k a b c d e f g' h' i' j' l' m' n

theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2

-- (3) multipliers (HUFF.md §5.2): entries `[1][c code][side][Yq: qb bits]`, closed by `[0]`
structure YA where
  (o P0 P1 P2 S0 S1 S2 Cp Cm : ℕ)

def MulOK (s : St) (y : YA) : Prop :=
  MulOKg 3 PR (toCl s) [y.P0, y.P1, y.P2] [y.S0, y.S1, y.S2] y.Cp y.Cm

def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) ⟨(Nat.add o 1), y.P0, y.P1, y.P2, y.S0, y.S1, y.S2, y.Cp, y.Cm⟩
    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) 31) fun c => forceT (Nat.add o 6) fun o1 =>
     Bool.rec (motive := fun _ => YA) ⟨(Nat.add o1 (Nat.add qb 1)), y.P0, y.P1, y.P2, y.S0, y.S1, y.S2, y.Cp, y.Cm⟩
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih ⟨(Nat.add o1 (Nat.add qb 1)), (Nat.add y.P0 (Nat.mul Ylo (ind (inr 0 i j)))), (Nat.add y.P1 (Nat.mul Ylo (ind (inr 1 i j)))), (Nat.add y.P2 (Nat.mul Ylo (ind (inr 2 i j)))), (Nat.add y.S0 (Nat.mul Yhi (ind (inr 0 i j)))), (Nat.add y.S1 (Nat.mul Yhi (ind (inr 1 i j)))), (Nat.add y.S2 (Nat.mul Yhi (ind (inr 2 i j)))), (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))), (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0))))⟩)
      (Nat.blt c 3))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)

def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel

theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, 0, 0, 0, 0, 0, 0, 0, 0⟩ := fun _ _ => by simp

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
    (k01 m01 p01 r01 k03 m03 p03 r03 k12 m12 p12 r12 k13 m13 p13 r13 k23 m23 p23 r23 : ℕ) (P0 P1 P2 S0 S1 S2 Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mcK f false s.l0 k01 m01 p01 r01))) (Nat.mul 19565904 (mcK f false (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 29997996 (mcK f false s.l1 k12 m12 p12 r12))) (Nat.mul 30621878 (mcK f false (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 37356140 (mcK f false s.l2 k23 m23 p23 r23))) Cp) (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub s.u0 s.l0) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add 0 (Nat.mul 13630830 (mwT k01 m01))) (Nat.mul 19565904 (mwT k03 m03)))) P0) (Nat.add (Nat.add (Nat.mul 1024000000000 28898) (Nat.add (Nat.add 0 (Nat.mul 13630830 (mslK f k01 m01 p01 r01))) (Nat.mul 19565904 (mslK f k03 m03 p03 r03)))) S0)))) (Nat.mul (Nat.sub s.u1 s.l1) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 29997996 (mwT k12 m12))) (Nat.mul 30621878 (mwT k13 m13)))) P1) (Nat.add (Nat.add (Nat.mul 1024000000000 57272) (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 29997996 (mslK f k12 m12 p12 r12))) (Nat.mul 30621878 (mslK f k13 m13 p13 r13)))) S1)))) (Nat.mul (Nat.sub s.u2 s.l2) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 30621878 (mwT k13 m13))) (Nat.mul 37356140 (mwT k23 m23)))) P2) (Nat.add (Nat.add (Nat.mul 1024000000000 75526) (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 30621878 (mslK f k13 m13 p13 r13))) (Nat.mul 37356140 (mslK f k23 m23 p23 r23)))) S2))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add 0 (Nat.mul 28898 s.l0)) (Nat.mul 57272 s.l1)) (Nat.mul 75526 s.l2))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mvKF top bk f s.l0 (uc s.l0 s.u0) k01 m01 p01 r01))) (Nat.mul 19565904 (mvKF top bk f (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (uc (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2))) k03 m03 p03 r03))) (Nat.mul 29997996 (mvKF top bk f s.l1 (uc s.l1 s.u1) k12 m12 p12 r12))) (Nat.mul 30621878 (mvKF top bk f (nmax s.A13 (Nat.add s.l1 s.l2)) (uc (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2))) k13 m13 p13 r13))) (Nat.mul 37356140 (mvKF top bk f s.l2 (uc s.l2 s.u2) k23 m23 p23 r23))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mcK f true s.l0 k01 m01 p01 r01))) (Nat.mul 19565904 (mcK f true (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 29997996 (mcK f true s.l1 k12 m12 p12 r12))) (Nat.mul 30621878 (mcK f true (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 37356140 (mcK f true s.l2 k23 m23 p23 r23))) Cm)))) (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l2 s.u2 k23 m23 p23 r23) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2)) k13 m13 p13 r13) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l1 s.u1 k12 m12 p12 r12) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) k03 m03 p03 r03) (Bool.rec (motive := fun _ => Bool) false (mokTZC R top bk tD bD f 8 3 s.l0 s.u0 k01 m01 p01 r01) (true)))))) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l2 s.u2) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l1 s.u1) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l0 s.u0) (true)))))

theorem mcheckP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k12 m12 p12 r12 k13 m13 p13 r13 k23 m23 p23 r23 : ℕ) (P0 P1 P2 S0 S1 S2 Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s k01 m01 p01 r01 k03 m03 p03 r03 k12 m12 p12 r12 k13 m13 p13 r13 k23 m23 p23 r23 P0 P1 P2 S0 S1 S2 Cp Cm = true) :
    mcheckGX (mokTZC R top bk tD bD f 8 3) top bk f 3 BS TS cN (toCl s) [(k01, m01, p01, r01), (k03, m03, p03, r03), (k12, m12, p12, r12), (k13, m13, p13, r13), (k23, m23, p23, r23)]
      [P0, P1, P2] [S0, S1, S2] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq, mvKF_eq] at h; exact h

/-- the polytope minorant leaf (HUFF.md §5): the payload length when the check passes, else `0` -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  forceR (nmax s.A02 (Nat.add s.l0 s.l1)) fun L02 => forceR (nmin s.B02 (Nat.add s.u0 s.u1)) fun U02 =>
  forceR (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) fun L03 => forceR (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) fun U03 =>
  forceR (nmax s.A13 (Nat.add s.l1 s.l2)) fun L13 => forceR (nmin s.B13 (Nat.add s.u1 s.u2)) fun U13 =>
  forceR 0 fun o0 =>
  dec4F 8 w o0 s.l0 s.u0 fun k01 m01 p01 r01 o1 =>
  dec4F 8 w o1 L03 U03 fun k03 m03 p03 r03 o2 =>
  dec4F 8 w o2 s.l1 s.u1 fun k12 m12 p12 r12 o3 =>
  dec4F 8 w o3 L13 U13 fun k13 m13 p13 r13 o4 =>
  dec4F 8 w o4 s.l2 s.u2 fun k23 m23 p23 r23 o5 =>
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s k01 m01 p01 r01 k03 m03 p03 r03 k12 m12 p12 r12 k13 m13 p13 r13 k23 m23 p23 r23 y.P0 y.P1 y.P2 y.S0 y.S1 y.S2 y.Cp y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨o5, 0, 0, 0, 0, 0, 0, 0, 0⟩)

theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  unfold mleafP at h
  simp only [dec4F, forceR_eq] at h
  exact mcheckGX_soundL (f := pb) (mtermTZC hlb hD hpt hR (by decide : 0 < 8)) hPR hTS (ydec_ok s 12 w 42 _ (MulOK_zero s _)) (mcheckP_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h))

/-- (kind 8) the Farkas leaf (HUFF.md §6): the multiplier list only (`Yq` in 12 bits), accepted when the multiplier form
is negative on the whole box -/
def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [y.P0, y.P1, y.P2] [y.S0, y.S1, y.S2] 3)) y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

/-- a leaf (bit 0 clear): the reflected half-space (`u2 < l0`, no further bits), else bit 1 the kind (minorant leaf, or
Farkas leaf) with its payload from bit 2 -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun l0 u0 l1 u1 l2 u2 A02 B02 A03 B03 A13 B13 M =>
    forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, A02, B02, A03, B03, A13, B13, M⟩)
        (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, A02, B02, A03, B03, A13, B13, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
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

/-- (chunked walks) field-wise equality of two states -/
def stEq (a b : St) : Bool := Nat.beq a.l0 b.l0 && Nat.beq a.u0 b.u0 && Nat.beq a.l1 b.l1 && Nat.beq a.u1 b.u1 && Nat.beq a.l2 b.l2 && Nat.beq a.u2 b.u2 && Nat.beq a.A02 b.A02 && Nat.beq a.B02 b.B02 && Nat.beq a.A03 b.A03 && Nat.beq a.B03 b.B03 && Nat.beq a.A13 b.A13 && Nat.beq a.B13 b.B13 && Nat.beq a.M b.M
theorem St_eq {a b : St} (h : stEq a b = true) : a = b := by
  cases a; cases b
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  subst_vars; rfl
/-- the continuation that accepts exactly the state `t` -/
def kEq (t : St) : ST := fun l0 u0 l1 u1 l2 u2 A02 B02 A03 B03 A13 B13 M => Bool.rec (motive := fun _ => ℕ) 0 1 (stEq ⟨l0, u0, l1, u1, l2, u2, A02, B02, A03, B03, A13, B13, M⟩ t)
theorem kEq_ok {t : St} (h : Covered (toCl t)) : CovK (kEq t) := fun s hs => by
  have e : U (kEq t) s = Bool.rec (motive := fun _ => ℕ) 0 1 (stEq s t) := rfl
  rw [e] at hs
  cases hb : stEq s t
  · rw [hb] at hs; exact absurd rfl hs
  · rw [St_eq hb]; exact h
/-- a chunked root: `tm` takes the root box `s` to its closed state `t` (computed) -/
theorem tm_to {s t : St} (hT : U (tm (kEq t)) s = 1) (h : Covered (toCl t)) : Covered (toCl s) :=
  tm_ok (kEq_ok h) s (by rw [hT]; decide)
/-- a chunk boundary's split on gap `r` at its midpoint, the children closed (`cupd`) -/
theorem gsplit_to (r : ℕ) (hr : r < 3) {t sA sB : St}
    (eA : toCl sA = cupd 3 PR SL ⟨(toCl t).L, (toCl t).U.set r (qG (toCl t) r), (toCl t).A, (toCl t).B⟩ r (r + 1))
    (eB : toCl sB = cupd 3 PR SL ⟨(toCl t).L.set r (qG (toCl t) r), (toCl t).U, (toCl t).A, (toCl t).B⟩ (r + 1) r)
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_gmidC hSL hPR r rfl rfl hr (eA ▸ hA) (eB ▸ hB)
/-- a chunk boundary's split on pair `k` at the raw midpoint of its bounds, the children closed (`cupd`) -/
theorem ssplit_to (k : ℕ) (hk : k < 3) {t sA sB : St}
    (eA : toCl sA = cupd 3 PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A, (toCl t).B.set k (qR (toCl t) k)⟩ (pI PR k) (pJ PR k))
    (eB : toCl sB = cupd 3 PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A.set k (qR (toCl t) k), (toCl t).B⟩ (pJ PR k) (pI PR k))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_rmidC hSL hPR k rfl rfl hk (eA ▸ hA) (eB ▸ hB)
/-- a walk from any bit position -/
theorem covered_of_walkP {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits fuel pos e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel pos s (h ▸ he)

/-- the adjacent term of each gap (its index in `TS`) -/
def ADJ : List ℕ := [0, 2, 4]
theorem hADJ : ∀ r < 3, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide

/-- (root) the certificate on every point with nonnegative gaps, from the per-gap covers (`coverChk`) and the walks over
the root cells (`rootCl`: a bad segment per gap, pair bounds absent) -/
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < 3, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < 3, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 3, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : 3 * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < 3, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl 3 3 W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < 3, 0 ≤ g r) → PgL cN 3 BS TS g :=
  root_coverL hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun

/-- the root: every pair bound absent (`A = 0`, `B = W ≥ Σ u`) -/
theorem covered_box (s : St) (W : ℕ) (hA : ∀ k < 3, (toCl s).A.getD k 0 = 0) (hB : ∀ k < 3, (toCl s).B.getD k 0 = W)
    (hW : sumR (toCl s).U 0 3 ≤ W) (h : Covered (toCl s)) (g : ℕ → ℝ) (hb : InBox 3 (toCl s) g) : PgL cN 3 BS TS g :=
  h g (incell_root hPR hA hB hW hb)


end AMW.Cert.PCE3
