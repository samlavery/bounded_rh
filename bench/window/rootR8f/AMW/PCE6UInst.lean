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

namespace AMW.Cert.PCE6U

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

def gsplit0 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add a b) 1) (bcutL BND 64 a b) (Nat.beq md 1);
  let ka0 := nmin q q;
  let ka1 := nmax c (Nat.sub n q);
  let ka2 := nmax e (Nat.sub r (Nat.add q d));
  let ka3 := nmin f (Nat.sub (Nat.add q A) n);
  let ka4 := nmax g (Nat.sub t (Nat.add q A));
  let ka5 := nmin h (Nat.sub (Nat.add q C) r);
  let ka6 := nmax i (Nat.sub v (Nat.add q C));
  let ka7 := nmin j (Nat.sub (Nat.add q E) t);
  let ka8 := nmax l (Nat.sub x (Nat.add q E));
  let ka9 := nmin m (Nat.sub (Nat.add q G) v);
  let ka10 := nmin o (Nat.add q d);
  let ka11 := nmin s (Nat.add q A);
  let ka12 := nmin u (Nat.add q C);
  let ka13 := nmin w (Nat.add q E);
  let ka14 := nmin y (Nat.add q G);
  let ka15 := nmax z (Nat.sub r q);
  let ka16 := nmax B (Nat.sub t q);
  let ka17 := nmax D (Nat.sub v q);
  let ka18 := nmax F (Nat.sub x q);
  let ka19 := nmax H (Nat.sub t (Nat.add q d));
  let ka20 := nmin I (Nat.sub (Nat.add q C) n);
  let ka21 := nmax J (Nat.sub v (Nat.add q d));
  let ka22 := nmin K (Nat.sub (Nat.add q E) n);
  let ka23 := nmax L (Nat.sub x (Nat.add q d));
  let ka24 := nmin M (Nat.sub (Nat.add q G) n);
  let ka25 := nmax N (Nat.sub v (Nat.add q A));
  let ka26 := nmin O (Nat.sub (Nat.add q E) r);
  let ka27 := nmax P (Nat.sub x (Nat.add q A));
  let ka28 := nmin Q (Nat.sub (Nat.add q G) r);
  let ka29 := nmax R (Nat.sub x (Nat.add q C));
  let ka30 := nmin S (Nat.sub (Nat.add q G) t);
  let p := ih pos a ka0 ka1 d ka2 ka3 ka4 ka5 ka6 ka7 ka8 ka9 n ka10 r ka11 t ka12 v ka13 x ka14 ka15 A ka16 C ka17 E ka18 G ka19 ka20 ka21 ka22 ka23 ka24 ka25 ka26 ka27 ka28 ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax q q;
    let kb1 := nmin d (Nat.sub o q);
    let kb2 := nmax e (Nat.sub (Nat.add z q) o);
    let kb3 := nmin f (Nat.sub s (Nat.add c q));
    let kb4 := nmax g (Nat.sub (Nat.add B q) s);
    let kb5 := nmin h (Nat.sub u (Nat.add z q));
    let kb6 := nmax i (Nat.sub (Nat.add D q) u);
    let kb7 := nmin j (Nat.sub w (Nat.add B q));
    let kb8 := nmax l (Nat.sub (Nat.add F q) w);
    let kb9 := nmin m (Nat.sub y (Nat.add D q));
    let kb10 := nmax n (Nat.add c q);
    let kb11 := nmax r (Nat.add z q);
    let kb12 := nmax t (Nat.add B q);
    let kb13 := nmax v (Nat.add D q);
    let kb14 := nmax x (Nat.add F q);
    let kb15 := nmin A (Nat.sub s q);
    let kb16 := nmin C (Nat.sub u q);
    let kb17 := nmin E (Nat.sub w q);
    let kb18 := nmin G (Nat.sub y q);
    let kb19 := nmax H (Nat.sub (Nat.add B q) o);
    let kb20 := nmin I (Nat.sub u (Nat.add c q));
    let kb21 := nmax J (Nat.sub (Nat.add D q) o);
    let kb22 := nmin K (Nat.sub w (Nat.add c q));
    let kb23 := nmax L (Nat.sub (Nat.add F q) o);
    let kb24 := nmin M (Nat.sub y (Nat.add c q));
    let kb25 := nmax N (Nat.sub (Nat.add D q) s);
    let kb26 := nmin O (Nat.sub w (Nat.add z q));
    let kb27 := nmax P (Nat.sub (Nat.add F q) s);
    let kb28 := nmin Q (Nat.sub y (Nat.add z q));
    let kb29 := nmax R (Nat.sub (Nat.add F q) u);
    let kb30 := nmin S (Nat.sub y (Nat.add B q));
    ih p kb0 b c kb1 kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 o kb11 s kb12 u kb13 w kb14 y z kb15 B kb16 D kb17 F kb18 kb19 kb20 kb21 kb22 kb23 kb24 kb25 kb26 kb27 kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def gsplit1 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add c d) 1) (bcutL BND 64 c d) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub n q);
  let ka1 := nmin q q;
  let ka2 := nmax e (Nat.sub z q);
  let ka3 := nmax g (Nat.sub B (Nat.add q f));
  let ka4 := nmin h (Nat.sub (Nat.add q I) z);
  let ka5 := nmax i (Nat.sub D (Nat.add q I));
  let ka6 := nmin j (Nat.sub (Nat.add q K) B);
  let ka7 := nmax l (Nat.sub F (Nat.add q K));
  let ka8 := nmin m (Nat.sub (Nat.add q M) D);
  let ka9 := nmin o (Nat.add b q);
  let ka10 := nmax r (Nat.sub (Nat.add z n) q);
  let ka11 := nmin s (Nat.add (Nat.add b q) f);
  let ka12 := nmax t (Nat.sub (Nat.add B n) q);
  let ka13 := nmin u (Nat.add (Nat.add b q) I);
  let ka14 := nmax v (Nat.sub (Nat.add D n) q);
  let ka15 := nmin w (Nat.add (Nat.add b q) K);
  let ka16 := nmax x (Nat.sub (Nat.add F n) q);
  let ka17 := nmin y (Nat.add (Nat.add b q) M);
  let ka18 := nmin A (Nat.add q f);
  let ka19 := nmin C (Nat.add q I);
  let ka20 := nmin E (Nat.add q K);
  let ka21 := nmin G (Nat.add q M);
  let ka22 := nmax H (Nat.sub B q);
  let ka23 := nmax J (Nat.sub D q);
  let ka24 := nmax L (Nat.sub F q);
  let ka25 := nmax N (Nat.sub D (Nat.add q f));
  let ka26 := nmin O (Nat.sub (Nat.add q K) z);
  let ka27 := nmax P (Nat.sub F (Nat.add q f));
  let ka28 := nmin Q (Nat.sub (Nat.add q M) z);
  let ka29 := nmax R (Nat.sub F (Nat.add q I));
  let ka30 := nmin S (Nat.sub (Nat.add q M) B);
  let p := ih pos ka0 b c ka1 ka2 f ka3 ka4 ka5 ka6 ka7 ka8 n ka9 ka10 ka11 ka12 ka13 ka14 ka15 ka16 ka17 z ka18 B ka19 D ka20 F ka21 ka22 I ka23 K ka24 M ka25 ka26 ka27 ka28 ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub o q);
    let kb1 := nmax q q;
    let kb2 := nmin f (Nat.sub A q);
    let kb3 := nmax g (Nat.sub (Nat.add H q) A);
    let kb4 := nmin h (Nat.sub C (Nat.add e q));
    let kb5 := nmax i (Nat.sub (Nat.add J q) C);
    let kb6 := nmin j (Nat.sub E (Nat.add H q));
    let kb7 := nmax l (Nat.sub (Nat.add L q) E);
    let kb8 := nmin m (Nat.sub G (Nat.add J q));
    let kb9 := nmax n (Nat.add q a);
    let kb10 := nmax r (Nat.add (Nat.add e q) a);
    let kb11 := nmin s (Nat.sub (Nat.add o A) q);
    let kb12 := nmax t (Nat.add (Nat.add H q) a);
    let kb13 := nmin u (Nat.sub (Nat.add o C) q);
    let kb14 := nmax v (Nat.add (Nat.add J q) a);
    let kb15 := nmin w (Nat.sub (Nat.add o E) q);
    let kb16 := nmax x (Nat.add (Nat.add L q) a);
    let kb17 := nmin y (Nat.sub (Nat.add o G) q);
    let kb18 := nmax z (Nat.add e q);
    let kb19 := nmax B (Nat.add H q);
    let kb20 := nmax D (Nat.add J q);
    let kb21 := nmax F (Nat.add L q);
    let kb22 := nmin I (Nat.sub C q);
    let kb23 := nmin K (Nat.sub E q);
    let kb24 := nmin M (Nat.sub G q);
    let kb25 := nmax N (Nat.sub (Nat.add J q) A);
    let kb26 := nmin O (Nat.sub E (Nat.add e q));
    let kb27 := nmax P (Nat.sub (Nat.add L q) A);
    let kb28 := nmin Q (Nat.sub G (Nat.add e q));
    let kb29 := nmax R (Nat.sub (Nat.add L q) C);
    let kb30 := nmin S (Nat.sub G (Nat.add H q));
    ih p a kb0 kb1 d e kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 o kb10 kb11 kb12 kb13 kb14 kb15 kb16 kb17 kb18 A kb19 C kb20 E kb21 G H kb22 J kb23 L kb24 kb25 kb26 kb27 kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def gsplit2 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add e f) 1) (bcutL BND 64 e f) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub r (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add o q) z);
  let ka2 := nmax c (Nat.sub z q);
  let ka3 := nmin q q;
  let ka4 := nmax g (Nat.sub H q);
  let ka5 := nmax i (Nat.sub J (Nat.add q h));
  let ka6 := nmin j (Nat.sub (Nat.add q O) H);
  let ka7 := nmax l (Nat.sub L (Nat.add q O));
  let ka8 := nmin m (Nat.sub (Nat.add q Q) J);
  let ka9 := nmax n (Nat.sub r q);
  let ka10 := nmin s (Nat.add o q);
  let ka11 := nmax t (Nat.sub (Nat.add H r) q);
  let ka12 := nmin u (Nat.add (Nat.add o q) h);
  let ka13 := nmax v (Nat.sub (Nat.add J r) q);
  let ka14 := nmin w (Nat.add (Nat.add o q) O);
  let ka15 := nmax x (Nat.sub (Nat.add L r) q);
  let ka16 := nmin y (Nat.add (Nat.add o q) Q);
  let ka17 := nmin A (Nat.add d q);
  let ka18 := nmax B (Nat.sub (Nat.add H z) q);
  let ka19 := nmin C (Nat.add (Nat.add d q) h);
  let ka20 := nmax D (Nat.sub (Nat.add J z) q);
  let ka21 := nmin E (Nat.add (Nat.add d q) O);
  let ka22 := nmax F (Nat.sub (Nat.add L z) q);
  let ka23 := nmin G (Nat.add (Nat.add d q) Q);
  let ka24 := nmin I (Nat.add q h);
  let ka25 := nmin K (Nat.add q O);
  let ka26 := nmin M (Nat.add q Q);
  let ka27 := nmax N (Nat.sub J q);
  let ka28 := nmax P (Nat.sub L q);
  let ka29 := nmax R (Nat.sub L (Nat.add q h));
  let ka30 := nmin S (Nat.sub (Nat.add q Q) H);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 h ka5 ka6 ka7 ka8 ka9 o r ka10 ka11 ka12 ka13 ka14 ka15 ka16 z ka17 ka18 ka19 ka20 ka21 ka22 ka23 H ka24 J ka25 L ka26 ka27 O ka28 Q ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q n) A);
    let kb1 := nmin b (Nat.sub s (Nat.add q c));
    let kb2 := nmin d (Nat.sub A q);
    let kb3 := nmax q q;
    let kb4 := nmin h (Nat.sub I q);
    let kb5 := nmax i (Nat.sub (Nat.add N q) I);
    let kb6 := nmin j (Nat.sub K (Nat.add g q));
    let kb7 := nmax l (Nat.sub (Nat.add P q) K);
    let kb8 := nmin m (Nat.sub M (Nat.add N q));
    let kb9 := nmin o (Nat.sub s q);
    let kb10 := nmax r (Nat.add q n);
    let kb11 := nmax t (Nat.add (Nat.add g q) n);
    let kb12 := nmin u (Nat.sub (Nat.add s I) q);
    let kb13 := nmax v (Nat.add (Nat.add N q) n);
    let kb14 := nmin w (Nat.sub (Nat.add s K) q);
    let kb15 := nmax x (Nat.add (Nat.add P q) n);
    let kb16 := nmin y (Nat.sub (Nat.add s M) q);
    let kb17 := nmax z (Nat.add q c);
    let kb18 := nmax B (Nat.add (Nat.add g q) c);
    let kb19 := nmin C (Nat.sub (Nat.add A I) q);
    let kb20 := nmax D (Nat.add (Nat.add N q) c);
    let kb21 := nmin E (Nat.sub (Nat.add A K) q);
    let kb22 := nmax F (Nat.add (Nat.add P q) c);
    let kb23 := nmin G (Nat.sub (Nat.add A M) q);
    let kb24 := nmax H (Nat.add g q);
    let kb25 := nmax J (Nat.add N q);
    let kb26 := nmax L (Nat.add P q);
    let kb27 := nmin O (Nat.sub K q);
    let kb28 := nmin Q (Nat.sub M q);
    let kb29 := nmax R (Nat.sub (Nat.add P q) I);
    let kb30 := nmin S (Nat.sub M (Nat.add g q));
    ih p kb0 kb1 c kb2 kb3 f g kb4 kb5 kb6 kb7 kb8 n kb9 kb10 s kb11 kb12 kb13 kb14 kb15 kb16 kb17 A kb18 kb19 kb20 kb21 kb22 kb23 kb24 I kb25 K kb26 M N kb27 P kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def gsplit3 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add g h) 1) (bcutL BND 64 g h) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub t (Nat.add A q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) B);
  let ka2 := nmax c (Nat.sub B (Nat.add f q));
  let ka3 := nmin d (Nat.sub (Nat.add A q) H);
  let ka4 := nmax e (Nat.sub H q);
  let ka5 := nmin q q;
  let ka6 := nmax i (Nat.sub N q);
  let ka7 := nmax l (Nat.sub P (Nat.add q j));
  let ka8 := nmin m (Nat.sub (Nat.add q S) N);
  let ka9 := nmax n (Nat.sub t (Nat.add f q));
  let ka10 := nmin o (Nat.sub (Nat.add s q) H);
  let ka11 := nmax r (Nat.sub t q);
  let ka12 := nmin u (Nat.add s q);
  let ka13 := nmax v (Nat.sub (Nat.add N t) q);
  let ka14 := nmin w (Nat.add (Nat.add s q) j);
  let ka15 := nmax x (Nat.sub (Nat.add P t) q);
  let ka16 := nmin y (Nat.add (Nat.add s q) S);
  let ka17 := nmax z (Nat.sub B q);
  let ka18 := nmin C (Nat.add A q);
  let ka19 := nmax D (Nat.sub (Nat.add N B) q);
  let ka20 := nmin E (Nat.add (Nat.add A q) j);
  let ka21 := nmax F (Nat.sub (Nat.add P B) q);
  let ka22 := nmin G (Nat.add (Nat.add A q) S);
  let ka23 := nmin I (Nat.add f q);
  let ka24 := nmax J (Nat.sub (Nat.add N H) q);
  let ka25 := nmin K (Nat.add (Nat.add f q) j);
  let ka26 := nmax L (Nat.sub (Nat.add P H) q);
  let ka27 := nmin M (Nat.add (Nat.add f q) S);
  let ka28 := nmin O (Nat.add q j);
  let ka29 := nmin Q (Nat.add q S);
  let ka30 := nmax R (Nat.sub P q);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 f g ka5 ka6 j ka7 ka8 ka9 ka10 ka11 s t ka12 ka13 ka14 ka15 ka16 ka17 A B ka18 ka19 ka20 ka21 ka22 H ka23 ka24 ka25 ka26 ka27 N ka28 P ka29 ka30 S T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) C);
    let kb1 := nmin b (Nat.sub u (Nat.add q z));
    let kb2 := nmax c (Nat.sub (Nat.add q z) I);
    let kb3 := nmin d (Nat.sub C (Nat.add q e));
    let kb4 := nmin f (Nat.sub I q);
    let kb5 := nmax q q;
    let kb6 := nmin j (Nat.sub O q);
    let kb7 := nmax l (Nat.sub (Nat.add R q) O);
    let kb8 := nmin m (Nat.sub Q (Nat.add i q));
    let kb9 := nmax n (Nat.sub (Nat.add q r) I);
    let kb10 := nmin o (Nat.sub u (Nat.add q e));
    let kb11 := nmin s (Nat.sub u q);
    let kb12 := nmax t (Nat.add q r);
    let kb13 := nmax v (Nat.add (Nat.add i q) r);
    let kb14 := nmin w (Nat.sub (Nat.add u O) q);
    let kb15 := nmax x (Nat.add (Nat.add R q) r);
    let kb16 := nmin y (Nat.sub (Nat.add u Q) q);
    let kb17 := nmin A (Nat.sub C q);
    let kb18 := nmax B (Nat.add q z);
    let kb19 := nmax D (Nat.add (Nat.add i q) z);
    let kb20 := nmin E (Nat.sub (Nat.add C O) q);
    let kb21 := nmax F (Nat.add (Nat.add R q) z);
    let kb22 := nmin G (Nat.sub (Nat.add C Q) q);
    let kb23 := nmax H (Nat.add q e);
    let kb24 := nmax J (Nat.add (Nat.add i q) e);
    let kb25 := nmin K (Nat.sub (Nat.add I O) q);
    let kb26 := nmax L (Nat.add (Nat.add R q) e);
    let kb27 := nmin M (Nat.sub (Nat.add I Q) q);
    let kb28 := nmax N (Nat.add i q);
    let kb29 := nmax P (Nat.add R q);
    let kb30 := nmin S (Nat.sub Q q);
    ih p kb0 kb1 kb2 kb3 e kb4 kb5 h i kb6 kb7 kb8 kb9 kb10 r kb11 kb12 u kb13 kb14 kb15 kb16 z kb17 kb18 C kb19 kb20 kb21 kb22 kb23 I kb24 kb25 kb26 kb27 kb28 O kb29 Q R kb30 T) 0 (Nat.beq p 0)

def gsplit4 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add i j) 1) (bcutL BND 64 i j) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub v (Nat.add C q));
  let ka1 := nmin b (Nat.sub (Nat.add u q) D);
  let ka2 := nmax c (Nat.sub D (Nat.add I q));
  let ka3 := nmin d (Nat.sub (Nat.add C q) J);
  let ka4 := nmax e (Nat.sub J (Nat.add h q));
  let ka5 := nmin f (Nat.sub (Nat.add I q) N);
  let ka6 := nmax g (Nat.sub N q);
  let ka7 := nmin q q;
  let ka8 := nmax l (Nat.sub R q);
  let ka9 := nmax n (Nat.sub v (Nat.add I q));
  let ka10 := nmin o (Nat.sub (Nat.add u q) J);
  let ka11 := nmax r (Nat.sub v (Nat.add h q));
  let ka12 := nmin s (Nat.sub (Nat.add u q) N);
  let ka13 := nmax t (Nat.sub v q);
  let ka14 := nmin w (Nat.add u q);
  let ka15 := nmax x (Nat.sub (Nat.add R v) q);
  let ka16 := nmin y (Nat.add (Nat.add u q) m);
  let ka17 := nmax z (Nat.sub D (Nat.add h q));
  let ka18 := nmin A (Nat.sub (Nat.add C q) N);
  let ka19 := nmax B (Nat.sub D q);
  let ka20 := nmin E (Nat.add C q);
  let ka21 := nmax F (Nat.sub (Nat.add R D) q);
  let ka22 := nmin G (Nat.add (Nat.add C q) m);
  let ka23 := nmax H (Nat.sub J q);
  let ka24 := nmin K (Nat.add I q);
  let ka25 := nmax L (Nat.sub (Nat.add R J) q);
  let ka26 := nmin M (Nat.add (Nat.add I q) m);
  let ka27 := nmin O (Nat.add h q);
  let ka28 := nmax P (Nat.sub (Nat.add R N) q);
  let ka29 := nmin Q (Nat.add (Nat.add h q) m);
  let ka30 := nmin S (Nat.add q m);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 h i ka7 ka8 m ka9 ka10 ka11 ka12 ka13 u v ka14 ka15 ka16 ka17 ka18 ka19 C D ka20 ka21 ka22 ka23 I J ka24 ka25 ka26 N ka27 ka28 ka29 R ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q t) E);
    let kb1 := nmin b (Nat.sub w (Nat.add q B));
    let kb2 := nmax c (Nat.sub (Nat.add q B) K);
    let kb3 := nmin d (Nat.sub E (Nat.add q H));
    let kb4 := nmax e (Nat.sub (Nat.add q H) O);
    let kb5 := nmin f (Nat.sub K (Nat.add q g));
    let kb6 := nmin h (Nat.sub O q);
    let kb7 := nmax q q;
    let kb8 := nmin m (Nat.sub S q);
    let kb9 := nmax n (Nat.sub (Nat.add q t) K);
    let kb10 := nmin o (Nat.sub w (Nat.add q H));
    let kb11 := nmax r (Nat.sub (Nat.add q t) O);
    let kb12 := nmin s (Nat.sub w (Nat.add q g));
    let kb13 := nmin u (Nat.sub w q);
    let kb14 := nmax v (Nat.add q t);
    let kb15 := nmax x (Nat.add (Nat.add l q) t);
    let kb16 := nmin y (Nat.sub (Nat.add w S) q);
    let kb17 := nmax z (Nat.sub (Nat.add q B) O);
    let kb18 := nmin A (Nat.sub E (Nat.add q g));
    let kb19 := nmin C (Nat.sub E q);
    let kb20 := nmax D (Nat.add q B);
    let kb21 := nmax F (Nat.add (Nat.add l q) B);
    let kb22 := nmin G (Nat.sub (Nat.add E S) q);
    let kb23 := nmin I (Nat.sub K q);
    let kb24 := nmax J (Nat.add q H);
    let kb25 := nmax L (Nat.add (Nat.add l q) H);
    let kb26 := nmin M (Nat.sub (Nat.add K S) q);
    let kb27 := nmax N (Nat.add q g);
    let kb28 := nmax P (Nat.add (Nat.add l q) g);
    let kb29 := nmin Q (Nat.sub (Nat.add O S) q);
    let kb30 := nmax R (Nat.add l q);
    ih p kb0 kb1 kb2 kb3 kb4 kb5 g kb6 kb7 j l kb8 kb9 kb10 kb11 kb12 t kb13 kb14 w kb15 kb16 kb17 kb18 B kb19 kb20 E kb21 kb22 H kb23 kb24 K kb25 kb26 kb27 O kb28 kb29 kb30 S T) 0 (Nat.beq p 0)

def gsplit5 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add l m) 1) (bcutL BND 64 l m) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub x (Nat.add E q));
  let ka1 := nmin b (Nat.sub (Nat.add w q) F);
  let ka2 := nmax c (Nat.sub F (Nat.add K q));
  let ka3 := nmin d (Nat.sub (Nat.add E q) L);
  let ka4 := nmax e (Nat.sub L (Nat.add O q));
  let ka5 := nmin f (Nat.sub (Nat.add K q) P);
  let ka6 := nmax g (Nat.sub P (Nat.add j q));
  let ka7 := nmin h (Nat.sub (Nat.add O q) R);
  let ka8 := nmax i (Nat.sub R q);
  let ka9 := nmin q q;
  let ka10 := nmax n (Nat.sub x (Nat.add K q));
  let ka11 := nmin o (Nat.sub (Nat.add w q) L);
  let ka12 := nmax r (Nat.sub x (Nat.add O q));
  let ka13 := nmin s (Nat.sub (Nat.add w q) P);
  let ka14 := nmax t (Nat.sub x (Nat.add j q));
  let ka15 := nmin u (Nat.sub (Nat.add w q) R);
  let ka16 := nmax v (Nat.sub x q);
  let ka17 := nmin y (Nat.add w q);
  let ka18 := nmax z (Nat.sub F (Nat.add O q));
  let ka19 := nmin A (Nat.sub (Nat.add E q) P);
  let ka20 := nmax B (Nat.sub F (Nat.add j q));
  let ka21 := nmin C (Nat.sub (Nat.add E q) R);
  let ka22 := nmax D (Nat.sub F q);
  let ka23 := nmin G (Nat.add E q);
  let ka24 := nmax H (Nat.sub L (Nat.add j q));
  let ka25 := nmin I (Nat.sub (Nat.add K q) R);
  let ka26 := nmax J (Nat.sub L q);
  let ka27 := nmin M (Nat.add K q);
  let ka28 := nmax N (Nat.sub P q);
  let ka29 := nmin Q (Nat.add O q);
  let ka30 := nmin S (Nat.add j q);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 j l ka9 ka10 ka11 ka12 ka13 ka14 ka15 ka16 w x ka17 ka18 ka19 ka20 ka21 ka22 E F ka23 ka24 ka25 ka26 K L ka27 ka28 O P ka29 R ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q v) G);
    let kb1 := nmin b (Nat.sub y (Nat.add q D));
    let kb2 := nmax c (Nat.sub (Nat.add q D) M);
    let kb3 := nmin d (Nat.sub G (Nat.add q J));
    let kb4 := nmax e (Nat.sub (Nat.add q J) Q);
    let kb5 := nmin f (Nat.sub M (Nat.add q N));
    let kb6 := nmax g (Nat.sub (Nat.add q N) S);
    let kb7 := nmin h (Nat.sub Q (Nat.add q i));
    let kb8 := nmin j (Nat.sub S q);
    let kb9 := nmax q q;
    let kb10 := nmax n (Nat.sub (Nat.add q v) M);
    let kb11 := nmin o (Nat.sub y (Nat.add q J));
    let kb12 := nmax r (Nat.sub (Nat.add q v) Q);
    let kb13 := nmin s (Nat.sub y (Nat.add q N));
    let kb14 := nmax t (Nat.sub (Nat.add q v) S);
    let kb15 := nmin u (Nat.sub y (Nat.add q i));
    let kb16 := nmin w (Nat.sub y q);
    let kb17 := nmax x (Nat.add q v);
    let kb18 := nmax z (Nat.sub (Nat.add q D) Q);
    let kb19 := nmin A (Nat.sub G (Nat.add q N));
    let kb20 := nmax B (Nat.sub (Nat.add q D) S);
    let kb21 := nmin C (Nat.sub G (Nat.add q i));
    let kb22 := nmin E (Nat.sub G q);
    let kb23 := nmax F (Nat.add q D);
    let kb24 := nmax H (Nat.sub (Nat.add q J) S);
    let kb25 := nmin I (Nat.sub M (Nat.add q i));
    let kb26 := nmin K (Nat.sub M q);
    let kb27 := nmax L (Nat.add q J);
    let kb28 := nmin O (Nat.sub Q q);
    let kb29 := nmax P (Nat.add q N);
    let kb30 := nmax R (Nat.add q i);
    ih p kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 i kb8 kb9 m kb10 kb11 kb12 kb13 kb14 kb15 v kb16 kb17 y kb18 kb19 kb20 kb21 D kb22 kb23 G kb24 kb25 J kb26 kb27 M N kb28 kb29 Q kb30 S T) 0 (Nat.beq p 0)

def ssplit02 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add n o) 1) (bcutL BND 64 n o) (Nat.beq md 1);
  let ka0 := nmin b (Nat.sub q c);
  let ka1 := nmin d (Nat.sub q a);
  let ka2 := nmax e (Nat.sub r q);
  let ka3 := nmax g (Nat.sub t (Nat.add q f));
  let ka4 := nmin h (Nat.sub (Nat.add q I) r);
  let ka5 := nmax i (Nat.sub v (Nat.add q I));
  let ka6 := nmin j (Nat.sub (Nat.add q K) t);
  let ka7 := nmax l (Nat.sub x (Nat.add q K));
  let ka8 := nmin m (Nat.sub (Nat.add q M) v);
  let ka9 := nmin q q;
  let ka10 := nmin s (Nat.add q f);
  let ka11 := nmin u (Nat.add q I);
  let ka12 := nmin w (Nat.add q K);
  let ka13 := nmin y (Nat.add q M);
  let ka14 := nmax z (Nat.sub (Nat.add r c) q);
  let ka15 := nmin A (Nat.sub (Nat.add q f) a);
  let ka16 := nmax B (Nat.sub (Nat.add t c) q);
  let ka17 := nmin C (Nat.sub (Nat.add q I) a);
  let ka18 := nmax D (Nat.sub (Nat.add v c) q);
  let ka19 := nmin E (Nat.sub (Nat.add q K) a);
  let ka20 := nmax F (Nat.sub (Nat.add x c) q);
  let ka21 := nmin G (Nat.sub (Nat.add q M) a);
  let ka22 := nmax H (Nat.sub t q);
  let ka23 := nmax J (Nat.sub v q);
  let ka24 := nmax L (Nat.sub x q);
  let ka25 := nmax N (Nat.sub v (Nat.add q f));
  let ka26 := nmin O (Nat.sub (Nat.add q K) r);
  let ka27 := nmax P (Nat.sub x (Nat.add q f));
  let ka28 := nmin Q (Nat.sub (Nat.add q M) r);
  let ka29 := nmax R (Nat.sub x (Nat.add q I));
  let ka30 := nmin S (Nat.sub (Nat.add q M) t);
  let p := ih pos a ka0 c ka1 ka2 f ka3 ka4 ka5 ka6 ka7 ka8 n ka9 r ka10 t ka11 v ka12 x ka13 ka14 ka15 ka16 ka17 ka18 ka19 ka20 ka21 ka22 I ka23 K ka24 M ka25 ka26 ka27 ka28 ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q d);
    let kb1 := nmax c (Nat.sub q b);
    let kb2 := nmin f (Nat.sub s q);
    let kb3 := nmax g (Nat.sub (Nat.add H q) s);
    let kb4 := nmin h (Nat.sub u (Nat.add e q));
    let kb5 := nmax i (Nat.sub (Nat.add J q) u);
    let kb6 := nmin j (Nat.sub w (Nat.add H q));
    let kb7 := nmax l (Nat.sub (Nat.add L q) w);
    let kb8 := nmin m (Nat.sub y (Nat.add J q));
    let kb9 := nmax q q;
    let kb10 := nmax r (Nat.add e q);
    let kb11 := nmax t (Nat.add H q);
    let kb12 := nmax v (Nat.add J q);
    let kb13 := nmax x (Nat.add L q);
    let kb14 := nmax z (Nat.sub (Nat.add e q) b);
    let kb15 := nmin A (Nat.sub (Nat.add d s) q);
    let kb16 := nmax B (Nat.sub (Nat.add H q) b);
    let kb17 := nmin C (Nat.sub (Nat.add d u) q);
    let kb18 := nmax D (Nat.sub (Nat.add J q) b);
    let kb19 := nmin E (Nat.sub (Nat.add d w) q);
    let kb20 := nmax F (Nat.sub (Nat.add L q) b);
    let kb21 := nmin G (Nat.sub (Nat.add d y) q);
    let kb22 := nmin I (Nat.sub u q);
    let kb23 := nmin K (Nat.sub w q);
    let kb24 := nmin M (Nat.sub y q);
    let kb25 := nmax N (Nat.sub (Nat.add J q) s);
    let kb26 := nmin O (Nat.sub w (Nat.add e q));
    let kb27 := nmax P (Nat.sub (Nat.add L q) s);
    let kb28 := nmin Q (Nat.sub y (Nat.add e q));
    let kb29 := nmax R (Nat.sub (Nat.add L q) u);
    let kb30 := nmin S (Nat.sub y (Nat.add H q));
    ih p kb0 b kb1 d e kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 o kb10 s kb11 u kb12 w kb13 y kb14 kb15 kb16 kb17 kb18 kb19 kb20 kb21 H kb22 J kb23 L kb24 kb25 kb26 kb27 kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def ssplit03 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add r s) 1) (bcutL BND 64 r s) (Nat.beq md 1);
  let ka0 := nmin b (Nat.sub q z);
  let ka1 := nmax c (Nat.sub (Nat.add n z) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a e));
  let ka3 := nmin f (Nat.sub q n);
  let ka4 := nmax g (Nat.sub t q);
  let ka5 := nmax i (Nat.sub v (Nat.add q h));
  let ka6 := nmin j (Nat.sub (Nat.add q O) t);
  let ka7 := nmax l (Nat.sub x (Nat.add q O));
  let ka8 := nmin m (Nat.sub (Nat.add q Q) v);
  let ka9 := nmin o (Nat.sub q e);
  let ka10 := nmin q q;
  let ka11 := nmin u (Nat.add q h);
  let ka12 := nmin w (Nat.add q O);
  let ka13 := nmin y (Nat.add q Q);
  let ka14 := nmin A (Nat.sub q a);
  let ka15 := nmax B (Nat.sub (Nat.add t z) q);
  let ka16 := nmin C (Nat.sub (Nat.add q h) a);
  let ka17 := nmax D (Nat.sub (Nat.add v z) q);
  let ka18 := nmin E (Nat.sub (Nat.add q O) a);
  let ka19 := nmax F (Nat.sub (Nat.add x z) q);
  let ka20 := nmin G (Nat.sub (Nat.add q Q) a);
  let ka21 := nmax H (Nat.sub (Nat.add t e) q);
  let ka22 := nmin I (Nat.sub (Nat.add q h) n);
  let ka23 := nmax J (Nat.sub (Nat.add v e) q);
  let ka24 := nmin K (Nat.sub (Nat.add q O) n);
  let ka25 := nmax L (Nat.sub (Nat.add x e) q);
  let ka26 := nmin M (Nat.sub (Nat.add q Q) n);
  let ka27 := nmax N (Nat.sub v q);
  let ka28 := nmax P (Nat.sub x q);
  let ka29 := nmax R (Nat.sub x (Nat.add q h));
  let ka30 := nmin S (Nat.sub (Nat.add q Q) t);
  let p := ih pos a ka0 ka1 ka2 e ka3 ka4 h ka5 ka6 ka7 ka8 n ka9 r ka10 t ka11 v ka12 x ka13 z ka14 ka15 ka16 ka17 ka18 ka19 ka20 ka21 ka22 ka23 ka24 ka25 ka26 ka27 O ka28 Q ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q A);
    let kb1 := nmax c (Nat.sub q (Nat.add f b));
    let kb2 := nmin d (Nat.sub (Nat.add A o) q);
    let kb3 := nmax e (Nat.sub q o);
    let kb4 := nmin h (Nat.sub u q);
    let kb5 := nmax i (Nat.sub (Nat.add N q) u);
    let kb6 := nmin j (Nat.sub w (Nat.add g q));
    let kb7 := nmax l (Nat.sub (Nat.add P q) w);
    let kb8 := nmin m (Nat.sub y (Nat.add N q));
    let kb9 := nmax n (Nat.sub q f);
    let kb10 := nmax q q;
    let kb11 := nmax t (Nat.add g q);
    let kb12 := nmax v (Nat.add N q);
    let kb13 := nmax x (Nat.add P q);
    let kb14 := nmax z (Nat.sub q b);
    let kb15 := nmax B (Nat.sub (Nat.add g q) b);
    let kb16 := nmin C (Nat.sub (Nat.add A u) q);
    let kb17 := nmax D (Nat.sub (Nat.add N q) b);
    let kb18 := nmin E (Nat.sub (Nat.add A w) q);
    let kb19 := nmax F (Nat.sub (Nat.add P q) b);
    let kb20 := nmin G (Nat.sub (Nat.add A y) q);
    let kb21 := nmax H (Nat.sub (Nat.add g q) o);
    let kb22 := nmin I (Nat.sub (Nat.add f u) q);
    let kb23 := nmax J (Nat.sub (Nat.add N q) o);
    let kb24 := nmin K (Nat.sub (Nat.add f w) q);
    let kb25 := nmax L (Nat.sub (Nat.add P q) o);
    let kb26 := nmin M (Nat.sub (Nat.add f y) q);
    let kb27 := nmin O (Nat.sub w q);
    let kb28 := nmin Q (Nat.sub y q);
    let kb29 := nmax R (Nat.sub (Nat.add P q) u);
    let kb30 := nmin S (Nat.sub y (Nat.add g q));
    ih p kb0 b kb1 kb2 kb3 f g kb4 kb5 kb6 kb7 kb8 kb9 o kb10 s kb11 u kb12 w kb13 y kb14 A kb15 kb16 kb17 kb18 kb19 kb20 kb21 kb22 kb23 kb24 kb25 kb26 N kb27 P kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def ssplit04 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add t u) 1) (bcutL BND 64 t u) (Nat.beq md 1);
  let ka0 := nmin b (Nat.sub q B);
  let ka1 := nmax c (Nat.sub (Nat.add n B) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a H));
  let ka3 := nmax e (Nat.sub (Nat.add r H) q);
  let ka4 := nmin f (Nat.sub q (Nat.add n g));
  let ka5 := nmin h (Nat.sub q r);
  let ka6 := nmax i (Nat.sub v q);
  let ka7 := nmax l (Nat.sub x (Nat.add q j));
  let ka8 := nmin m (Nat.sub (Nat.add q S) v);
  let ka9 := nmin o (Nat.sub q H);
  let ka10 := nmin s (Nat.sub q g);
  let ka11 := nmin q q;
  let ka12 := nmin w (Nat.add q j);
  let ka13 := nmin y (Nat.add q S);
  let ka14 := nmax z (Nat.sub (Nat.add r B) q);
  let ka15 := nmin A (Nat.sub q (Nat.add a g));
  let ka16 := nmin C (Nat.sub q a);
  let ka17 := nmax D (Nat.sub (Nat.add v B) q);
  let ka18 := nmin E (Nat.sub (Nat.add q j) a);
  let ka19 := nmax F (Nat.sub (Nat.add x B) q);
  let ka20 := nmin G (Nat.sub (Nat.add q S) a);
  let ka21 := nmin I (Nat.sub q n);
  let ka22 := nmax J (Nat.sub (Nat.add v H) q);
  let ka23 := nmin K (Nat.sub (Nat.add q j) n);
  let ka24 := nmax L (Nat.sub (Nat.add x H) q);
  let ka25 := nmin M (Nat.sub (Nat.add q S) n);
  let ka26 := nmax N (Nat.sub (Nat.add v g) q);
  let ka27 := nmin O (Nat.sub (Nat.add q j) r);
  let ka28 := nmax P (Nat.sub (Nat.add x g) q);
  let ka29 := nmin Q (Nat.sub (Nat.add q S) r);
  let ka30 := nmax R (Nat.sub x q);
  let p := ih pos a ka0 ka1 ka2 ka3 ka4 g ka5 ka6 j ka7 ka8 n ka9 r ka10 t ka11 v ka12 x ka13 ka14 ka15 B ka16 ka17 ka18 ka19 ka20 H ka21 ka22 ka23 ka24 ka25 ka26 ka27 ka28 ka29 ka30 S T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q C);
    let kb1 := nmax c (Nat.sub q (Nat.add I b));
    let kb2 := nmin d (Nat.sub (Nat.add C o) q);
    let kb3 := nmax e (Nat.sub q (Nat.add h o));
    let kb4 := nmin f (Nat.sub (Nat.add I s) q);
    let kb5 := nmax g (Nat.sub q s);
    let kb6 := nmin j (Nat.sub w q);
    let kb7 := nmax l (Nat.sub (Nat.add R q) w);
    let kb8 := nmin m (Nat.sub y (Nat.add i q));
    let kb9 := nmax n (Nat.sub q I);
    let kb10 := nmax r (Nat.sub q h);
    let kb11 := nmax q q;
    let kb12 := nmax v (Nat.add i q);
    let kb13 := nmax x (Nat.add R q);
    let kb14 := nmax z (Nat.sub q (Nat.add h b));
    let kb15 := nmin A (Nat.sub (Nat.add C s) q);
    let kb16 := nmax B (Nat.sub q b);
    let kb17 := nmax D (Nat.sub (Nat.add i q) b);
    let kb18 := nmin E (Nat.sub (Nat.add C w) q);
    let kb19 := nmax F (Nat.sub (Nat.add R q) b);
    let kb20 := nmin G (Nat.sub (Nat.add C y) q);
    let kb21 := nmax H (Nat.sub q o);
    let kb22 := nmax J (Nat.sub (Nat.add i q) o);
    let kb23 := nmin K (Nat.sub (Nat.add I w) q);
    let kb24 := nmax L (Nat.sub (Nat.add R q) o);
    let kb25 := nmin M (Nat.sub (Nat.add I y) q);
    let kb26 := nmax N (Nat.sub (Nat.add i q) s);
    let kb27 := nmin O (Nat.sub (Nat.add h w) q);
    let kb28 := nmax P (Nat.sub (Nat.add R q) s);
    let kb29 := nmin Q (Nat.sub (Nat.add h y) q);
    let kb30 := nmin S (Nat.sub y q);
    ih p kb0 b kb1 kb2 kb3 kb4 kb5 h i kb6 kb7 kb8 kb9 o kb10 s kb11 u kb12 w kb13 y kb14 kb15 kb16 C kb17 kb18 kb19 kb20 kb21 I kb22 kb23 kb24 kb25 kb26 kb27 kb28 kb29 R kb30 T) 0 (Nat.beq p 0)

def ssplit05 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add v w) 1) (bcutL BND 64 v w) (Nat.beq md 1);
  let ka0 := nmin b (Nat.sub q D);
  let ka1 := nmax c (Nat.sub (Nat.add n D) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a J));
  let ka3 := nmax e (Nat.sub (Nat.add r J) q);
  let ka4 := nmin f (Nat.sub q (Nat.add n N));
  let ka5 := nmax g (Nat.sub (Nat.add t N) q);
  let ka6 := nmin h (Nat.sub q (Nat.add r i));
  let ka7 := nmin j (Nat.sub q t);
  let ka8 := nmax l (Nat.sub x q);
  let ka9 := nmin o (Nat.sub q J);
  let ka10 := nmin s (Nat.sub q N);
  let ka11 := nmin u (Nat.sub q i);
  let ka12 := nmin q q;
  let ka13 := nmin y (Nat.add q m);
  let ka14 := nmax z (Nat.sub (Nat.add r D) q);
  let ka15 := nmin A (Nat.sub q (Nat.add a N));
  let ka16 := nmax B (Nat.sub (Nat.add t D) q);
  let ka17 := nmin C (Nat.sub q (Nat.add a i));
  let ka18 := nmin E (Nat.sub q a);
  let ka19 := nmax F (Nat.sub (Nat.add x D) q);
  let ka20 := nmin G (Nat.sub (Nat.add q m) a);
  let ka21 := nmax H (Nat.sub (Nat.add t J) q);
  let ka22 := nmin I (Nat.sub q (Nat.add n i));
  let ka23 := nmin K (Nat.sub q n);
  let ka24 := nmax L (Nat.sub (Nat.add x J) q);
  let ka25 := nmin M (Nat.sub (Nat.add q m) n);
  let ka26 := nmin O (Nat.sub q r);
  let ka27 := nmax P (Nat.sub (Nat.add x N) q);
  let ka28 := nmin Q (Nat.sub (Nat.add q m) r);
  let ka29 := nmax R (Nat.sub (Nat.add x i) q);
  let ka30 := nmin S (Nat.sub (Nat.add q m) t);
  let p := ih pos a ka0 ka1 ka2 ka3 ka4 ka5 ka6 i ka7 ka8 m n ka9 r ka10 t ka11 v ka12 x ka13 ka14 ka15 ka16 ka17 D ka18 ka19 ka20 ka21 ka22 J ka23 ka24 ka25 N ka26 ka27 ka28 ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q E);
    let kb1 := nmax c (Nat.sub q (Nat.add K b));
    let kb2 := nmin d (Nat.sub (Nat.add E o) q);
    let kb3 := nmax e (Nat.sub q (Nat.add O o));
    let kb4 := nmin f (Nat.sub (Nat.add K s) q);
    let kb5 := nmax g (Nat.sub q (Nat.add j s));
    let kb6 := nmin h (Nat.sub (Nat.add O u) q);
    let kb7 := nmax i (Nat.sub q u);
    let kb8 := nmin m (Nat.sub y q);
    let kb9 := nmax n (Nat.sub q K);
    let kb10 := nmax r (Nat.sub q O);
    let kb11 := nmax t (Nat.sub q j);
    let kb12 := nmax q q;
    let kb13 := nmax x (Nat.add l q);
    let kb14 := nmax z (Nat.sub q (Nat.add O b));
    let kb15 := nmin A (Nat.sub (Nat.add E s) q);
    let kb16 := nmax B (Nat.sub q (Nat.add j b));
    let kb17 := nmin C (Nat.sub (Nat.add E u) q);
    let kb18 := nmax D (Nat.sub q b);
    let kb19 := nmax F (Nat.sub (Nat.add l q) b);
    let kb20 := nmin G (Nat.sub (Nat.add E y) q);
    let kb21 := nmax H (Nat.sub q (Nat.add j o));
    let kb22 := nmin I (Nat.sub (Nat.add K u) q);
    let kb23 := nmax J (Nat.sub q o);
    let kb24 := nmax L (Nat.sub (Nat.add l q) o);
    let kb25 := nmin M (Nat.sub (Nat.add K y) q);
    let kb26 := nmax N (Nat.sub q s);
    let kb27 := nmax P (Nat.sub (Nat.add l q) s);
    let kb28 := nmin Q (Nat.sub (Nat.add O y) q);
    let kb29 := nmax R (Nat.sub (Nat.add l q) u);
    let kb30 := nmin S (Nat.sub (Nat.add j y) q);
    ih p kb0 b kb1 kb2 kb3 kb4 kb5 kb6 kb7 j l kb8 kb9 o kb10 s kb11 u kb12 w kb13 y kb14 kb15 kb16 kb17 kb18 E kb19 kb20 kb21 kb22 kb23 K kb24 kb25 kb26 O kb27 kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def ssplit06 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add x y) 1) (bcutL BND 64 x y) (Nat.beq md 1);
  let ka0 := nmin b (Nat.sub q F);
  let ka1 := nmax c (Nat.sub (Nat.add n F) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a L));
  let ka3 := nmax e (Nat.sub (Nat.add r L) q);
  let ka4 := nmin f (Nat.sub q (Nat.add n P));
  let ka5 := nmax g (Nat.sub (Nat.add t P) q);
  let ka6 := nmin h (Nat.sub q (Nat.add r R));
  let ka7 := nmax i (Nat.sub (Nat.add v R) q);
  let ka8 := nmin j (Nat.sub q (Nat.add t l));
  let ka9 := nmin m (Nat.sub q v);
  let ka10 := nmin o (Nat.sub q L);
  let ka11 := nmin s (Nat.sub q P);
  let ka12 := nmin u (Nat.sub q R);
  let ka13 := nmin w (Nat.sub q l);
  let ka14 := nmin q q;
  let ka15 := nmax z (Nat.sub (Nat.add r F) q);
  let ka16 := nmin A (Nat.sub q (Nat.add a P));
  let ka17 := nmax B (Nat.sub (Nat.add t F) q);
  let ka18 := nmin C (Nat.sub q (Nat.add a R));
  let ka19 := nmax D (Nat.sub (Nat.add v F) q);
  let ka20 := nmin E (Nat.sub q (Nat.add a l));
  let ka21 := nmin G (Nat.sub q a);
  let ka22 := nmax H (Nat.sub (Nat.add t L) q);
  let ka23 := nmin I (Nat.sub q (Nat.add n R));
  let ka24 := nmax J (Nat.sub (Nat.add v L) q);
  let ka25 := nmin K (Nat.sub q (Nat.add n l));
  let ka26 := nmin M (Nat.sub q n);
  let ka27 := nmax N (Nat.sub (Nat.add v P) q);
  let ka28 := nmin O (Nat.sub q (Nat.add r l));
  let ka29 := nmin Q (Nat.sub q r);
  let ka30 := nmin S (Nat.sub q t);
  let p := ih pos a ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 l ka9 n ka10 r ka11 t ka12 v ka13 x ka14 ka15 ka16 ka17 ka18 ka19 ka20 F ka21 ka22 ka23 ka24 ka25 L ka26 ka27 ka28 P ka29 R ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q G);
    let kb1 := nmax c (Nat.sub q (Nat.add M b));
    let kb2 := nmin d (Nat.sub (Nat.add G o) q);
    let kb3 := nmax e (Nat.sub q (Nat.add Q o));
    let kb4 := nmin f (Nat.sub (Nat.add M s) q);
    let kb5 := nmax g (Nat.sub q (Nat.add S s));
    let kb6 := nmin h (Nat.sub (Nat.add Q u) q);
    let kb7 := nmax i (Nat.sub q (Nat.add m u));
    let kb8 := nmin j (Nat.sub (Nat.add S w) q);
    let kb9 := nmax l (Nat.sub q w);
    let kb10 := nmax n (Nat.sub q M);
    let kb11 := nmax r (Nat.sub q Q);
    let kb12 := nmax t (Nat.sub q S);
    let kb13 := nmax v (Nat.sub q m);
    let kb14 := nmax q q;
    let kb15 := nmax z (Nat.sub q (Nat.add Q b));
    let kb16 := nmin A (Nat.sub (Nat.add G s) q);
    let kb17 := nmax B (Nat.sub q (Nat.add S b));
    let kb18 := nmin C (Nat.sub (Nat.add G u) q);
    let kb19 := nmax D (Nat.sub q (Nat.add m b));
    let kb20 := nmin E (Nat.sub (Nat.add G w) q);
    let kb21 := nmax F (Nat.sub q b);
    let kb22 := nmax H (Nat.sub q (Nat.add S o));
    let kb23 := nmin I (Nat.sub (Nat.add M u) q);
    let kb24 := nmax J (Nat.sub q (Nat.add m o));
    let kb25 := nmin K (Nat.sub (Nat.add M w) q);
    let kb26 := nmax L (Nat.sub q o);
    let kb27 := nmax N (Nat.sub q (Nat.add m s));
    let kb28 := nmin O (Nat.sub (Nat.add Q w) q);
    let kb29 := nmax P (Nat.sub q s);
    let kb30 := nmax R (Nat.sub q u);
    ih p kb0 b kb1 kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 m kb10 o kb11 s kb12 u kb13 w kb14 y kb15 kb16 kb17 kb18 kb19 kb20 kb21 G kb22 kb23 kb24 kb25 kb26 M kb27 kb28 kb29 Q kb30 S T) 0 (Nat.beq p 0)

def ssplit13 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add z A) 1) (bcutL BND 64 z A) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub r q);
  let ka1 := nmin d (Nat.sub q e);
  let ka2 := nmin f (Nat.sub q c);
  let ka3 := nmax g (Nat.sub B q);
  let ka4 := nmax i (Nat.sub D (Nat.add q h));
  let ka5 := nmin j (Nat.sub (Nat.add q O) B);
  let ka6 := nmax l (Nat.sub F (Nat.add q O));
  let ka7 := nmin m (Nat.sub (Nat.add q Q) D);
  let ka8 := nmax n (Nat.sub (Nat.add c r) q);
  let ka9 := nmin o (Nat.sub (Nat.add b q) e);
  let ka10 := nmin s (Nat.add b q);
  let ka11 := nmax t (Nat.sub (Nat.add B r) q);
  let ka12 := nmin u (Nat.add (Nat.add b q) h);
  let ka13 := nmax v (Nat.sub (Nat.add D r) q);
  let ka14 := nmin w (Nat.add (Nat.add b q) O);
  let ka15 := nmax x (Nat.sub (Nat.add F r) q);
  let ka16 := nmin y (Nat.add (Nat.add b q) Q);
  let ka17 := nmin q q;
  let ka18 := nmin C (Nat.add q h);
  let ka19 := nmin E (Nat.add q O);
  let ka20 := nmin G (Nat.add q Q);
  let ka21 := nmax H (Nat.sub (Nat.add B e) q);
  let ka22 := nmin I (Nat.sub (Nat.add q h) c);
  let ka23 := nmax J (Nat.sub (Nat.add D e) q);
  let ka24 := nmin K (Nat.sub (Nat.add q O) c);
  let ka25 := nmax L (Nat.sub (Nat.add F e) q);
  let ka26 := nmin M (Nat.sub (Nat.add q Q) c);
  let ka27 := nmax N (Nat.sub D q);
  let ka28 := nmax P (Nat.sub F q);
  let ka29 := nmax R (Nat.sub F (Nat.add q h));
  let ka30 := nmin S (Nat.sub (Nat.add q Q) B);
  let p := ih pos ka0 b c ka1 e ka2 ka3 h ka4 ka5 ka6 ka7 ka8 ka9 r ka10 ka11 ka12 ka13 ka14 ka15 ka16 z ka17 B ka18 D ka19 F ka20 ka21 ka22 ka23 ka24 ka25 ka26 ka27 O ka28 Q ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub s q);
    let kb1 := nmax c (Nat.sub q f);
    let kb2 := nmax e (Nat.sub q d);
    let kb3 := nmin h (Nat.sub C q);
    let kb4 := nmax i (Nat.sub (Nat.add N q) C);
    let kb5 := nmin j (Nat.sub E (Nat.add g q));
    let kb6 := nmax l (Nat.sub (Nat.add P q) E);
    let kb7 := nmin m (Nat.sub G (Nat.add N q));
    let kb8 := nmax n (Nat.sub (Nat.add q a) f);
    let kb9 := nmin o (Nat.sub (Nat.add s d) q);
    let kb10 := nmax r (Nat.add q a);
    let kb11 := nmax t (Nat.add (Nat.add g q) a);
    let kb12 := nmin u (Nat.sub (Nat.add s C) q);
    let kb13 := nmax v (Nat.add (Nat.add N q) a);
    let kb14 := nmin w (Nat.sub (Nat.add s E) q);
    let kb15 := nmax x (Nat.add (Nat.add P q) a);
    let kb16 := nmin y (Nat.sub (Nat.add s G) q);
    let kb17 := nmax q q;
    let kb18 := nmax B (Nat.add g q);
    let kb19 := nmax D (Nat.add N q);
    let kb20 := nmax F (Nat.add P q);
    let kb21 := nmax H (Nat.sub (Nat.add g q) d);
    let kb22 := nmin I (Nat.sub (Nat.add f C) q);
    let kb23 := nmax J (Nat.sub (Nat.add N q) d);
    let kb24 := nmin K (Nat.sub (Nat.add f E) q);
    let kb25 := nmax L (Nat.sub (Nat.add P q) d);
    let kb26 := nmin M (Nat.sub (Nat.add f G) q);
    let kb27 := nmin O (Nat.sub E q);
    let kb28 := nmin Q (Nat.sub G q);
    let kb29 := nmax R (Nat.sub (Nat.add P q) C);
    let kb30 := nmin S (Nat.sub G (Nat.add g q));
    ih p a kb0 kb1 d kb2 f g kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 s kb11 kb12 kb13 kb14 kb15 kb16 kb17 A kb18 C kb19 E kb20 G kb21 kb22 kb23 kb24 kb25 kb26 N kb27 P kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def ssplit14 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add B C) 1) (bcutL BND 64 B C) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub t q);
  let ka1 := nmin d (Nat.sub q H);
  let ka2 := nmax e (Nat.sub (Nat.add z H) q);
  let ka3 := nmin f (Nat.sub q (Nat.add c g));
  let ka4 := nmin h (Nat.sub q z);
  let ka5 := nmax i (Nat.sub D q);
  let ka6 := nmax l (Nat.sub F (Nat.add q j));
  let ka7 := nmin m (Nat.sub (Nat.add q S) D);
  let ka8 := nmax n (Nat.sub (Nat.add c t) q);
  let ka9 := nmin o (Nat.sub (Nat.add b q) H);
  let ka10 := nmax r (Nat.sub (Nat.add z t) q);
  let ka11 := nmin s (Nat.sub (Nat.add b q) g);
  let ka12 := nmin u (Nat.add b q);
  let ka13 := nmax v (Nat.sub (Nat.add D t) q);
  let ka14 := nmin w (Nat.add (Nat.add b q) j);
  let ka15 := nmax x (Nat.sub (Nat.add F t) q);
  let ka16 := nmin y (Nat.add (Nat.add b q) S);
  let ka17 := nmin A (Nat.sub q g);
  let ka18 := nmin q q;
  let ka19 := nmin E (Nat.add q j);
  let ka20 := nmin G (Nat.add q S);
  let ka21 := nmin I (Nat.sub q c);
  let ka22 := nmax J (Nat.sub (Nat.add D H) q);
  let ka23 := nmin K (Nat.sub (Nat.add q j) c);
  let ka24 := nmax L (Nat.sub (Nat.add F H) q);
  let ka25 := nmin M (Nat.sub (Nat.add q S) c);
  let ka26 := nmax N (Nat.sub (Nat.add D g) q);
  let ka27 := nmin O (Nat.sub (Nat.add q j) z);
  let ka28 := nmax P (Nat.sub (Nat.add F g) q);
  let ka29 := nmin Q (Nat.sub (Nat.add q S) z);
  let ka30 := nmax R (Nat.sub F q);
  let p := ih pos ka0 b c ka1 ka2 ka3 g ka4 ka5 j ka6 ka7 ka8 ka9 ka10 ka11 t ka12 ka13 ka14 ka15 ka16 z ka17 B ka18 D ka19 F ka20 H ka21 ka22 ka23 ka24 ka25 ka26 ka27 ka28 ka29 ka30 S T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub u q);
    let kb1 := nmax c (Nat.sub q I);
    let kb2 := nmax e (Nat.sub q (Nat.add h d));
    let kb3 := nmin f (Nat.sub (Nat.add I A) q);
    let kb4 := nmax g (Nat.sub q A);
    let kb5 := nmin j (Nat.sub E q);
    let kb6 := nmax l (Nat.sub (Nat.add R q) E);
    let kb7 := nmin m (Nat.sub G (Nat.add i q));
    let kb8 := nmax n (Nat.sub (Nat.add q a) I);
    let kb9 := nmin o (Nat.sub (Nat.add u d) q);
    let kb10 := nmax r (Nat.sub (Nat.add q a) h);
    let kb11 := nmin s (Nat.sub (Nat.add u A) q);
    let kb12 := nmax t (Nat.add q a);
    let kb13 := nmax v (Nat.add (Nat.add i q) a);
    let kb14 := nmin w (Nat.sub (Nat.add u E) q);
    let kb15 := nmax x (Nat.add (Nat.add R q) a);
    let kb16 := nmin y (Nat.sub (Nat.add u G) q);
    let kb17 := nmax z (Nat.sub q h);
    let kb18 := nmax q q;
    let kb19 := nmax D (Nat.add i q);
    let kb20 := nmax F (Nat.add R q);
    let kb21 := nmax H (Nat.sub q d);
    let kb22 := nmax J (Nat.sub (Nat.add i q) d);
    let kb23 := nmin K (Nat.sub (Nat.add I E) q);
    let kb24 := nmax L (Nat.sub (Nat.add R q) d);
    let kb25 := nmin M (Nat.sub (Nat.add I G) q);
    let kb26 := nmax N (Nat.sub (Nat.add i q) A);
    let kb27 := nmin O (Nat.sub (Nat.add h E) q);
    let kb28 := nmax P (Nat.sub (Nat.add R q) A);
    let kb29 := nmin Q (Nat.sub (Nat.add h G) q);
    let kb30 := nmin S (Nat.sub G q);
    ih p a kb0 kb1 d kb2 kb3 kb4 h i kb5 kb6 kb7 kb8 kb9 kb10 kb11 kb12 u kb13 kb14 kb15 kb16 kb17 A kb18 C kb19 E kb20 G kb21 I kb22 kb23 kb24 kb25 kb26 kb27 kb28 kb29 R kb30 T) 0 (Nat.beq p 0)

def ssplit15 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add D E) 1) (bcutL BND 64 D E) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub v q);
  let ka1 := nmin d (Nat.sub q J);
  let ka2 := nmax e (Nat.sub (Nat.add z J) q);
  let ka3 := nmin f (Nat.sub q (Nat.add c N));
  let ka4 := nmax g (Nat.sub (Nat.add B N) q);
  let ka5 := nmin h (Nat.sub q (Nat.add z i));
  let ka6 := nmin j (Nat.sub q B);
  let ka7 := nmax l (Nat.sub F q);
  let ka8 := nmax n (Nat.sub (Nat.add c v) q);
  let ka9 := nmin o (Nat.sub (Nat.add b q) J);
  let ka10 := nmax r (Nat.sub (Nat.add z v) q);
  let ka11 := nmin s (Nat.sub (Nat.add b q) N);
  let ka12 := nmax t (Nat.sub (Nat.add B v) q);
  let ka13 := nmin u (Nat.sub (Nat.add b q) i);
  let ka14 := nmin w (Nat.add b q);
  let ka15 := nmax x (Nat.sub (Nat.add F v) q);
  let ka16 := nmin y (Nat.add (Nat.add b q) m);
  let ka17 := nmin A (Nat.sub q N);
  let ka18 := nmin C (Nat.sub q i);
  let ka19 := nmin q q;
  let ka20 := nmin G (Nat.add q m);
  let ka21 := nmax H (Nat.sub (Nat.add B J) q);
  let ka22 := nmin I (Nat.sub q (Nat.add c i));
  let ka23 := nmin K (Nat.sub q c);
  let ka24 := nmax L (Nat.sub (Nat.add F J) q);
  let ka25 := nmin M (Nat.sub (Nat.add q m) c);
  let ka26 := nmin O (Nat.sub q z);
  let ka27 := nmax P (Nat.sub (Nat.add F N) q);
  let ka28 := nmin Q (Nat.sub (Nat.add q m) z);
  let ka29 := nmax R (Nat.sub (Nat.add F i) q);
  let ka30 := nmin S (Nat.sub (Nat.add q m) B);
  let p := ih pos ka0 b c ka1 ka2 ka3 ka4 ka5 i ka6 ka7 m ka8 ka9 ka10 ka11 ka12 ka13 v ka14 ka15 ka16 z ka17 B ka18 D ka19 F ka20 ka21 ka22 J ka23 ka24 ka25 N ka26 ka27 ka28 ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub w q);
    let kb1 := nmax c (Nat.sub q K);
    let kb2 := nmax e (Nat.sub q (Nat.add O d));
    let kb3 := nmin f (Nat.sub (Nat.add K A) q);
    let kb4 := nmax g (Nat.sub q (Nat.add j A));
    let kb5 := nmin h (Nat.sub (Nat.add O C) q);
    let kb6 := nmax i (Nat.sub q C);
    let kb7 := nmin m (Nat.sub G q);
    let kb8 := nmax n (Nat.sub (Nat.add q a) K);
    let kb9 := nmin o (Nat.sub (Nat.add w d) q);
    let kb10 := nmax r (Nat.sub (Nat.add q a) O);
    let kb11 := nmin s (Nat.sub (Nat.add w A) q);
    let kb12 := nmax t (Nat.sub (Nat.add q a) j);
    let kb13 := nmin u (Nat.sub (Nat.add w C) q);
    let kb14 := nmax v (Nat.add q a);
    let kb15 := nmax x (Nat.add (Nat.add l q) a);
    let kb16 := nmin y (Nat.sub (Nat.add w G) q);
    let kb17 := nmax z (Nat.sub q O);
    let kb18 := nmax B (Nat.sub q j);
    let kb19 := nmax q q;
    let kb20 := nmax F (Nat.add l q);
    let kb21 := nmax H (Nat.sub q (Nat.add j d));
    let kb22 := nmin I (Nat.sub (Nat.add K C) q);
    let kb23 := nmax J (Nat.sub q d);
    let kb24 := nmax L (Nat.sub (Nat.add l q) d);
    let kb25 := nmin M (Nat.sub (Nat.add K G) q);
    let kb26 := nmax N (Nat.sub q A);
    let kb27 := nmax P (Nat.sub (Nat.add l q) A);
    let kb28 := nmin Q (Nat.sub (Nat.add O G) q);
    let kb29 := nmax R (Nat.sub (Nat.add l q) C);
    let kb30 := nmin S (Nat.sub (Nat.add j G) q);
    ih p a kb0 kb1 d kb2 kb3 kb4 kb5 kb6 j l kb7 kb8 kb9 kb10 kb11 kb12 kb13 kb14 w kb15 kb16 kb17 A kb18 C kb19 E kb20 G kb21 kb22 kb23 K kb24 kb25 kb26 O kb27 kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def ssplit16 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add F G) 1) (bcutL BND 64 F G) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub x q);
  let ka1 := nmin d (Nat.sub q L);
  let ka2 := nmax e (Nat.sub (Nat.add z L) q);
  let ka3 := nmin f (Nat.sub q (Nat.add c P));
  let ka4 := nmax g (Nat.sub (Nat.add B P) q);
  let ka5 := nmin h (Nat.sub q (Nat.add z R));
  let ka6 := nmax i (Nat.sub (Nat.add D R) q);
  let ka7 := nmin j (Nat.sub q (Nat.add B l));
  let ka8 := nmin m (Nat.sub q D);
  let ka9 := nmax n (Nat.sub (Nat.add c x) q);
  let ka10 := nmin o (Nat.sub (Nat.add b q) L);
  let ka11 := nmax r (Nat.sub (Nat.add z x) q);
  let ka12 := nmin s (Nat.sub (Nat.add b q) P);
  let ka13 := nmax t (Nat.sub (Nat.add B x) q);
  let ka14 := nmin u (Nat.sub (Nat.add b q) R);
  let ka15 := nmax v (Nat.sub (Nat.add D x) q);
  let ka16 := nmin w (Nat.sub (Nat.add b q) l);
  let ka17 := nmin y (Nat.add b q);
  let ka18 := nmin A (Nat.sub q P);
  let ka19 := nmin C (Nat.sub q R);
  let ka20 := nmin E (Nat.sub q l);
  let ka21 := nmin q q;
  let ka22 := nmax H (Nat.sub (Nat.add B L) q);
  let ka23 := nmin I (Nat.sub q (Nat.add c R));
  let ka24 := nmax J (Nat.sub (Nat.add D L) q);
  let ka25 := nmin K (Nat.sub q (Nat.add c l));
  let ka26 := nmin M (Nat.sub q c);
  let ka27 := nmax N (Nat.sub (Nat.add D P) q);
  let ka28 := nmin O (Nat.sub q (Nat.add z l));
  let ka29 := nmin Q (Nat.sub q z);
  let ka30 := nmin S (Nat.sub q B);
  let p := ih pos ka0 b c ka1 ka2 ka3 ka4 ka5 ka6 ka7 l ka8 ka9 ka10 ka11 ka12 ka13 ka14 ka15 ka16 x ka17 z ka18 B ka19 D ka20 F ka21 ka22 ka23 ka24 ka25 L ka26 ka27 ka28 P ka29 R ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub y q);
    let kb1 := nmax c (Nat.sub q M);
    let kb2 := nmax e (Nat.sub q (Nat.add Q d));
    let kb3 := nmin f (Nat.sub (Nat.add M A) q);
    let kb4 := nmax g (Nat.sub q (Nat.add S A));
    let kb5 := nmin h (Nat.sub (Nat.add Q C) q);
    let kb6 := nmax i (Nat.sub q (Nat.add m C));
    let kb7 := nmin j (Nat.sub (Nat.add S E) q);
    let kb8 := nmax l (Nat.sub q E);
    let kb9 := nmax n (Nat.sub (Nat.add q a) M);
    let kb10 := nmin o (Nat.sub (Nat.add y d) q);
    let kb11 := nmax r (Nat.sub (Nat.add q a) Q);
    let kb12 := nmin s (Nat.sub (Nat.add y A) q);
    let kb13 := nmax t (Nat.sub (Nat.add q a) S);
    let kb14 := nmin u (Nat.sub (Nat.add y C) q);
    let kb15 := nmax v (Nat.sub (Nat.add q a) m);
    let kb16 := nmin w (Nat.sub (Nat.add y E) q);
    let kb17 := nmax x (Nat.add q a);
    let kb18 := nmax z (Nat.sub q Q);
    let kb19 := nmax B (Nat.sub q S);
    let kb20 := nmax D (Nat.sub q m);
    let kb21 := nmax q q;
    let kb22 := nmax H (Nat.sub q (Nat.add S d));
    let kb23 := nmin I (Nat.sub (Nat.add M C) q);
    let kb24 := nmax J (Nat.sub q (Nat.add m d));
    let kb25 := nmin K (Nat.sub (Nat.add M E) q);
    let kb26 := nmax L (Nat.sub q d);
    let kb27 := nmax N (Nat.sub q (Nat.add m A));
    let kb28 := nmin O (Nat.sub (Nat.add Q E) q);
    let kb29 := nmax P (Nat.sub q A);
    let kb30 := nmax R (Nat.sub q C);
    ih p a kb0 kb1 d kb2 kb3 kb4 kb5 kb6 kb7 kb8 m kb9 kb10 kb11 kb12 kb13 kb14 kb15 kb16 kb17 y kb18 A kb19 C kb20 E kb21 G kb22 kb23 kb24 kb25 kb26 M kb27 kb28 kb29 Q kb30 S T) 0 (Nat.beq p 0)

def ssplit24 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add H I) 1) (bcutL BND 64 H I) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub t (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add o q) B);
  let ka2 := nmax c (Nat.sub B q);
  let ka3 := nmin f (Nat.sub q g);
  let ka4 := nmin h (Nat.sub q e);
  let ka5 := nmax i (Nat.sub J q);
  let ka6 := nmax l (Nat.sub L (Nat.add q j));
  let ka7 := nmin m (Nat.sub (Nat.add q S) J);
  let ka8 := nmax n (Nat.sub t q);
  let ka9 := nmax r (Nat.sub (Nat.add e t) q);
  let ka10 := nmin s (Nat.sub (Nat.add o q) g);
  let ka11 := nmin u (Nat.add o q);
  let ka12 := nmax v (Nat.sub (Nat.add J t) q);
  let ka13 := nmin w (Nat.add (Nat.add o q) j);
  let ka14 := nmax x (Nat.sub (Nat.add L t) q);
  let ka15 := nmin y (Nat.add (Nat.add o q) S);
  let ka16 := nmax z (Nat.sub (Nat.add e B) q);
  let ka17 := nmin A (Nat.sub (Nat.add d q) g);
  let ka18 := nmin C (Nat.add d q);
  let ka19 := nmax D (Nat.sub (Nat.add J B) q);
  let ka20 := nmin E (Nat.add (Nat.add d q) j);
  let ka21 := nmax F (Nat.sub (Nat.add L B) q);
  let ka22 := nmin G (Nat.add (Nat.add d q) S);
  let ka23 := nmin q q;
  let ka24 := nmin K (Nat.add q j);
  let ka25 := nmin M (Nat.add q S);
  let ka26 := nmax N (Nat.sub (Nat.add J g) q);
  let ka27 := nmin O (Nat.sub (Nat.add q j) e);
  let ka28 := nmax P (Nat.sub (Nat.add L g) q);
  let ka29 := nmin Q (Nat.sub (Nat.add q S) e);
  let ka30 := nmax R (Nat.sub L q);
  let p := ih pos ka0 ka1 ka2 d e ka3 g ka4 ka5 j ka6 ka7 ka8 o ka9 ka10 t ka11 ka12 ka13 ka14 ka15 ka16 ka17 B ka18 ka19 ka20 ka21 ka22 H ka23 J ka24 L ka25 ka26 ka27 ka28 ka29 ka30 S T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q n) C);
    let kb1 := nmin b (Nat.sub u (Nat.add q c));
    let kb2 := nmin d (Nat.sub C q);
    let kb3 := nmax e (Nat.sub q h);
    let kb4 := nmax g (Nat.sub q f);
    let kb5 := nmin j (Nat.sub K q);
    let kb6 := nmax l (Nat.sub (Nat.add R q) K);
    let kb7 := nmin m (Nat.sub M (Nat.add i q));
    let kb8 := nmin o (Nat.sub u q);
    let kb9 := nmax r (Nat.sub (Nat.add q n) h);
    let kb10 := nmin s (Nat.sub (Nat.add u f) q);
    let kb11 := nmax t (Nat.add q n);
    let kb12 := nmax v (Nat.add (Nat.add i q) n);
    let kb13 := nmin w (Nat.sub (Nat.add u K) q);
    let kb14 := nmax x (Nat.add (Nat.add R q) n);
    let kb15 := nmin y (Nat.sub (Nat.add u M) q);
    let kb16 := nmax z (Nat.sub (Nat.add q c) h);
    let kb17 := nmin A (Nat.sub (Nat.add C f) q);
    let kb18 := nmax B (Nat.add q c);
    let kb19 := nmax D (Nat.add (Nat.add i q) c);
    let kb20 := nmin E (Nat.sub (Nat.add C K) q);
    let kb21 := nmax F (Nat.add (Nat.add R q) c);
    let kb22 := nmin G (Nat.sub (Nat.add C M) q);
    let kb23 := nmax q q;
    let kb24 := nmax J (Nat.add i q);
    let kb25 := nmax L (Nat.add R q);
    let kb26 := nmax N (Nat.sub (Nat.add i q) f);
    let kb27 := nmin O (Nat.sub (Nat.add h K) q);
    let kb28 := nmax P (Nat.sub (Nat.add R q) f);
    let kb29 := nmin Q (Nat.sub (Nat.add h M) q);
    let kb30 := nmin S (Nat.sub M q);
    ih p kb0 kb1 c kb2 kb3 f kb4 h i kb5 kb6 kb7 n kb8 kb9 kb10 kb11 u kb12 kb13 kb14 kb15 kb16 kb17 kb18 C kb19 kb20 kb21 kb22 kb23 I kb24 K kb25 M kb26 kb27 kb28 kb29 R kb30 T) 0 (Nat.beq p 0)

def ssplit25 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add J K) 1) (bcutL BND 64 J K) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub v (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add o q) D);
  let ka2 := nmax c (Nat.sub D q);
  let ka3 := nmin f (Nat.sub q N);
  let ka4 := nmax g (Nat.sub (Nat.add H N) q);
  let ka5 := nmin h (Nat.sub q (Nat.add e i));
  let ka6 := nmin j (Nat.sub q H);
  let ka7 := nmax l (Nat.sub L q);
  let ka8 := nmax n (Nat.sub v q);
  let ka9 := nmax r (Nat.sub (Nat.add e v) q);
  let ka10 := nmin s (Nat.sub (Nat.add o q) N);
  let ka11 := nmax t (Nat.sub (Nat.add H v) q);
  let ka12 := nmin u (Nat.sub (Nat.add o q) i);
  let ka13 := nmin w (Nat.add o q);
  let ka14 := nmax x (Nat.sub (Nat.add L v) q);
  let ka15 := nmin y (Nat.add (Nat.add o q) m);
  let ka16 := nmax z (Nat.sub (Nat.add e D) q);
  let ka17 := nmin A (Nat.sub (Nat.add d q) N);
  let ka18 := nmax B (Nat.sub (Nat.add H D) q);
  let ka19 := nmin C (Nat.sub (Nat.add d q) i);
  let ka20 := nmin E (Nat.add d q);
  let ka21 := nmax F (Nat.sub (Nat.add L D) q);
  let ka22 := nmin G (Nat.add (Nat.add d q) m);
  let ka23 := nmin I (Nat.sub q i);
  let ka24 := nmin q q;
  let ka25 := nmin M (Nat.add q m);
  let ka26 := nmin O (Nat.sub q e);
  let ka27 := nmax P (Nat.sub (Nat.add L N) q);
  let ka28 := nmin Q (Nat.sub (Nat.add q m) e);
  let ka29 := nmax R (Nat.sub (Nat.add L i) q);
  let ka30 := nmin S (Nat.sub (Nat.add q m) H);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 ka5 i ka6 ka7 m ka8 o ka9 ka10 ka11 ka12 v ka13 ka14 ka15 ka16 ka17 ka18 ka19 D ka20 ka21 ka22 H ka23 J ka24 L ka25 N ka26 ka27 ka28 ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q n) E);
    let kb1 := nmin b (Nat.sub w (Nat.add q c));
    let kb2 := nmin d (Nat.sub E q);
    let kb3 := nmax e (Nat.sub q O);
    let kb4 := nmax g (Nat.sub q (Nat.add j f));
    let kb5 := nmin h (Nat.sub (Nat.add O I) q);
    let kb6 := nmax i (Nat.sub q I);
    let kb7 := nmin m (Nat.sub M q);
    let kb8 := nmin o (Nat.sub w q);
    let kb9 := nmax r (Nat.sub (Nat.add q n) O);
    let kb10 := nmin s (Nat.sub (Nat.add w f) q);
    let kb11 := nmax t (Nat.sub (Nat.add q n) j);
    let kb12 := nmin u (Nat.sub (Nat.add w I) q);
    let kb13 := nmax v (Nat.add q n);
    let kb14 := nmax x (Nat.add (Nat.add l q) n);
    let kb15 := nmin y (Nat.sub (Nat.add w M) q);
    let kb16 := nmax z (Nat.sub (Nat.add q c) O);
    let kb17 := nmin A (Nat.sub (Nat.add E f) q);
    let kb18 := nmax B (Nat.sub (Nat.add q c) j);
    let kb19 := nmin C (Nat.sub (Nat.add E I) q);
    let kb20 := nmax D (Nat.add q c);
    let kb21 := nmax F (Nat.add (Nat.add l q) c);
    let kb22 := nmin G (Nat.sub (Nat.add E M) q);
    let kb23 := nmax H (Nat.sub q j);
    let kb24 := nmax q q;
    let kb25 := nmax L (Nat.add l q);
    let kb26 := nmax N (Nat.sub q f);
    let kb27 := nmax P (Nat.sub (Nat.add l q) f);
    let kb28 := nmin Q (Nat.sub (Nat.add O M) q);
    let kb29 := nmax R (Nat.sub (Nat.add l q) I);
    let kb30 := nmin S (Nat.sub (Nat.add j M) q);
    ih p kb0 kb1 c kb2 kb3 f kb4 kb5 kb6 j l kb7 n kb8 kb9 kb10 kb11 kb12 kb13 w kb14 kb15 kb16 kb17 kb18 kb19 kb20 E kb21 kb22 kb23 I kb24 K kb25 M kb26 O kb27 kb28 kb29 kb30 T) 0 (Nat.beq p 0)

def ssplit26 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add L M) 1) (bcutL BND 64 L M) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub x (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add o q) F);
  let ka2 := nmax c (Nat.sub F q);
  let ka3 := nmin f (Nat.sub q P);
  let ka4 := nmax g (Nat.sub (Nat.add H P) q);
  let ka5 := nmin h (Nat.sub q (Nat.add e R));
  let ka6 := nmax i (Nat.sub (Nat.add J R) q);
  let ka7 := nmin j (Nat.sub q (Nat.add H l));
  let ka8 := nmin m (Nat.sub q J);
  let ka9 := nmax n (Nat.sub x q);
  let ka10 := nmax r (Nat.sub (Nat.add e x) q);
  let ka11 := nmin s (Nat.sub (Nat.add o q) P);
  let ka12 := nmax t (Nat.sub (Nat.add H x) q);
  let ka13 := nmin u (Nat.sub (Nat.add o q) R);
  let ka14 := nmax v (Nat.sub (Nat.add J x) q);
  let ka15 := nmin w (Nat.sub (Nat.add o q) l);
  let ka16 := nmin y (Nat.add o q);
  let ka17 := nmax z (Nat.sub (Nat.add e F) q);
  let ka18 := nmin A (Nat.sub (Nat.add d q) P);
  let ka19 := nmax B (Nat.sub (Nat.add H F) q);
  let ka20 := nmin C (Nat.sub (Nat.add d q) R);
  let ka21 := nmax D (Nat.sub (Nat.add J F) q);
  let ka22 := nmin E (Nat.sub (Nat.add d q) l);
  let ka23 := nmin G (Nat.add d q);
  let ka24 := nmin I (Nat.sub q R);
  let ka25 := nmin K (Nat.sub q l);
  let ka26 := nmin q q;
  let ka27 := nmax N (Nat.sub (Nat.add J P) q);
  let ka28 := nmin O (Nat.sub q (Nat.add e l));
  let ka29 := nmin Q (Nat.sub q e);
  let ka30 := nmin S (Nat.sub q H);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 ka5 ka6 ka7 l ka8 ka9 o ka10 ka11 ka12 ka13 ka14 ka15 x ka16 ka17 ka18 ka19 ka20 ka21 ka22 F ka23 H ka24 J ka25 L ka26 ka27 ka28 P ka29 R ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q n) G);
    let kb1 := nmin b (Nat.sub y (Nat.add q c));
    let kb2 := nmin d (Nat.sub G q);
    let kb3 := nmax e (Nat.sub q Q);
    let kb4 := nmax g (Nat.sub q (Nat.add S f));
    let kb5 := nmin h (Nat.sub (Nat.add Q I) q);
    let kb6 := nmax i (Nat.sub q (Nat.add m I));
    let kb7 := nmin j (Nat.sub (Nat.add S K) q);
    let kb8 := nmax l (Nat.sub q K);
    let kb9 := nmin o (Nat.sub y q);
    let kb10 := nmax r (Nat.sub (Nat.add q n) Q);
    let kb11 := nmin s (Nat.sub (Nat.add y f) q);
    let kb12 := nmax t (Nat.sub (Nat.add q n) S);
    let kb13 := nmin u (Nat.sub (Nat.add y I) q);
    let kb14 := nmax v (Nat.sub (Nat.add q n) m);
    let kb15 := nmin w (Nat.sub (Nat.add y K) q);
    let kb16 := nmax x (Nat.add q n);
    let kb17 := nmax z (Nat.sub (Nat.add q c) Q);
    let kb18 := nmin A (Nat.sub (Nat.add G f) q);
    let kb19 := nmax B (Nat.sub (Nat.add q c) S);
    let kb20 := nmin C (Nat.sub (Nat.add G I) q);
    let kb21 := nmax D (Nat.sub (Nat.add q c) m);
    let kb22 := nmin E (Nat.sub (Nat.add G K) q);
    let kb23 := nmax F (Nat.add q c);
    let kb24 := nmax H (Nat.sub q S);
    let kb25 := nmax J (Nat.sub q m);
    let kb26 := nmax q q;
    let kb27 := nmax N (Nat.sub q (Nat.add m f));
    let kb28 := nmin O (Nat.sub (Nat.add Q K) q);
    let kb29 := nmax P (Nat.sub q f);
    let kb30 := nmax R (Nat.sub q I);
    ih p kb0 kb1 c kb2 kb3 f kb4 kb5 kb6 kb7 kb8 m n kb9 kb10 kb11 kb12 kb13 kb14 kb15 kb16 y kb17 kb18 kb19 kb20 kb21 kb22 kb23 G kb24 I kb25 K kb26 M kb27 kb28 kb29 Q kb30 S T) 0 (Nat.beq p 0)

def ssplit35 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add N O) 1) (bcutL BND 64 N O) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub v (Nat.add A q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) D);
  let ka2 := nmax c (Nat.sub D (Nat.add f q));
  let ka3 := nmin d (Nat.sub (Nat.add A q) J);
  let ka4 := nmax e (Nat.sub J q);
  let ka5 := nmin h (Nat.sub q i);
  let ka6 := nmin j (Nat.sub q g);
  let ka7 := nmax l (Nat.sub P q);
  let ka8 := nmax n (Nat.sub v (Nat.add f q));
  let ka9 := nmin o (Nat.sub (Nat.add s q) J);
  let ka10 := nmax r (Nat.sub v q);
  let ka11 := nmax t (Nat.sub (Nat.add g v) q);
  let ka12 := nmin u (Nat.sub (Nat.add s q) i);
  let ka13 := nmin w (Nat.add s q);
  let ka14 := nmax x (Nat.sub (Nat.add P v) q);
  let ka15 := nmin y (Nat.add (Nat.add s q) m);
  let ka16 := nmax z (Nat.sub D q);
  let ka17 := nmax B (Nat.sub (Nat.add g D) q);
  let ka18 := nmin C (Nat.sub (Nat.add A q) i);
  let ka19 := nmin E (Nat.add A q);
  let ka20 := nmax F (Nat.sub (Nat.add P D) q);
  let ka21 := nmin G (Nat.add (Nat.add A q) m);
  let ka22 := nmax H (Nat.sub (Nat.add g J) q);
  let ka23 := nmin I (Nat.sub (Nat.add f q) i);
  let ka24 := nmin K (Nat.add f q);
  let ka25 := nmax L (Nat.sub (Nat.add P J) q);
  let ka26 := nmin M (Nat.add (Nat.add f q) m);
  let ka27 := nmin q q;
  let ka28 := nmin Q (Nat.add q m);
  let ka29 := nmax R (Nat.sub (Nat.add P i) q);
  let ka30 := nmin S (Nat.sub (Nat.add q m) g);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 f g ka5 i ka6 ka7 m ka8 ka9 ka10 s ka11 ka12 v ka13 ka14 ka15 ka16 A ka17 ka18 D ka19 ka20 ka21 ka22 ka23 J ka24 ka25 ka26 N ka27 P ka28 ka29 ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) E);
    let kb1 := nmin b (Nat.sub w (Nat.add q z));
    let kb2 := nmax c (Nat.sub (Nat.add q z) K);
    let kb3 := nmin d (Nat.sub E (Nat.add q e));
    let kb4 := nmin f (Nat.sub K q);
    let kb5 := nmax g (Nat.sub q j);
    let kb6 := nmax i (Nat.sub q h);
    let kb7 := nmin m (Nat.sub Q q);
    let kb8 := nmax n (Nat.sub (Nat.add q r) K);
    let kb9 := nmin o (Nat.sub w (Nat.add q e));
    let kb10 := nmin s (Nat.sub w q);
    let kb11 := nmax t (Nat.sub (Nat.add q r) j);
    let kb12 := nmin u (Nat.sub (Nat.add w h) q);
    let kb13 := nmax v (Nat.add q r);
    let kb14 := nmax x (Nat.add (Nat.add l q) r);
    let kb15 := nmin y (Nat.sub (Nat.add w Q) q);
    let kb16 := nmin A (Nat.sub E q);
    let kb17 := nmax B (Nat.sub (Nat.add q z) j);
    let kb18 := nmin C (Nat.sub (Nat.add E h) q);
    let kb19 := nmax D (Nat.add q z);
    let kb20 := nmax F (Nat.add (Nat.add l q) z);
    let kb21 := nmin G (Nat.sub (Nat.add E Q) q);
    let kb22 := nmax H (Nat.sub (Nat.add q e) j);
    let kb23 := nmin I (Nat.sub (Nat.add K h) q);
    let kb24 := nmax J (Nat.add q e);
    let kb25 := nmax L (Nat.add (Nat.add l q) e);
    let kb26 := nmin M (Nat.sub (Nat.add K Q) q);
    let kb27 := nmax q q;
    let kb28 := nmax P (Nat.add l q);
    let kb29 := nmax R (Nat.sub (Nat.add l q) h);
    let kb30 := nmin S (Nat.sub (Nat.add j Q) q);
    ih p kb0 kb1 kb2 kb3 e kb4 kb5 h kb6 j l kb7 kb8 kb9 r kb10 kb11 kb12 kb13 w kb14 kb15 z kb16 kb17 kb18 kb19 E kb20 kb21 kb22 kb23 kb24 K kb25 kb26 kb27 O kb28 Q kb29 kb30 T) 0 (Nat.beq p 0)

def ssplit36 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add P Q) 1) (bcutL BND 64 P Q) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub x (Nat.add A q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) F);
  let ka2 := nmax c (Nat.sub F (Nat.add f q));
  let ka3 := nmin d (Nat.sub (Nat.add A q) L);
  let ka4 := nmax e (Nat.sub L q);
  let ka5 := nmin h (Nat.sub q R);
  let ka6 := nmax i (Nat.sub (Nat.add N R) q);
  let ka7 := nmin j (Nat.sub q (Nat.add g l));
  let ka8 := nmin m (Nat.sub q N);
  let ka9 := nmax n (Nat.sub x (Nat.add f q));
  let ka10 := nmin o (Nat.sub (Nat.add s q) L);
  let ka11 := nmax r (Nat.sub x q);
  let ka12 := nmax t (Nat.sub (Nat.add g x) q);
  let ka13 := nmin u (Nat.sub (Nat.add s q) R);
  let ka14 := nmax v (Nat.sub (Nat.add N x) q);
  let ka15 := nmin w (Nat.sub (Nat.add s q) l);
  let ka16 := nmin y (Nat.add s q);
  let ka17 := nmax z (Nat.sub F q);
  let ka18 := nmax B (Nat.sub (Nat.add g F) q);
  let ka19 := nmin C (Nat.sub (Nat.add A q) R);
  let ka20 := nmax D (Nat.sub (Nat.add N F) q);
  let ka21 := nmin E (Nat.sub (Nat.add A q) l);
  let ka22 := nmin G (Nat.add A q);
  let ka23 := nmax H (Nat.sub (Nat.add g L) q);
  let ka24 := nmin I (Nat.sub (Nat.add f q) R);
  let ka25 := nmax J (Nat.sub (Nat.add N L) q);
  let ka26 := nmin K (Nat.sub (Nat.add f q) l);
  let ka27 := nmin M (Nat.add f q);
  let ka28 := nmin O (Nat.sub q l);
  let ka29 := nmin q q;
  let ka30 := nmin S (Nat.sub q g);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 f g ka5 ka6 ka7 l ka8 ka9 ka10 ka11 s ka12 ka13 ka14 ka15 x ka16 ka17 A ka18 ka19 ka20 ka21 F ka22 ka23 ka24 ka25 ka26 L ka27 N ka28 P ka29 R ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) G);
    let kb1 := nmin b (Nat.sub y (Nat.add q z));
    let kb2 := nmax c (Nat.sub (Nat.add q z) M);
    let kb3 := nmin d (Nat.sub G (Nat.add q e));
    let kb4 := nmin f (Nat.sub M q);
    let kb5 := nmax g (Nat.sub q S);
    let kb6 := nmax i (Nat.sub q (Nat.add m h));
    let kb7 := nmin j (Nat.sub (Nat.add S O) q);
    let kb8 := nmax l (Nat.sub q O);
    let kb9 := nmax n (Nat.sub (Nat.add q r) M);
    let kb10 := nmin o (Nat.sub y (Nat.add q e));
    let kb11 := nmin s (Nat.sub y q);
    let kb12 := nmax t (Nat.sub (Nat.add q r) S);
    let kb13 := nmin u (Nat.sub (Nat.add y h) q);
    let kb14 := nmax v (Nat.sub (Nat.add q r) m);
    let kb15 := nmin w (Nat.sub (Nat.add y O) q);
    let kb16 := nmax x (Nat.add q r);
    let kb17 := nmin A (Nat.sub G q);
    let kb18 := nmax B (Nat.sub (Nat.add q z) S);
    let kb19 := nmin C (Nat.sub (Nat.add G h) q);
    let kb20 := nmax D (Nat.sub (Nat.add q z) m);
    let kb21 := nmin E (Nat.sub (Nat.add G O) q);
    let kb22 := nmax F (Nat.add q z);
    let kb23 := nmax H (Nat.sub (Nat.add q e) S);
    let kb24 := nmin I (Nat.sub (Nat.add M h) q);
    let kb25 := nmax J (Nat.sub (Nat.add q e) m);
    let kb26 := nmin K (Nat.sub (Nat.add M O) q);
    let kb27 := nmax L (Nat.add q e);
    let kb28 := nmax N (Nat.sub q m);
    let kb29 := nmax q q;
    let kb30 := nmax R (Nat.sub q h);
    ih p kb0 kb1 kb2 kb3 e kb4 kb5 h kb6 kb7 kb8 m kb9 kb10 r kb11 kb12 kb13 kb14 kb15 kb16 y z kb17 kb18 kb19 kb20 kb21 kb22 G kb23 kb24 kb25 kb26 kb27 M kb28 O kb29 Q kb30 S T) 0 (Nat.beq p 0)

def ssplit46 (ih : WF) (md pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  let q := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add R S) 1) (bcutL BND 64 R S) (Nat.beq md 1);
  let ka0 := nmax a (Nat.sub x (Nat.add C q));
  let ka1 := nmin b (Nat.sub (Nat.add u q) F);
  let ka2 := nmax c (Nat.sub F (Nat.add I q));
  let ka3 := nmin d (Nat.sub (Nat.add C q) L);
  let ka4 := nmax e (Nat.sub L (Nat.add h q));
  let ka5 := nmin f (Nat.sub (Nat.add I q) P);
  let ka6 := nmax g (Nat.sub P q);
  let ka7 := nmin j (Nat.sub q l);
  let ka8 := nmin m (Nat.sub q i);
  let ka9 := nmax n (Nat.sub x (Nat.add I q));
  let ka10 := nmin o (Nat.sub (Nat.add u q) L);
  let ka11 := nmax r (Nat.sub x (Nat.add h q));
  let ka12 := nmin s (Nat.sub (Nat.add u q) P);
  let ka13 := nmax t (Nat.sub x q);
  let ka14 := nmax v (Nat.sub (Nat.add i x) q);
  let ka15 := nmin w (Nat.sub (Nat.add u q) l);
  let ka16 := nmin y (Nat.add u q);
  let ka17 := nmax z (Nat.sub F (Nat.add h q));
  let ka18 := nmin A (Nat.sub (Nat.add C q) P);
  let ka19 := nmax B (Nat.sub F q);
  let ka20 := nmax D (Nat.sub (Nat.add i F) q);
  let ka21 := nmin E (Nat.sub (Nat.add C q) l);
  let ka22 := nmin G (Nat.add C q);
  let ka23 := nmax H (Nat.sub L q);
  let ka24 := nmax J (Nat.sub (Nat.add i L) q);
  let ka25 := nmin K (Nat.sub (Nat.add I q) l);
  let ka26 := nmin M (Nat.add I q);
  let ka27 := nmax N (Nat.sub (Nat.add i P) q);
  let ka28 := nmin O (Nat.sub (Nat.add h q) l);
  let ka29 := nmin Q (Nat.add h q);
  let ka30 := nmin q q;
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 h i ka7 l ka8 ka9 ka10 ka11 ka12 ka13 u ka14 ka15 x ka16 ka17 ka18 ka19 C ka20 ka21 F ka22 ka23 I ka24 ka25 L ka26 ka27 ka28 P ka29 R ka30 T
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q t) G);
    let kb1 := nmin b (Nat.sub y (Nat.add q B));
    let kb2 := nmax c (Nat.sub (Nat.add q B) M);
    let kb3 := nmin d (Nat.sub G (Nat.add q H));
    let kb4 := nmax e (Nat.sub (Nat.add q H) Q);
    let kb5 := nmin f (Nat.sub M (Nat.add q g));
    let kb6 := nmin h (Nat.sub Q q);
    let kb7 := nmax i (Nat.sub q m);
    let kb8 := nmax l (Nat.sub q j);
    let kb9 := nmax n (Nat.sub (Nat.add q t) M);
    let kb10 := nmin o (Nat.sub y (Nat.add q H));
    let kb11 := nmax r (Nat.sub (Nat.add q t) Q);
    let kb12 := nmin s (Nat.sub y (Nat.add q g));
    let kb13 := nmin u (Nat.sub y q);
    let kb14 := nmax v (Nat.sub (Nat.add q t) m);
    let kb15 := nmin w (Nat.sub (Nat.add y j) q);
    let kb16 := nmax x (Nat.add q t);
    let kb17 := nmax z (Nat.sub (Nat.add q B) Q);
    let kb18 := nmin A (Nat.sub G (Nat.add q g));
    let kb19 := nmin C (Nat.sub G q);
    let kb20 := nmax D (Nat.sub (Nat.add q B) m);
    let kb21 := nmin E (Nat.sub (Nat.add G j) q);
    let kb22 := nmax F (Nat.add q B);
    let kb23 := nmin I (Nat.sub M q);
    let kb24 := nmax J (Nat.sub (Nat.add q H) m);
    let kb25 := nmin K (Nat.sub (Nat.add M j) q);
    let kb26 := nmax L (Nat.add q H);
    let kb27 := nmax N (Nat.sub (Nat.add q g) m);
    let kb28 := nmin O (Nat.sub (Nat.add Q j) q);
    let kb29 := nmax P (Nat.add q g);
    let kb30 := nmax q q;
    ih p kb0 kb1 kb2 kb3 kb4 kb5 g kb6 kb7 j kb8 m kb9 kb10 kb11 kb12 t kb13 kb14 kb15 kb16 y kb17 kb18 B kb19 kb20 kb21 kb22 G H kb23 kb24 kb25 kb26 M kb27 kb28 kb29 Q kb30 S T) 0 (Nat.beq p 0)

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
theorem gsplit3_ok : CovK (gsplit3 ih md pos) := pc_spl gsplit3 (cov_gsplitQ hSL hPR 3 (qB BND 64 (toCl s) 3 md) rfl rfl (by decide))
theorem gsplit4_ok : CovK (gsplit4 ih md pos) := pc_spl gsplit4 (cov_gsplitQ hSL hPR 4 (qB BND 64 (toCl s) 4 md) rfl rfl (by decide))
theorem gsplit5_ok : CovK (gsplit5 ih md pos) := pc_spl gsplit5 (cov_gsplitQ hSL hPR 5 (qB BND 64 (toCl s) 5 md) rfl rfl (by decide))
theorem ssplit02_ok : CovK (ssplit02 ih md pos) := pc_spl ssplit02 (cov_ssplitQ hSL hPR 0 (qBr BND 64 (toCl s) 0 md) rfl rfl (by decide))
theorem ssplit03_ok : CovK (ssplit03 ih md pos) := pc_spl ssplit03 (cov_ssplitQ hSL hPR 1 (qBr BND 64 (toCl s) 1 md) rfl rfl (by decide))
theorem ssplit04_ok : CovK (ssplit04 ih md pos) := pc_spl ssplit04 (cov_ssplitQ hSL hPR 2 (qBr BND 64 (toCl s) 2 md) rfl rfl (by decide))
theorem ssplit05_ok : CovK (ssplit05 ih md pos) := pc_spl ssplit05 (cov_ssplitQ hSL hPR 3 (qBr BND 64 (toCl s) 3 md) rfl rfl (by decide))
theorem ssplit06_ok : CovK (ssplit06 ih md pos) := pc_spl ssplit06 (cov_ssplitQ hSL hPR 4 (qBr BND 64 (toCl s) 4 md) rfl rfl (by decide))
theorem ssplit13_ok : CovK (ssplit13 ih md pos) := pc_spl ssplit13 (cov_ssplitQ hSL hPR 5 (qBr BND 64 (toCl s) 5 md) rfl rfl (by decide))
theorem ssplit14_ok : CovK (ssplit14 ih md pos) := pc_spl ssplit14 (cov_ssplitQ hSL hPR 6 (qBr BND 64 (toCl s) 6 md) rfl rfl (by decide))
theorem ssplit15_ok : CovK (ssplit15 ih md pos) := pc_spl ssplit15 (cov_ssplitQ hSL hPR 7 (qBr BND 64 (toCl s) 7 md) rfl rfl (by decide))
theorem ssplit16_ok : CovK (ssplit16 ih md pos) := pc_spl ssplit16 (cov_ssplitQ hSL hPR 8 (qBr BND 64 (toCl s) 8 md) rfl rfl (by decide))
theorem ssplit24_ok : CovK (ssplit24 ih md pos) := pc_spl ssplit24 (cov_ssplitQ hSL hPR 9 (qBr BND 64 (toCl s) 9 md) rfl rfl (by decide))
theorem ssplit25_ok : CovK (ssplit25 ih md pos) := pc_spl ssplit25 (cov_ssplitQ hSL hPR 10 (qBr BND 64 (toCl s) 10 md) rfl rfl (by decide))
theorem ssplit26_ok : CovK (ssplit26 ih md pos) := pc_spl ssplit26 (cov_ssplitQ hSL hPR 11 (qBr BND 64 (toCl s) 11 md) rfl rfl (by decide))
theorem ssplit35_ok : CovK (ssplit35 ih md pos) := pc_spl ssplit35 (cov_ssplitQ hSL hPR 12 (qBr BND 64 (toCl s) 12 md) rfl rfl (by decide))
theorem ssplit36_ok : CovK (ssplit36 ih md pos) := pc_spl ssplit36 (cov_ssplitQ hSL hPR 13 (qBr BND 64 (toCl s) 13 md) rfl rfl (by decide))
theorem ssplit46_ok : CovK (ssplit46 ih md pos) := pc_spl ssplit46 (cov_ssplitQ hSL hPR 14 (qBr BND 64 (toCl s) 14 md) rfl rfl (by decide))
end

/-- a split node: axis `0 … 5` a gap, `6 … 20` a pair (pair order) -/
def splitAx (ih : WF) (md pos ax : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (zK) (ssplit46 ih md pos) (Nat.beq ax 20)) (ssplit36 ih md pos) (Nat.beq ax 19)) (ssplit35 ih md pos) (Nat.beq ax 18)) (ssplit26 ih md pos) (Nat.beq ax 17)) (ssplit25 ih md pos) (Nat.beq ax 16)) (ssplit24 ih md pos) (Nat.beq ax 15)) (ssplit16 ih md pos) (Nat.beq ax 14)) (ssplit15 ih md pos) (Nat.beq ax 13)) (ssplit14 ih md pos) (Nat.beq ax 12)) (ssplit13 ih md pos) (Nat.beq ax 11)) (ssplit06 ih md pos) (Nat.beq ax 10)) (ssplit05 ih md pos) (Nat.beq ax 9)) (ssplit04 ih md pos) (Nat.beq ax 8)) (ssplit03 ih md pos) (Nat.beq ax 7)) (ssplit02 ih md pos) (Nat.beq ax 6)) (gsplit5 ih md pos) (Nat.beq ax 5)) (gsplit4 ih md pos) (Nat.beq ax 4)) (gsplit3 ih md pos) (Nat.beq ax 3)) (gsplit2 ih md pos) (Nat.beq ax 2)) (gsplit1 ih md pos) (Nat.beq ax 1)) (gsplit0 ih md pos) (Nat.beq ax 0)

theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) :=
  brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => zK_ok) (fun _ => ssplit46_ok hih md pos)) (fun _ => ssplit36_ok hih md pos)) (fun _ => ssplit35_ok hih md pos)) (fun _ => ssplit26_ok hih md pos)) (fun _ => ssplit25_ok hih md pos)) (fun _ => ssplit24_ok hih md pos)) (fun _ => ssplit16_ok hih md pos)) (fun _ => ssplit15_ok hih md pos)) (fun _ => ssplit14_ok hih md pos)) (fun _ => ssplit13_ok hih md pos)) (fun _ => ssplit06_ok hih md pos)) (fun _ => ssplit05_ok hih md pos)) (fun _ => ssplit04_ok hih md pos)) (fun _ => ssplit03_ok hih md pos)) (fun _ => ssplit02_ok hih md pos)) (fun _ => gsplit5_ok hih md pos)) (fun _ => gsplit4_ok hih md pos)) (fun _ => gsplit3_ok hih md pos)) (fun _ => gsplit2_ok hih md pos)) (fun _ => gsplit1_ok hih md pos)) (fun _ => gsplit0_ok hih md pos)

-- (5) the root: the box sums written into the pair bounds (`matC`), once, which closes the root box (TZ.md §5)

def tm (k : ST) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T : ℕ) : ℕ :=
  forceR (nmax n (Nat.add a c)) fun n' => forceR (nmin o (Nat.add b d)) fun o' =>
  forceR (nmax r (Nat.add (Nat.add a c) e)) fun r' => forceR (nmin s (Nat.add (Nat.add b d) f)) fun s' =>
  forceR (nmax t (Nat.add (Nat.add (Nat.add a c) e) g)) fun t' => forceR (nmin u (Nat.add (Nat.add (Nat.add b d) f) h)) fun u' =>
  forceR (nmax v (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i)) fun v' => forceR (nmin w (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j)) fun w' =>
  forceR (nmax x (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l)) fun x' => forceR (nmin y (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m)) fun y' =>
  forceR (nmax z (Nat.add c e)) fun z' => forceR (nmin A (Nat.add d f)) fun A' =>
  forceR (nmax B (Nat.add (Nat.add c e) g)) fun B' => forceR (nmin C (Nat.add (Nat.add d f) h)) fun C' =>
  forceR (nmax D (Nat.add (Nat.add (Nat.add c e) g) i)) fun D' => forceR (nmin E (Nat.add (Nat.add (Nat.add d f) h) j)) fun E' =>
  forceR (nmax F (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l)) fun F' => forceR (nmin G (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m)) fun G' =>
  forceR (nmax H (Nat.add e g)) fun H' => forceR (nmin I (Nat.add f h)) fun I' =>
  forceR (nmax J (Nat.add (Nat.add e g) i)) fun J' => forceR (nmin K (Nat.add (Nat.add f h) j)) fun K' =>
  forceR (nmax L (Nat.add (Nat.add (Nat.add e g) i) l)) fun L' => forceR (nmin M (Nat.add (Nat.add (Nat.add f h) j) m)) fun M' =>
  forceR (nmax N (Nat.add g i)) fun N' => forceR (nmin O (Nat.add h j)) fun O' =>
  forceR (nmax P (Nat.add (Nat.add g i) l)) fun P' => forceR (nmin Q (Nat.add (Nat.add h j) m)) fun Q' =>
  forceR (nmax R (Nat.add i l)) fun R' => forceR (nmin S (Nat.add j m)) fun S' =>
  k a b c d e f g h i j l m n' o' r' s' t' u' v' w' x' y' z' A' B' C' D' E' F' G' H' I' J' K' L' M' N' O' P' Q' R' S' T

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

/-- (chunked walks) field-wise equality of two states -/
def stEq (a b : St) : Bool := Nat.beq a.l0 b.l0 && Nat.beq a.u0 b.u0 && Nat.beq a.l1 b.l1 && Nat.beq a.u1 b.u1 && Nat.beq a.l2 b.l2 && Nat.beq a.u2 b.u2 && Nat.beq a.l3 b.l3 && Nat.beq a.u3 b.u3 && Nat.beq a.l4 b.l4 && Nat.beq a.u4 b.u4 && Nat.beq a.l5 b.l5 && Nat.beq a.u5 b.u5 && Nat.beq a.A02 b.A02 && Nat.beq a.B02 b.B02 && Nat.beq a.A03 b.A03 && Nat.beq a.B03 b.B03 && Nat.beq a.A04 b.A04 && Nat.beq a.B04 b.B04 && Nat.beq a.A05 b.A05 && Nat.beq a.B05 b.B05 && Nat.beq a.A06 b.A06 && Nat.beq a.B06 b.B06 && Nat.beq a.A13 b.A13 && Nat.beq a.B13 b.B13 && Nat.beq a.A14 b.A14 && Nat.beq a.B14 b.B14 && Nat.beq a.A15 b.A15 && Nat.beq a.B15 b.B15 && Nat.beq a.A16 b.A16 && Nat.beq a.B16 b.B16 && Nat.beq a.A24 b.A24 && Nat.beq a.B24 b.B24 && Nat.beq a.A25 b.A25 && Nat.beq a.B25 b.B25 && Nat.beq a.A26 b.A26 && Nat.beq a.B26 b.B26 && Nat.beq a.A35 b.A35 && Nat.beq a.B35 b.B35 && Nat.beq a.A36 b.A36 && Nat.beq a.B36 b.B36 && Nat.beq a.A46 b.A46 && Nat.beq a.B46 b.B46 && Nat.beq a.M b.M
theorem St_eq {a b : St} (h : stEq a b = true) : a = b := by
  cases a; cases b
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩, h36⟩, h37⟩, h38⟩, h39⟩, h40⟩, h41⟩, h42⟩ := h
  subst_vars; rfl
/-- the continuation that accepts exactly the state `t` -/
def kEq (t : St) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A13 B13 A14 B14 A15 B15 A16 B16 A24 B24 A25 B25 A26 B26 A35 B35 A36 B36 A46 B46 M => Bool.rec (motive := fun _ => ℕ) 0 1 (stEq ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A13, B13, A14, B14, A15, B15, A16, B16, A24, B24, A25, B25, A26, B26, A35, B35, A36, B36, A46, B46, M⟩ t)
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
theorem gsplit_to (r : ℕ) (hr : r < 6) {t sA sB : St}
    (eA : toCl sA = cupd 6 PR SL ⟨(toCl t).L, (toCl t).U.set r (qG (toCl t) r), (toCl t).A, (toCl t).B⟩ r (r + 1))
    (eB : toCl sB = cupd 6 PR SL ⟨(toCl t).L.set r (qG (toCl t) r), (toCl t).U, (toCl t).A, (toCl t).B⟩ (r + 1) r)
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_gmidC hSL hPR r rfl rfl hr (eA ▸ hA) (eB ▸ hB)
/-- a chunk boundary's split on pair `k` at the raw midpoint of its bounds, the children closed (`cupd`) -/
theorem ssplit_to (k : ℕ) (hk : k < 15) {t sA sB : St}
    (eA : toCl sA = cupd 6 PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A, (toCl t).B.set k (qR (toCl t) k)⟩ (pI PR k) (pJ PR k))
    (eB : toCl sB = cupd 6 PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A.set k (qR (toCl t) k), (toCl t).B⟩ (pJ PR k) (pI PR k))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_rmidC hSL hPR k rfl rfl hk (eA ▸ hA) (eB ▸ hB)
/-- a walk from any bit position -/
theorem covered_of_walkP {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits fuel pos e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel pos s (h ▸ he)

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


end AMW.Cert.PCE6U
