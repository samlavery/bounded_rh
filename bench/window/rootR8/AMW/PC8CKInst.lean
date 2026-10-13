import AMW.PCellClose

/-! ###### polytope cells for Q = 7: the instance layer with the exact closure and Z
(instance layer: bridge-port, amg/genpcell4.py; the closure splits, the closure walk and its chunk lemmas: mvt-engine,
eight/am8/genpcellC.py, TZ.md §5)

Kernel functions unrolled on the curried state (14 gap and 42 pair bounds, the mask); every proof is a link to
the generic layer `AMW.PCellGen` through `toCl : St → Cl`.  The walk is mvt-engine's fixed-width DATA layout (emit8pz.py).
Engine, tables and per-term minorants: mvt-engine's MinCore on the AM
engine (pyramid oracle adapted from five-point-pyramid-2 by typh, Apache-2.0). ###### -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace AMW.Cert.PC8CK

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

def cN : ℕ := 805003
/-- the multiplier quantum: `Y = SIG · Yq`, `Yq < 2^12` (`2^-14` per unit g) -/
def SIG : ℕ := 6250000000000000

/-- the non-adjacent pairs, in pair order -/
def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 6), (4, 7), (5, 7)]
theorem hPR : PRok 7 PR := by decide
/-- the gap weights and the terms `(i, j, a, k)` of the functional `Fg` (units 1/SA) -/
def BS : List ℕ := [28898, 57272, 75526, 80958, 75526, 57272, 28898]
def TS : List Term := [(0, 1, 13630830, 0), (0, 3, 19565904, 1), (0, 4, 20317441, 2), (0, 5, 45030671, 3), (0, 6, 100000000, 4), (0, 7, 200000000, 5), (1, 2, 29997996, 0), (1, 3, 30621878, 6), (1, 4, 47766489, 7), (1, 5, 79682558, 8), (1, 6, 109938656, 9), (1, 7, 100000000, 10), (2, 3, 37356140, 0), (2, 4, 69378121, 11), (2, 5, 65335210, 12), (2, 6, 79682558, 13), (2, 7, 45030671, 14), (3, 4, 38030065, 0), (3, 5, 69378121, 15), (3, 6, 47766489, 16), (3, 7, 20317441, 17), (4, 5, 37356140, 0), (4, 6, 30621878, 18), (4, 7, 19565904, 19), (5, 6, 29997996, 0), (6, 7, 13630830, 0)]
theorem hTS : TSok 7 PR TS := by decide

/-- the slot of the pair `(a, b)`, `a < b`, at `a · 8 + b`: gap `a` when `b = a + 1`, else `7` + the pair's rank -/
def SL : List ℕ := [0, 0, 7, 8, 9, 10, 11, 12, 0, 0, 1, 13, 14, 15, 16, 17, 0, 0, 0, 2, 18, 19, 20, 21, 0, 0, 0, 0, 3, 22, 23, 24, 0, 0, 0, 0, 0, 4, 25, 26, 0, 0, 0, 0, 0, 0, 5, 27, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0]
theorem hSL : SLok 7 PR SL := by decide

def SA : ℕ := 100000000

/-- the weighted functional on the gaps, in real form (pair weights `a_ij` and pressures `b_r` over `SA`) -/
def G (g0 g1 g2 g3 g4 g5 g6 : ℝ) : ℝ :=
  (28898 / (SA:ℝ)) * g0 + (57272 / (SA:ℝ)) * g1 + (75526 / (SA:ℝ)) * g2 + (80958 / (SA:ℝ)) * g3 + (75526 / (SA:ℝ)) * g4 + (57272 / (SA:ℝ)) * g5 + (28898 / (SA:ℝ)) * g6
    + (13630830 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (19565904 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (20317441 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (45030671 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (29997996 / (SA:ℝ)) * wfun (g1) + (30621878 / (SA:ℝ)) * wfun (g1 + g2) + (47766489 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (79682558 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (109938656 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (37356140 / (SA:ℝ)) * wfun (g2) + (69378121 / (SA:ℝ)) * wfun (g2 + g3) + (65335210 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (79682558 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (45030671 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (38030065 / (SA:ℝ)) * wfun (g3) + (69378121 / (SA:ℝ)) * wfun (g3 + g4) + (47766489 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (20317441 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (37356140 / (SA:ℝ)) * wfun (g4) + (30621878 / (SA:ℝ)) * wfun (g4 + g5) + (19565904 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (29997996 / (SA:ℝ)) * wfun (g5) + (0 / (SA:ℝ)) * wfun (g5 + g6) + (13630830 / (SA:ℝ)) * wfun (g6)

/-- the integer functional `Fg` on a tuple of gaps is `SA · G` -/
theorem Fg_G (x0 x1 x2 x3 x4 x5 x6 : ℝ) : Fg 7 BS TS (fun r => [x0, x1, x2, x3, x4, x5, x6].getD r 0) = (SA : ℝ) * G x0 x1 x2 x3 x4 x5 x6 := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring

/-- the canonical tables (HUFF.md §3): per table the count of each code length from 0, and the symbols in table order
(16-bit fields); a term's symbol is `κ · 2^14 + j1 · 2^7 + j2`, the axis `0 … 6` a gap, `7 …` a pair (pair order),
the multiplier's `c` the pair's rank -/
-- (fixed-width fields: no tables)

abbrev Covered : Cl → Prop := CovBy 7 PR (Pg cN 7 BS TS)

/-- the kernel state -/
structure St where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A24 B24 A25 B25 A26 B26 A27 B27 A35 B35 A36 B36 A37 B37 A46 B46 A47 B47 A57 B57 M : ℕ)

def toCl (s : St) : Cl :=
  ⟨[s.l0, s.l1, s.l2, s.l3, s.l4, s.l5, s.l6], [s.u0, s.u1, s.u2, s.u3, s.u4, s.u5, s.u6],
   [s.A02, s.A03, s.A04, s.A05, s.A06, s.A07, s.A13, s.A14, s.A15, s.A16, s.A17, s.A24, s.A25, s.A26, s.A27, s.A35, s.A36, s.A37, s.A46, s.A47, s.A57], [s.B02, s.B03, s.B04, s.B05, s.B06, s.B07, s.B13, s.B14, s.B15, s.B16, s.B17, s.B24, s.B25, s.B26, s.B27, s.B35, s.B36, s.B37, s.B46, s.B47, s.B57]⟩
def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨c.L.getD 0 0, c.U.getD 0 0, c.L.getD 1 0, c.U.getD 1 0, c.L.getD 2 0, c.U.getD 2 0, c.L.getD 3 0, c.U.getD 3 0, c.L.getD 4 0, c.U.getD 4 0, c.L.getD 5 0, c.U.getD 5 0, c.L.getD 6 0, c.U.getD 6 0, c.A.getD 0 0, c.B.getD 0 0, c.A.getD 1 0, c.B.getD 1 0, c.A.getD 2 0, c.B.getD 2 0, c.A.getD 3 0, c.B.getD 3 0, c.A.getD 4 0, c.B.getD 4 0, c.A.getD 5 0, c.B.getD 5 0, c.A.getD 6 0, c.B.getD 6 0, c.A.getD 7 0, c.B.getD 7 0, c.A.getD 8 0, c.B.getD 8 0, c.A.getD 9 0, c.B.getD 9 0, c.A.getD 10 0, c.B.getD 10 0, c.A.getD 11 0, c.B.getD 11 0, c.A.getD 12 0, c.B.getD 12 0, c.A.getD 13 0, c.B.getD 13 0, c.A.getD 14 0, c.B.getD 14 0, c.A.getD 15 0, c.B.getD 15 0, c.A.getD 16 0, c.B.getD 16 0, c.A.getD 17 0, c.B.getD 17 0, c.A.getD 18 0, c.B.getD 18 0, c.A.getD 19 0, c.B.getD 19 0, c.A.getD 20 0, c.B.getD 20 0, m⟩

theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = 7) (h2 : c.U.length = 7) (h3 : c.A.length = 21) (h4 : c.B.length = 21) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]

abbrev ST : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
/-- a continuation applied to a state -/
def U (k : ST) (s : St) : ℕ := k s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.l6 s.u6 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A07 s.B07 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A17 s.B17 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A27 s.B27 s.A35 s.B35 s.A36 s.B36 s.A37 s.B37 s.A46 s.B46 s.A47 s.B47 s.A57 s.B57 s.M
def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
def zK : ST := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h

theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = 7) (h2 : c.U.length = 7) (h3 : c.A.length = 21)
    (h4 : c.B.length = 21) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h

/-- a split node's two children (`cA` from `pos`, the bit after the axis code, then `cB`) cover the cell when the split lemma does -/
theorem sp_ok {ih : WF} (hih : WalkOK ih) {s : St} {cA cB : Cl} {pos mA mB : ℕ}
    (hc : Covered cA → Covered cB → Covered (toCl s))
    (h : Bool.rec (motive := fun _ => ℕ) (U (ih (U (ih pos) (ofCl cA mA))) (ofCl cB mB)) 0
      (Nat.beq (U (ih pos) (ofCl cA mA)) 0) ≠ 0)
    (hA : cA.L.length = 7 ∧ cA.U.length = 7 ∧ cA.A.length = 21 ∧ cA.B.length = 21)
    (hB : cB.L.length = 7 ∧ cB.U.length = 7 ∧ cB.A.length = 21 ∧ cB.B.length = 21) : Covered (toCl s) := by
  cases hp : Nat.beq (U (ih pos) (ofCl cA mA)) 0
  · rw [hp] at h
    exact hc (ofCl_ok (hih _) hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 fun h0 => by rw [h0] at hp; exact absurd hp (by decide))
      (ofCl_ok (hih _) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 h)
  · rw [hp] at h; exact absurd rfl h


-- (2) split nodes: gap r at the midpoint of [l_r, u_r]; pair t at the midpoint of its (persisted) bounds

def gsplit0 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add a b) 1;
  let ka0 := nmin q q;
  let ka1 := nmax c (Nat.sub r q);
  let ka2 := nmax e (Nat.sub t (Nat.add q d));
  let ka3 := nmin f (Nat.sub (Nat.add q E) r);
  let ka4 := nmax g (Nat.sub v (Nat.add q E));
  let ka5 := nmin h (Nat.sub (Nat.add q G) t);
  let ka6 := nmax i (Nat.sub x (Nat.add q G));
  let ka7 := nmin j (Nat.sub (Nat.add q I) v);
  let ka8 := nmax l (Nat.sub z (Nat.add q I));
  let ka9 := nmin m (Nat.sub (Nat.add q K) x);
  let ka10 := nmax n (Nat.sub B (Nat.add q K));
  let ka11 := nmin o (Nat.sub (Nat.add q M) z);
  let ka12 := nmin s (Nat.add q d);
  let ka13 := nmin u (Nat.add q E);
  let ka14 := nmin w (Nat.add q G);
  let ka15 := nmin y (Nat.add q I);
  let ka16 := nmin A (Nat.add q K);
  let ka17 := nmin C (Nat.add q M);
  let ka18 := nmax D (Nat.sub t q);
  let ka19 := nmax F (Nat.sub v q);
  let ka20 := nmax H (Nat.sub x q);
  let ka21 := nmax J (Nat.sub z q);
  let ka22 := nmax L (Nat.sub B q);
  let ka23 := nmax N (Nat.sub v (Nat.add q d));
  let ka24 := nmin O (Nat.sub (Nat.add q G) r);
  let ka25 := nmax P (Nat.sub x (Nat.add q d));
  let ka26 := nmin Q (Nat.sub (Nat.add q I) r);
  let ka27 := nmax R (Nat.sub z (Nat.add q d));
  let ka28 := nmin S (Nat.sub (Nat.add q K) r);
  let ka29 := nmax T (Nat.sub B (Nat.add q d));
  let ka30 := nmin U (Nat.sub (Nat.add q M) r);
  let ka31 := nmax V (Nat.sub x (Nat.add q E));
  let ka32 := nmin W (Nat.sub (Nat.add q I) t);
  let ka33 := nmax X (Nat.sub z (Nat.add q E));
  let ka34 := nmin Y (Nat.sub (Nat.add q K) t);
  let ka35 := nmax Z (Nat.sub B (Nat.add q E));
  let ka36 := nmin aa (Nat.sub (Nat.add q M) t);
  let ka37 := nmax ab (Nat.sub z (Nat.add q G));
  let ka38 := nmin ac (Nat.sub (Nat.add q K) v);
  let ka39 := nmax ad (Nat.sub B (Nat.add q G));
  let ka40 := nmin ae (Nat.sub (Nat.add q M) v);
  let ka41 := nmax af (Nat.sub B (Nat.add q I));
  let ka42 := nmin ag (Nat.sub (Nat.add q M) x);
  let p := ih pos a ka0 ka1 d ka2 ka3 ka4 ka5 ka6 ka7 ka8 ka9 ka10 ka11 r ka12 t ka13 v ka14 x ka15 z ka16 B ka17 ka18 E ka19 G ka20 I ka21 K ka22 M ka23 ka24 ka25 ka26 ka27 ka28 ka29 ka30 ka31 ka32 ka33 ka34 ka35 ka36 ka37 ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax q q;
    let kb1 := nmin d (Nat.sub s q);
    let kb2 := nmax e (Nat.sub (Nat.add D q) s);
    let kb3 := nmin f (Nat.sub u (Nat.add c q));
    let kb4 := nmax g (Nat.sub (Nat.add F q) u);
    let kb5 := nmin h (Nat.sub w (Nat.add D q));
    let kb6 := nmax i (Nat.sub (Nat.add H q) w);
    let kb7 := nmin j (Nat.sub y (Nat.add F q));
    let kb8 := nmax l (Nat.sub (Nat.add J q) y);
    let kb9 := nmin m (Nat.sub A (Nat.add H q));
    let kb10 := nmax n (Nat.sub (Nat.add L q) A);
    let kb11 := nmin o (Nat.sub C (Nat.add J q));
    let kb12 := nmax r (Nat.add c q);
    let kb13 := nmax t (Nat.add D q);
    let kb14 := nmax v (Nat.add F q);
    let kb15 := nmax x (Nat.add H q);
    let kb16 := nmax z (Nat.add J q);
    let kb17 := nmax B (Nat.add L q);
    let kb18 := nmin E (Nat.sub u q);
    let kb19 := nmin G (Nat.sub w q);
    let kb20 := nmin I (Nat.sub y q);
    let kb21 := nmin K (Nat.sub A q);
    let kb22 := nmin M (Nat.sub C q);
    let kb23 := nmax N (Nat.sub (Nat.add F q) s);
    let kb24 := nmin O (Nat.sub w (Nat.add c q));
    let kb25 := nmax P (Nat.sub (Nat.add H q) s);
    let kb26 := nmin Q (Nat.sub y (Nat.add c q));
    let kb27 := nmax R (Nat.sub (Nat.add J q) s);
    let kb28 := nmin S (Nat.sub A (Nat.add c q));
    let kb29 := nmax T (Nat.sub (Nat.add L q) s);
    let kb30 := nmin U (Nat.sub C (Nat.add c q));
    let kb31 := nmax V (Nat.sub (Nat.add H q) u);
    let kb32 := nmin W (Nat.sub y (Nat.add D q));
    let kb33 := nmax X (Nat.sub (Nat.add J q) u);
    let kb34 := nmin Y (Nat.sub A (Nat.add D q));
    let kb35 := nmax Z (Nat.sub (Nat.add L q) u);
    let kb36 := nmin aa (Nat.sub C (Nat.add D q));
    let kb37 := nmax ab (Nat.sub (Nat.add J q) w);
    let kb38 := nmin ac (Nat.sub A (Nat.add F q));
    let kb39 := nmax ad (Nat.sub (Nat.add L q) w);
    let kb40 := nmin ae (Nat.sub C (Nat.add F q));
    let kb41 := nmax af (Nat.sub (Nat.add L q) y);
    let kb42 := nmin ag (Nat.sub C (Nat.add H q));
    ih p kb0 b c kb1 kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 kb11 kb12 s kb13 u kb14 w kb15 y kb16 A kb17 C D kb18 F kb19 H kb20 J kb21 L kb22 kb23 kb24 kb25 kb26 kb27 kb28 kb29 kb30 kb31 kb32 kb33 kb34 kb35 kb36 kb37 kb38 kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def gsplit1 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add c d) 1;
  let ka0 := nmax a (Nat.sub r q);
  let ka1 := nmin q q;
  let ka2 := nmax e (Nat.sub D q);
  let ka3 := nmax g (Nat.sub F (Nat.add q f));
  let ka4 := nmin h (Nat.sub (Nat.add q O) D);
  let ka5 := nmax i (Nat.sub H (Nat.add q O));
  let ka6 := nmin j (Nat.sub (Nat.add q Q) F);
  let ka7 := nmax l (Nat.sub J (Nat.add q Q));
  let ka8 := nmin m (Nat.sub (Nat.add q S) H);
  let ka9 := nmax n (Nat.sub L (Nat.add q S));
  let ka10 := nmin o (Nat.sub (Nat.add q U) J);
  let ka11 := nmin s (Nat.add b q);
  let ka12 := nmax t (Nat.sub (Nat.add D r) q);
  let ka13 := nmin u (Nat.add (Nat.add b q) f);
  let ka14 := nmax v (Nat.sub (Nat.add F r) q);
  let ka15 := nmin w (Nat.add (Nat.add b q) O);
  let ka16 := nmax x (Nat.sub (Nat.add H r) q);
  let ka17 := nmin y (Nat.add (Nat.add b q) Q);
  let ka18 := nmax z (Nat.sub (Nat.add J r) q);
  let ka19 := nmin A (Nat.add (Nat.add b q) S);
  let ka20 := nmax B (Nat.sub (Nat.add L r) q);
  let ka21 := nmin C (Nat.add (Nat.add b q) U);
  let ka22 := nmin E (Nat.add q f);
  let ka23 := nmin G (Nat.add q O);
  let ka24 := nmin I (Nat.add q Q);
  let ka25 := nmin K (Nat.add q S);
  let ka26 := nmin M (Nat.add q U);
  let ka27 := nmax N (Nat.sub F q);
  let ka28 := nmax P (Nat.sub H q);
  let ka29 := nmax R (Nat.sub J q);
  let ka30 := nmax T (Nat.sub L q);
  let ka31 := nmax V (Nat.sub H (Nat.add q f));
  let ka32 := nmin W (Nat.sub (Nat.add q Q) D);
  let ka33 := nmax X (Nat.sub J (Nat.add q f));
  let ka34 := nmin Y (Nat.sub (Nat.add q S) D);
  let ka35 := nmax Z (Nat.sub L (Nat.add q f));
  let ka36 := nmin aa (Nat.sub (Nat.add q U) D);
  let ka37 := nmax ab (Nat.sub J (Nat.add q O));
  let ka38 := nmin ac (Nat.sub (Nat.add q S) F);
  let ka39 := nmax ad (Nat.sub L (Nat.add q O));
  let ka40 := nmin ae (Nat.sub (Nat.add q U) F);
  let ka41 := nmax af (Nat.sub L (Nat.add q Q));
  let ka42 := nmin ag (Nat.sub (Nat.add q U) H);
  let p := ih pos ka0 b c ka1 ka2 f ka3 ka4 ka5 ka6 ka7 ka8 ka9 ka10 r ka11 ka12 ka13 ka14 ka15 ka16 ka17 ka18 ka19 ka20 ka21 D ka22 F ka23 H ka24 J ka25 L ka26 ka27 O ka28 Q ka29 S ka30 U ka31 ka32 ka33 ka34 ka35 ka36 ka37 ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub s q);
    let kb1 := nmax q q;
    let kb2 := nmin f (Nat.sub E q);
    let kb3 := nmax g (Nat.sub (Nat.add N q) E);
    let kb4 := nmin h (Nat.sub G (Nat.add e q));
    let kb5 := nmax i (Nat.sub (Nat.add P q) G);
    let kb6 := nmin j (Nat.sub I (Nat.add N q));
    let kb7 := nmax l (Nat.sub (Nat.add R q) I);
    let kb8 := nmin m (Nat.sub K (Nat.add P q));
    let kb9 := nmax n (Nat.sub (Nat.add T q) K);
    let kb10 := nmin o (Nat.sub M (Nat.add R q));
    let kb11 := nmax r (Nat.add q a);
    let kb12 := nmax t (Nat.add (Nat.add e q) a);
    let kb13 := nmin u (Nat.sub (Nat.add s E) q);
    let kb14 := nmax v (Nat.add (Nat.add N q) a);
    let kb15 := nmin w (Nat.sub (Nat.add s G) q);
    let kb16 := nmax x (Nat.add (Nat.add P q) a);
    let kb17 := nmin y (Nat.sub (Nat.add s I) q);
    let kb18 := nmax z (Nat.add (Nat.add R q) a);
    let kb19 := nmin A (Nat.sub (Nat.add s K) q);
    let kb20 := nmax B (Nat.add (Nat.add T q) a);
    let kb21 := nmin C (Nat.sub (Nat.add s M) q);
    let kb22 := nmax D (Nat.add e q);
    let kb23 := nmax F (Nat.add N q);
    let kb24 := nmax H (Nat.add P q);
    let kb25 := nmax J (Nat.add R q);
    let kb26 := nmax L (Nat.add T q);
    let kb27 := nmin O (Nat.sub G q);
    let kb28 := nmin Q (Nat.sub I q);
    let kb29 := nmin S (Nat.sub K q);
    let kb30 := nmin U (Nat.sub M q);
    let kb31 := nmax V (Nat.sub (Nat.add P q) E);
    let kb32 := nmin W (Nat.sub I (Nat.add e q));
    let kb33 := nmax X (Nat.sub (Nat.add R q) E);
    let kb34 := nmin Y (Nat.sub K (Nat.add e q));
    let kb35 := nmax Z (Nat.sub (Nat.add T q) E);
    let kb36 := nmin aa (Nat.sub M (Nat.add e q));
    let kb37 := nmax ab (Nat.sub (Nat.add R q) G);
    let kb38 := nmin ac (Nat.sub K (Nat.add N q));
    let kb39 := nmax ad (Nat.sub (Nat.add T q) G);
    let kb40 := nmin ae (Nat.sub M (Nat.add N q));
    let kb41 := nmax af (Nat.sub (Nat.add T q) I);
    let kb42 := nmin ag (Nat.sub M (Nat.add P q));
    ih p a kb0 kb1 d e kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 kb11 s kb12 kb13 kb14 kb15 kb16 kb17 kb18 kb19 kb20 kb21 kb22 E kb23 G kb24 I kb25 K kb26 M N kb27 P kb28 R kb29 T kb30 kb31 kb32 kb33 kb34 kb35 kb36 kb37 kb38 kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def gsplit2 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add e f) 1;
  let ka0 := nmax a (Nat.sub t (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) D);
  let ka2 := nmax c (Nat.sub D q);
  let ka3 := nmin q q;
  let ka4 := nmax g (Nat.sub N q);
  let ka5 := nmax i (Nat.sub P (Nat.add q h));
  let ka6 := nmin j (Nat.sub (Nat.add q W) N);
  let ka7 := nmax l (Nat.sub R (Nat.add q W));
  let ka8 := nmin m (Nat.sub (Nat.add q Y) P);
  let ka9 := nmax n (Nat.sub T (Nat.add q Y));
  let ka10 := nmin o (Nat.sub (Nat.add q aa) R);
  let ka11 := nmax r (Nat.sub t q);
  let ka12 := nmin u (Nat.add s q);
  let ka13 := nmax v (Nat.sub (Nat.add N t) q);
  let ka14 := nmin w (Nat.add (Nat.add s q) h);
  let ka15 := nmax x (Nat.sub (Nat.add P t) q);
  let ka16 := nmin y (Nat.add (Nat.add s q) W);
  let ka17 := nmax z (Nat.sub (Nat.add R t) q);
  let ka18 := nmin A (Nat.add (Nat.add s q) Y);
  let ka19 := nmax B (Nat.sub (Nat.add T t) q);
  let ka20 := nmin C (Nat.add (Nat.add s q) aa);
  let ka21 := nmin E (Nat.add d q);
  let ka22 := nmax F (Nat.sub (Nat.add N D) q);
  let ka23 := nmin G (Nat.add (Nat.add d q) h);
  let ka24 := nmax H (Nat.sub (Nat.add P D) q);
  let ka25 := nmin I (Nat.add (Nat.add d q) W);
  let ka26 := nmax J (Nat.sub (Nat.add R D) q);
  let ka27 := nmin K (Nat.add (Nat.add d q) Y);
  let ka28 := nmax L (Nat.sub (Nat.add T D) q);
  let ka29 := nmin M (Nat.add (Nat.add d q) aa);
  let ka30 := nmin O (Nat.add q h);
  let ka31 := nmin Q (Nat.add q W);
  let ka32 := nmin S (Nat.add q Y);
  let ka33 := nmin U (Nat.add q aa);
  let ka34 := nmax V (Nat.sub P q);
  let ka35 := nmax X (Nat.sub R q);
  let ka36 := nmax Z (Nat.sub T q);
  let ka37 := nmax ab (Nat.sub R (Nat.add q h));
  let ka38 := nmin ac (Nat.sub (Nat.add q Y) N);
  let ka39 := nmax ad (Nat.sub T (Nat.add q h));
  let ka40 := nmin ae (Nat.sub (Nat.add q aa) N);
  let ka41 := nmax af (Nat.sub T (Nat.add q W));
  let ka42 := nmin ag (Nat.sub (Nat.add q aa) P);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 h ka5 ka6 ka7 ka8 ka9 ka10 ka11 s t ka12 ka13 ka14 ka15 ka16 ka17 ka18 ka19 ka20 D ka21 ka22 ka23 ka24 ka25 ka26 ka27 ka28 ka29 N ka30 P ka31 R ka32 T ka33 ka34 W ka35 Y ka36 aa ka37 ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) E);
    let kb1 := nmin b (Nat.sub u (Nat.add q c));
    let kb2 := nmin d (Nat.sub E q);
    let kb3 := nmax q q;
    let kb4 := nmin h (Nat.sub O q);
    let kb5 := nmax i (Nat.sub (Nat.add V q) O);
    let kb6 := nmin j (Nat.sub Q (Nat.add g q));
    let kb7 := nmax l (Nat.sub (Nat.add X q) Q);
    let kb8 := nmin m (Nat.sub S (Nat.add V q));
    let kb9 := nmax n (Nat.sub (Nat.add Z q) S);
    let kb10 := nmin o (Nat.sub U (Nat.add X q));
    let kb11 := nmin s (Nat.sub u q);
    let kb12 := nmax t (Nat.add q r);
    let kb13 := nmax v (Nat.add (Nat.add g q) r);
    let kb14 := nmin w (Nat.sub (Nat.add u O) q);
    let kb15 := nmax x (Nat.add (Nat.add V q) r);
    let kb16 := nmin y (Nat.sub (Nat.add u Q) q);
    let kb17 := nmax z (Nat.add (Nat.add X q) r);
    let kb18 := nmin A (Nat.sub (Nat.add u S) q);
    let kb19 := nmax B (Nat.add (Nat.add Z q) r);
    let kb20 := nmin C (Nat.sub (Nat.add u U) q);
    let kb21 := nmax D (Nat.add q c);
    let kb22 := nmax F (Nat.add (Nat.add g q) c);
    let kb23 := nmin G (Nat.sub (Nat.add E O) q);
    let kb24 := nmax H (Nat.add (Nat.add V q) c);
    let kb25 := nmin I (Nat.sub (Nat.add E Q) q);
    let kb26 := nmax J (Nat.add (Nat.add X q) c);
    let kb27 := nmin K (Nat.sub (Nat.add E S) q);
    let kb28 := nmax L (Nat.add (Nat.add Z q) c);
    let kb29 := nmin M (Nat.sub (Nat.add E U) q);
    let kb30 := nmax N (Nat.add g q);
    let kb31 := nmax P (Nat.add V q);
    let kb32 := nmax R (Nat.add X q);
    let kb33 := nmax T (Nat.add Z q);
    let kb34 := nmin W (Nat.sub Q q);
    let kb35 := nmin Y (Nat.sub S q);
    let kb36 := nmin aa (Nat.sub U q);
    let kb37 := nmax ab (Nat.sub (Nat.add X q) O);
    let kb38 := nmin ac (Nat.sub S (Nat.add g q));
    let kb39 := nmax ad (Nat.sub (Nat.add Z q) O);
    let kb40 := nmin ae (Nat.sub U (Nat.add g q));
    let kb41 := nmax af (Nat.sub (Nat.add Z q) Q);
    let kb42 := nmin ag (Nat.sub U (Nat.add V q));
    ih p kb0 kb1 c kb2 kb3 f g kb4 kb5 kb6 kb7 kb8 kb9 kb10 r kb11 kb12 u kb13 kb14 kb15 kb16 kb17 kb18 kb19 kb20 kb21 E kb22 kb23 kb24 kb25 kb26 kb27 kb28 kb29 kb30 O kb31 Q kb32 S kb33 U V kb34 X kb35 Z kb36 kb37 kb38 kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def gsplit3 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add g h) 1;
  let ka0 := nmax a (Nat.sub v (Nat.add E q));
  let ka1 := nmin b (Nat.sub (Nat.add u q) F);
  let ka2 := nmax c (Nat.sub F (Nat.add f q));
  let ka3 := nmin d (Nat.sub (Nat.add E q) N);
  let ka4 := nmax e (Nat.sub N q);
  let ka5 := nmin q q;
  let ka6 := nmax i (Nat.sub V q);
  let ka7 := nmax l (Nat.sub X (Nat.add q j));
  let ka8 := nmin m (Nat.sub (Nat.add q ac) V);
  let ka9 := nmax n (Nat.sub Z (Nat.add q ac));
  let ka10 := nmin o (Nat.sub (Nat.add q ae) X);
  let ka11 := nmax r (Nat.sub v (Nat.add f q));
  let ka12 := nmin s (Nat.sub (Nat.add u q) N);
  let ka13 := nmax t (Nat.sub v q);
  let ka14 := nmin w (Nat.add u q);
  let ka15 := nmax x (Nat.sub (Nat.add V v) q);
  let ka16 := nmin y (Nat.add (Nat.add u q) j);
  let ka17 := nmax z (Nat.sub (Nat.add X v) q);
  let ka18 := nmin A (Nat.add (Nat.add u q) ac);
  let ka19 := nmax B (Nat.sub (Nat.add Z v) q);
  let ka20 := nmin C (Nat.add (Nat.add u q) ae);
  let ka21 := nmax D (Nat.sub F q);
  let ka22 := nmin G (Nat.add E q);
  let ka23 := nmax H (Nat.sub (Nat.add V F) q);
  let ka24 := nmin I (Nat.add (Nat.add E q) j);
  let ka25 := nmax J (Nat.sub (Nat.add X F) q);
  let ka26 := nmin K (Nat.add (Nat.add E q) ac);
  let ka27 := nmax L (Nat.sub (Nat.add Z F) q);
  let ka28 := nmin M (Nat.add (Nat.add E q) ae);
  let ka29 := nmin O (Nat.add f q);
  let ka30 := nmax P (Nat.sub (Nat.add V N) q);
  let ka31 := nmin Q (Nat.add (Nat.add f q) j);
  let ka32 := nmax R (Nat.sub (Nat.add X N) q);
  let ka33 := nmin S (Nat.add (Nat.add f q) ac);
  let ka34 := nmax T (Nat.sub (Nat.add Z N) q);
  let ka35 := nmin U (Nat.add (Nat.add f q) ae);
  let ka36 := nmin W (Nat.add q j);
  let ka37 := nmin Y (Nat.add q ac);
  let ka38 := nmin aa (Nat.add q ae);
  let ka39 := nmax ab (Nat.sub X q);
  let ka40 := nmax ad (Nat.sub Z q);
  let ka41 := nmax af (Nat.sub Z (Nat.add q j));
  let ka42 := nmin ag (Nat.sub (Nat.add q ae) V);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 f g ka5 ka6 j ka7 ka8 ka9 ka10 ka11 ka12 ka13 u v ka14 ka15 ka16 ka17 ka18 ka19 ka20 ka21 E F ka22 ka23 ka24 ka25 ka26 ka27 ka28 N ka29 ka30 ka31 ka32 ka33 ka34 ka35 V ka36 X ka37 Z ka38 ka39 ac ka40 ae ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q t) G);
    let kb1 := nmin b (Nat.sub w (Nat.add q D));
    let kb2 := nmax c (Nat.sub (Nat.add q D) O);
    let kb3 := nmin d (Nat.sub G (Nat.add q e));
    let kb4 := nmin f (Nat.sub O q);
    let kb5 := nmax q q;
    let kb6 := nmin j (Nat.sub W q);
    let kb7 := nmax l (Nat.sub (Nat.add ab q) W);
    let kb8 := nmin m (Nat.sub Y (Nat.add i q));
    let kb9 := nmax n (Nat.sub (Nat.add ad q) Y);
    let kb10 := nmin o (Nat.sub aa (Nat.add ab q));
    let kb11 := nmax r (Nat.sub (Nat.add q t) O);
    let kb12 := nmin s (Nat.sub w (Nat.add q e));
    let kb13 := nmin u (Nat.sub w q);
    let kb14 := nmax v (Nat.add q t);
    let kb15 := nmax x (Nat.add (Nat.add i q) t);
    let kb16 := nmin y (Nat.sub (Nat.add w W) q);
    let kb17 := nmax z (Nat.add (Nat.add ab q) t);
    let kb18 := nmin A (Nat.sub (Nat.add w Y) q);
    let kb19 := nmax B (Nat.add (Nat.add ad q) t);
    let kb20 := nmin C (Nat.sub (Nat.add w aa) q);
    let kb21 := nmin E (Nat.sub G q);
    let kb22 := nmax F (Nat.add q D);
    let kb23 := nmax H (Nat.add (Nat.add i q) D);
    let kb24 := nmin I (Nat.sub (Nat.add G W) q);
    let kb25 := nmax J (Nat.add (Nat.add ab q) D);
    let kb26 := nmin K (Nat.sub (Nat.add G Y) q);
    let kb27 := nmax L (Nat.add (Nat.add ad q) D);
    let kb28 := nmin M (Nat.sub (Nat.add G aa) q);
    let kb29 := nmax N (Nat.add q e);
    let kb30 := nmax P (Nat.add (Nat.add i q) e);
    let kb31 := nmin Q (Nat.sub (Nat.add O W) q);
    let kb32 := nmax R (Nat.add (Nat.add ab q) e);
    let kb33 := nmin S (Nat.sub (Nat.add O Y) q);
    let kb34 := nmax T (Nat.add (Nat.add ad q) e);
    let kb35 := nmin U (Nat.sub (Nat.add O aa) q);
    let kb36 := nmax V (Nat.add i q);
    let kb37 := nmax X (Nat.add ab q);
    let kb38 := nmax Z (Nat.add ad q);
    let kb39 := nmin ac (Nat.sub Y q);
    let kb40 := nmin ae (Nat.sub aa q);
    let kb41 := nmax af (Nat.sub (Nat.add ad q) W);
    let kb42 := nmin ag (Nat.sub aa (Nat.add i q));
    ih p kb0 kb1 kb2 kb3 e kb4 kb5 h i kb6 kb7 kb8 kb9 kb10 kb11 kb12 t kb13 kb14 w kb15 kb16 kb17 kb18 kb19 kb20 D kb21 kb22 G kb23 kb24 kb25 kb26 kb27 kb28 kb29 O kb30 kb31 kb32 kb33 kb34 kb35 kb36 W kb37 Y kb38 aa ab kb39 ad kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def gsplit4 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add i j) 1;
  let ka0 := nmax a (Nat.sub x (Nat.add G q));
  let ka1 := nmin b (Nat.sub (Nat.add w q) H);
  let ka2 := nmax c (Nat.sub H (Nat.add O q));
  let ka3 := nmin d (Nat.sub (Nat.add G q) P);
  let ka4 := nmax e (Nat.sub P (Nat.add h q));
  let ka5 := nmin f (Nat.sub (Nat.add O q) V);
  let ka6 := nmax g (Nat.sub V q);
  let ka7 := nmin q q;
  let ka8 := nmax l (Nat.sub ab q);
  let ka9 := nmax n (Nat.sub ad (Nat.add q m));
  let ka10 := nmin o (Nat.sub (Nat.add q ag) ab);
  let ka11 := nmax r (Nat.sub x (Nat.add O q));
  let ka12 := nmin s (Nat.sub (Nat.add w q) P);
  let ka13 := nmax t (Nat.sub x (Nat.add h q));
  let ka14 := nmin u (Nat.sub (Nat.add w q) V);
  let ka15 := nmax v (Nat.sub x q);
  let ka16 := nmin y (Nat.add w q);
  let ka17 := nmax z (Nat.sub (Nat.add ab x) q);
  let ka18 := nmin A (Nat.add (Nat.add w q) m);
  let ka19 := nmax B (Nat.sub (Nat.add ad x) q);
  let ka20 := nmin C (Nat.add (Nat.add w q) ag);
  let ka21 := nmax D (Nat.sub H (Nat.add h q));
  let ka22 := nmin E (Nat.sub (Nat.add G q) V);
  let ka23 := nmax F (Nat.sub H q);
  let ka24 := nmin I (Nat.add G q);
  let ka25 := nmax J (Nat.sub (Nat.add ab H) q);
  let ka26 := nmin K (Nat.add (Nat.add G q) m);
  let ka27 := nmax L (Nat.sub (Nat.add ad H) q);
  let ka28 := nmin M (Nat.add (Nat.add G q) ag);
  let ka29 := nmax N (Nat.sub P q);
  let ka30 := nmin Q (Nat.add O q);
  let ka31 := nmax R (Nat.sub (Nat.add ab P) q);
  let ka32 := nmin S (Nat.add (Nat.add O q) m);
  let ka33 := nmax T (Nat.sub (Nat.add ad P) q);
  let ka34 := nmin U (Nat.add (Nat.add O q) ag);
  let ka35 := nmin W (Nat.add h q);
  let ka36 := nmax X (Nat.sub (Nat.add ab V) q);
  let ka37 := nmin Y (Nat.add (Nat.add h q) m);
  let ka38 := nmax Z (Nat.sub (Nat.add ad V) q);
  let ka39 := nmin aa (Nat.add (Nat.add h q) ag);
  let ka40 := nmin ac (Nat.add q m);
  let ka41 := nmin ae (Nat.add q ag);
  let ka42 := nmax af (Nat.sub ad q);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 h i ka7 ka8 m ka9 ka10 ka11 ka12 ka13 ka14 ka15 w x ka16 ka17 ka18 ka19 ka20 ka21 ka22 ka23 G H ka24 ka25 ka26 ka27 ka28 ka29 O P ka30 ka31 ka32 ka33 ka34 V ka35 ka36 ka37 ka38 ka39 ab ka40 ad ka41 ka42 ag ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q v) I);
    let kb1 := nmin b (Nat.sub y (Nat.add q F));
    let kb2 := nmax c (Nat.sub (Nat.add q F) Q);
    let kb3 := nmin d (Nat.sub I (Nat.add q N));
    let kb4 := nmax e (Nat.sub (Nat.add q N) W);
    let kb5 := nmin f (Nat.sub Q (Nat.add q g));
    let kb6 := nmin h (Nat.sub W q);
    let kb7 := nmax q q;
    let kb8 := nmin m (Nat.sub ac q);
    let kb9 := nmax n (Nat.sub (Nat.add af q) ac);
    let kb10 := nmin o (Nat.sub ae (Nat.add l q));
    let kb11 := nmax r (Nat.sub (Nat.add q v) Q);
    let kb12 := nmin s (Nat.sub y (Nat.add q N));
    let kb13 := nmax t (Nat.sub (Nat.add q v) W);
    let kb14 := nmin u (Nat.sub y (Nat.add q g));
    let kb15 := nmin w (Nat.sub y q);
    let kb16 := nmax x (Nat.add q v);
    let kb17 := nmax z (Nat.add (Nat.add l q) v);
    let kb18 := nmin A (Nat.sub (Nat.add y ac) q);
    let kb19 := nmax B (Nat.add (Nat.add af q) v);
    let kb20 := nmin C (Nat.sub (Nat.add y ae) q);
    let kb21 := nmax D (Nat.sub (Nat.add q F) W);
    let kb22 := nmin E (Nat.sub I (Nat.add q g));
    let kb23 := nmin G (Nat.sub I q);
    let kb24 := nmax H (Nat.add q F);
    let kb25 := nmax J (Nat.add (Nat.add l q) F);
    let kb26 := nmin K (Nat.sub (Nat.add I ac) q);
    let kb27 := nmax L (Nat.add (Nat.add af q) F);
    let kb28 := nmin M (Nat.sub (Nat.add I ae) q);
    let kb29 := nmin O (Nat.sub Q q);
    let kb30 := nmax P (Nat.add q N);
    let kb31 := nmax R (Nat.add (Nat.add l q) N);
    let kb32 := nmin S (Nat.sub (Nat.add Q ac) q);
    let kb33 := nmax T (Nat.add (Nat.add af q) N);
    let kb34 := nmin U (Nat.sub (Nat.add Q ae) q);
    let kb35 := nmax V (Nat.add q g);
    let kb36 := nmax X (Nat.add (Nat.add l q) g);
    let kb37 := nmin Y (Nat.sub (Nat.add W ac) q);
    let kb38 := nmax Z (Nat.add (Nat.add af q) g);
    let kb39 := nmin aa (Nat.sub (Nat.add W ae) q);
    let kb40 := nmax ab (Nat.add l q);
    let kb41 := nmax ad (Nat.add af q);
    let kb42 := nmin ag (Nat.sub ae q);
    ih p kb0 kb1 kb2 kb3 kb4 kb5 g kb6 kb7 j l kb8 kb9 kb10 kb11 kb12 kb13 kb14 v kb15 kb16 y kb17 kb18 kb19 kb20 kb21 kb22 F kb23 kb24 I kb25 kb26 kb27 kb28 N kb29 kb30 Q kb31 kb32 kb33 kb34 kb35 W kb36 kb37 kb38 kb39 kb40 ac kb41 ae af kb42 ah) 0 (Nat.beq p 0)

def gsplit5 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add l m) 1;
  let ka0 := nmax a (Nat.sub z (Nat.add I q));
  let ka1 := nmin b (Nat.sub (Nat.add y q) J);
  let ka2 := nmax c (Nat.sub J (Nat.add Q q));
  let ka3 := nmin d (Nat.sub (Nat.add I q) R);
  let ka4 := nmax e (Nat.sub R (Nat.add W q));
  let ka5 := nmin f (Nat.sub (Nat.add Q q) X);
  let ka6 := nmax g (Nat.sub X (Nat.add j q));
  let ka7 := nmin h (Nat.sub (Nat.add W q) ab);
  let ka8 := nmax i (Nat.sub ab q);
  let ka9 := nmin q q;
  let ka10 := nmax n (Nat.sub af q);
  let ka11 := nmax r (Nat.sub z (Nat.add Q q));
  let ka12 := nmin s (Nat.sub (Nat.add y q) R);
  let ka13 := nmax t (Nat.sub z (Nat.add W q));
  let ka14 := nmin u (Nat.sub (Nat.add y q) X);
  let ka15 := nmax v (Nat.sub z (Nat.add j q));
  let ka16 := nmin w (Nat.sub (Nat.add y q) ab);
  let ka17 := nmax x (Nat.sub z q);
  let ka18 := nmin A (Nat.add y q);
  let ka19 := nmax B (Nat.sub (Nat.add af z) q);
  let ka20 := nmin C (Nat.add (Nat.add y q) o);
  let ka21 := nmax D (Nat.sub J (Nat.add W q));
  let ka22 := nmin E (Nat.sub (Nat.add I q) X);
  let ka23 := nmax F (Nat.sub J (Nat.add j q));
  let ka24 := nmin G (Nat.sub (Nat.add I q) ab);
  let ka25 := nmax H (Nat.sub J q);
  let ka26 := nmin K (Nat.add I q);
  let ka27 := nmax L (Nat.sub (Nat.add af J) q);
  let ka28 := nmin M (Nat.add (Nat.add I q) o);
  let ka29 := nmax N (Nat.sub R (Nat.add j q));
  let ka30 := nmin O (Nat.sub (Nat.add Q q) ab);
  let ka31 := nmax P (Nat.sub R q);
  let ka32 := nmin S (Nat.add Q q);
  let ka33 := nmax T (Nat.sub (Nat.add af R) q);
  let ka34 := nmin U (Nat.add (Nat.add Q q) o);
  let ka35 := nmax V (Nat.sub X q);
  let ka36 := nmin Y (Nat.add W q);
  let ka37 := nmax Z (Nat.sub (Nat.add af X) q);
  let ka38 := nmin aa (Nat.add (Nat.add W q) o);
  let ka39 := nmin ac (Nat.add j q);
  let ka40 := nmax ad (Nat.sub (Nat.add af ab) q);
  let ka41 := nmin ae (Nat.add (Nat.add j q) o);
  let ka42 := nmin ag (Nat.add q o);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 j l ka9 ka10 o ka11 ka12 ka13 ka14 ka15 ka16 ka17 y z ka18 ka19 ka20 ka21 ka22 ka23 ka24 ka25 I J ka26 ka27 ka28 ka29 ka30 ka31 Q R ka32 ka33 ka34 ka35 W X ka36 ka37 ka38 ab ka39 ka40 ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q x) K);
    let kb1 := nmin b (Nat.sub A (Nat.add q H));
    let kb2 := nmax c (Nat.sub (Nat.add q H) S);
    let kb3 := nmin d (Nat.sub K (Nat.add q P));
    let kb4 := nmax e (Nat.sub (Nat.add q P) Y);
    let kb5 := nmin f (Nat.sub S (Nat.add q V));
    let kb6 := nmax g (Nat.sub (Nat.add q V) ac);
    let kb7 := nmin h (Nat.sub Y (Nat.add q i));
    let kb8 := nmin j (Nat.sub ac q);
    let kb9 := nmax q q;
    let kb10 := nmin o (Nat.sub ag q);
    let kb11 := nmax r (Nat.sub (Nat.add q x) S);
    let kb12 := nmin s (Nat.sub A (Nat.add q P));
    let kb13 := nmax t (Nat.sub (Nat.add q x) Y);
    let kb14 := nmin u (Nat.sub A (Nat.add q V));
    let kb15 := nmax v (Nat.sub (Nat.add q x) ac);
    let kb16 := nmin w (Nat.sub A (Nat.add q i));
    let kb17 := nmin y (Nat.sub A q);
    let kb18 := nmax z (Nat.add q x);
    let kb19 := nmax B (Nat.add (Nat.add n q) x);
    let kb20 := nmin C (Nat.sub (Nat.add A ag) q);
    let kb21 := nmax D (Nat.sub (Nat.add q H) Y);
    let kb22 := nmin E (Nat.sub K (Nat.add q V));
    let kb23 := nmax F (Nat.sub (Nat.add q H) ac);
    let kb24 := nmin G (Nat.sub K (Nat.add q i));
    let kb25 := nmin I (Nat.sub K q);
    let kb26 := nmax J (Nat.add q H);
    let kb27 := nmax L (Nat.add (Nat.add n q) H);
    let kb28 := nmin M (Nat.sub (Nat.add K ag) q);
    let kb29 := nmax N (Nat.sub (Nat.add q P) ac);
    let kb30 := nmin O (Nat.sub S (Nat.add q i));
    let kb31 := nmin Q (Nat.sub S q);
    let kb32 := nmax R (Nat.add q P);
    let kb33 := nmax T (Nat.add (Nat.add n q) P);
    let kb34 := nmin U (Nat.sub (Nat.add S ag) q);
    let kb35 := nmin W (Nat.sub Y q);
    let kb36 := nmax X (Nat.add q V);
    let kb37 := nmax Z (Nat.add (Nat.add n q) V);
    let kb38 := nmin aa (Nat.sub (Nat.add Y ag) q);
    let kb39 := nmax ab (Nat.add q i);
    let kb40 := nmax ad (Nat.add (Nat.add n q) i);
    let kb41 := nmin ae (Nat.sub (Nat.add ac ag) q);
    let kb42 := nmax af (Nat.add n q);
    ih p kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 i kb8 kb9 m n kb10 kb11 kb12 kb13 kb14 kb15 kb16 x kb17 kb18 A kb19 kb20 kb21 kb22 kb23 kb24 H kb25 kb26 K kb27 kb28 kb29 kb30 P kb31 kb32 S kb33 kb34 V kb35 kb36 Y kb37 kb38 kb39 ac kb40 kb41 kb42 ag ah) 0 (Nat.beq p 0)

def gsplit6 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add n o) 1;
  let ka0 := nmax a (Nat.sub B (Nat.add K q));
  let ka1 := nmin b (Nat.sub (Nat.add A q) L);
  let ka2 := nmax c (Nat.sub L (Nat.add S q));
  let ka3 := nmin d (Nat.sub (Nat.add K q) T);
  let ka4 := nmax e (Nat.sub T (Nat.add Y q));
  let ka5 := nmin f (Nat.sub (Nat.add S q) Z);
  let ka6 := nmax g (Nat.sub Z (Nat.add ac q));
  let ka7 := nmin h (Nat.sub (Nat.add Y q) ad);
  let ka8 := nmax i (Nat.sub ad (Nat.add m q));
  let ka9 := nmin j (Nat.sub (Nat.add ac q) af);
  let ka10 := nmax l (Nat.sub af q);
  let ka11 := nmin q q;
  let ka12 := nmax r (Nat.sub B (Nat.add S q));
  let ka13 := nmin s (Nat.sub (Nat.add A q) T);
  let ka14 := nmax t (Nat.sub B (Nat.add Y q));
  let ka15 := nmin u (Nat.sub (Nat.add A q) Z);
  let ka16 := nmax v (Nat.sub B (Nat.add ac q));
  let ka17 := nmin w (Nat.sub (Nat.add A q) ad);
  let ka18 := nmax x (Nat.sub B (Nat.add m q));
  let ka19 := nmin y (Nat.sub (Nat.add A q) af);
  let ka20 := nmax z (Nat.sub B q);
  let ka21 := nmin C (Nat.add A q);
  let ka22 := nmax D (Nat.sub L (Nat.add Y q));
  let ka23 := nmin E (Nat.sub (Nat.add K q) Z);
  let ka24 := nmax F (Nat.sub L (Nat.add ac q));
  let ka25 := nmin G (Nat.sub (Nat.add K q) ad);
  let ka26 := nmax H (Nat.sub L (Nat.add m q));
  let ka27 := nmin I (Nat.sub (Nat.add K q) af);
  let ka28 := nmax J (Nat.sub L q);
  let ka29 := nmin M (Nat.add K q);
  let ka30 := nmax N (Nat.sub T (Nat.add ac q));
  let ka31 := nmin O (Nat.sub (Nat.add S q) ad);
  let ka32 := nmax P (Nat.sub T (Nat.add m q));
  let ka33 := nmin Q (Nat.sub (Nat.add S q) af);
  let ka34 := nmax R (Nat.sub T q);
  let ka35 := nmin U (Nat.add S q);
  let ka36 := nmax V (Nat.sub Z (Nat.add m q));
  let ka37 := nmin W (Nat.sub (Nat.add Y q) af);
  let ka38 := nmax X (Nat.sub Z q);
  let ka39 := nmin aa (Nat.add Y q);
  let ka40 := nmax ab (Nat.sub ad q);
  let ka41 := nmin ae (Nat.add ac q);
  let ka42 := nmin ag (Nat.add m q);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 ka9 ka10 m n ka11 ka12 ka13 ka14 ka15 ka16 ka17 ka18 ka19 ka20 A B ka21 ka22 ka23 ka24 ka25 ka26 ka27 ka28 K L ka29 ka30 ka31 ka32 ka33 ka34 S T ka35 ka36 ka37 ka38 Y Z ka39 ka40 ac ad ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q z) M);
    let kb1 := nmin b (Nat.sub C (Nat.add q J));
    let kb2 := nmax c (Nat.sub (Nat.add q J) U);
    let kb3 := nmin d (Nat.sub M (Nat.add q R));
    let kb4 := nmax e (Nat.sub (Nat.add q R) aa);
    let kb5 := nmin f (Nat.sub U (Nat.add q X));
    let kb6 := nmax g (Nat.sub (Nat.add q X) ae);
    let kb7 := nmin h (Nat.sub aa (Nat.add q ab));
    let kb8 := nmax i (Nat.sub (Nat.add q ab) ag);
    let kb9 := nmin j (Nat.sub ae (Nat.add q l));
    let kb10 := nmin m (Nat.sub ag q);
    let kb11 := nmax q q;
    let kb12 := nmax r (Nat.sub (Nat.add q z) U);
    let kb13 := nmin s (Nat.sub C (Nat.add q R));
    let kb14 := nmax t (Nat.sub (Nat.add q z) aa);
    let kb15 := nmin u (Nat.sub C (Nat.add q X));
    let kb16 := nmax v (Nat.sub (Nat.add q z) ae);
    let kb17 := nmin w (Nat.sub C (Nat.add q ab));
    let kb18 := nmax x (Nat.sub (Nat.add q z) ag);
    let kb19 := nmin y (Nat.sub C (Nat.add q l));
    let kb20 := nmin A (Nat.sub C q);
    let kb21 := nmax B (Nat.add q z);
    let kb22 := nmax D (Nat.sub (Nat.add q J) aa);
    let kb23 := nmin E (Nat.sub M (Nat.add q X));
    let kb24 := nmax F (Nat.sub (Nat.add q J) ae);
    let kb25 := nmin G (Nat.sub M (Nat.add q ab));
    let kb26 := nmax H (Nat.sub (Nat.add q J) ag);
    let kb27 := nmin I (Nat.sub M (Nat.add q l));
    let kb28 := nmin K (Nat.sub M q);
    let kb29 := nmax L (Nat.add q J);
    let kb30 := nmax N (Nat.sub (Nat.add q R) ae);
    let kb31 := nmin O (Nat.sub U (Nat.add q ab));
    let kb32 := nmax P (Nat.sub (Nat.add q R) ag);
    let kb33 := nmin Q (Nat.sub U (Nat.add q l));
    let kb34 := nmin S (Nat.sub U q);
    let kb35 := nmax T (Nat.add q R);
    let kb36 := nmax V (Nat.sub (Nat.add q X) ag);
    let kb37 := nmin W (Nat.sub aa (Nat.add q l));
    let kb38 := nmin Y (Nat.sub aa q);
    let kb39 := nmax Z (Nat.add q X);
    let kb40 := nmin ac (Nat.sub ae q);
    let kb41 := nmax ad (Nat.add q ab);
    let kb42 := nmax af (Nat.add q l);
    ih p kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 l kb10 kb11 o kb12 kb13 kb14 kb15 kb16 kb17 kb18 kb19 z kb20 kb21 C kb22 kb23 kb24 kb25 kb26 kb27 J kb28 kb29 M kb30 kb31 kb32 kb33 R kb34 kb35 U kb36 kb37 X kb38 kb39 aa ab kb40 kb41 ae kb42 ag ah) 0 (Nat.beq p 0)

def ssplit02 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add r s) 1;
  let ka0 := nmin b (Nat.sub q c);
  let ka1 := nmin d (Nat.sub q a);
  let ka2 := nmax e (Nat.sub t q);
  let ka3 := nmax g (Nat.sub v (Nat.add q f));
  let ka4 := nmin h (Nat.sub (Nat.add q O) t);
  let ka5 := nmax i (Nat.sub x (Nat.add q O));
  let ka6 := nmin j (Nat.sub (Nat.add q Q) v);
  let ka7 := nmax l (Nat.sub z (Nat.add q Q));
  let ka8 := nmin m (Nat.sub (Nat.add q S) x);
  let ka9 := nmax n (Nat.sub B (Nat.add q S));
  let ka10 := nmin o (Nat.sub (Nat.add q U) z);
  let ka11 := nmin q q;
  let ka12 := nmin u (Nat.add q f);
  let ka13 := nmin w (Nat.add q O);
  let ka14 := nmin y (Nat.add q Q);
  let ka15 := nmin A (Nat.add q S);
  let ka16 := nmin C (Nat.add q U);
  let ka17 := nmax D (Nat.sub (Nat.add t c) q);
  let ka18 := nmin E (Nat.sub (Nat.add q f) a);
  let ka19 := nmax F (Nat.sub (Nat.add v c) q);
  let ka20 := nmin G (Nat.sub (Nat.add q O) a);
  let ka21 := nmax H (Nat.sub (Nat.add x c) q);
  let ka22 := nmin I (Nat.sub (Nat.add q Q) a);
  let ka23 := nmax J (Nat.sub (Nat.add z c) q);
  let ka24 := nmin K (Nat.sub (Nat.add q S) a);
  let ka25 := nmax L (Nat.sub (Nat.add B c) q);
  let ka26 := nmin M (Nat.sub (Nat.add q U) a);
  let ka27 := nmax N (Nat.sub v q);
  let ka28 := nmax P (Nat.sub x q);
  let ka29 := nmax R (Nat.sub z q);
  let ka30 := nmax T (Nat.sub B q);
  let ka31 := nmax V (Nat.sub x (Nat.add q f));
  let ka32 := nmin W (Nat.sub (Nat.add q Q) t);
  let ka33 := nmax X (Nat.sub z (Nat.add q f));
  let ka34 := nmin Y (Nat.sub (Nat.add q S) t);
  let ka35 := nmax Z (Nat.sub B (Nat.add q f));
  let ka36 := nmin aa (Nat.sub (Nat.add q U) t);
  let ka37 := nmax ab (Nat.sub z (Nat.add q O));
  let ka38 := nmin ac (Nat.sub (Nat.add q S) v);
  let ka39 := nmax ad (Nat.sub B (Nat.add q O));
  let ka40 := nmin ae (Nat.sub (Nat.add q U) v);
  let ka41 := nmax af (Nat.sub B (Nat.add q Q));
  let ka42 := nmin ag (Nat.sub (Nat.add q U) x);
  let p := ih pos a ka0 c ka1 ka2 f ka3 ka4 ka5 ka6 ka7 ka8 ka9 ka10 r ka11 t ka12 v ka13 x ka14 z ka15 B ka16 ka17 ka18 ka19 ka20 ka21 ka22 ka23 ka24 ka25 ka26 ka27 O ka28 Q ka29 S ka30 U ka31 ka32 ka33 ka34 ka35 ka36 ka37 ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q d);
    let kb1 := nmax c (Nat.sub q b);
    let kb2 := nmin f (Nat.sub u q);
    let kb3 := nmax g (Nat.sub (Nat.add N q) u);
    let kb4 := nmin h (Nat.sub w (Nat.add e q));
    let kb5 := nmax i (Nat.sub (Nat.add P q) w);
    let kb6 := nmin j (Nat.sub y (Nat.add N q));
    let kb7 := nmax l (Nat.sub (Nat.add R q) y);
    let kb8 := nmin m (Nat.sub A (Nat.add P q));
    let kb9 := nmax n (Nat.sub (Nat.add T q) A);
    let kb10 := nmin o (Nat.sub C (Nat.add R q));
    let kb11 := nmax q q;
    let kb12 := nmax t (Nat.add e q);
    let kb13 := nmax v (Nat.add N q);
    let kb14 := nmax x (Nat.add P q);
    let kb15 := nmax z (Nat.add R q);
    let kb16 := nmax B (Nat.add T q);
    let kb17 := nmax D (Nat.sub (Nat.add e q) b);
    let kb18 := nmin E (Nat.sub (Nat.add d u) q);
    let kb19 := nmax F (Nat.sub (Nat.add N q) b);
    let kb20 := nmin G (Nat.sub (Nat.add d w) q);
    let kb21 := nmax H (Nat.sub (Nat.add P q) b);
    let kb22 := nmin I (Nat.sub (Nat.add d y) q);
    let kb23 := nmax J (Nat.sub (Nat.add R q) b);
    let kb24 := nmin K (Nat.sub (Nat.add d A) q);
    let kb25 := nmax L (Nat.sub (Nat.add T q) b);
    let kb26 := nmin M (Nat.sub (Nat.add d C) q);
    let kb27 := nmin O (Nat.sub w q);
    let kb28 := nmin Q (Nat.sub y q);
    let kb29 := nmin S (Nat.sub A q);
    let kb30 := nmin U (Nat.sub C q);
    let kb31 := nmax V (Nat.sub (Nat.add P q) u);
    let kb32 := nmin W (Nat.sub y (Nat.add e q));
    let kb33 := nmax X (Nat.sub (Nat.add R q) u);
    let kb34 := nmin Y (Nat.sub A (Nat.add e q));
    let kb35 := nmax Z (Nat.sub (Nat.add T q) u);
    let kb36 := nmin aa (Nat.sub C (Nat.add e q));
    let kb37 := nmax ab (Nat.sub (Nat.add R q) w);
    let kb38 := nmin ac (Nat.sub A (Nat.add N q));
    let kb39 := nmax ad (Nat.sub (Nat.add T q) w);
    let kb40 := nmin ae (Nat.sub C (Nat.add N q));
    let kb41 := nmax af (Nat.sub (Nat.add T q) y);
    let kb42 := nmin ag (Nat.sub C (Nat.add P q));
    ih p kb0 b kb1 d e kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 kb11 s kb12 u kb13 w kb14 y kb15 A kb16 C kb17 kb18 kb19 kb20 kb21 kb22 kb23 kb24 kb25 kb26 N kb27 P kb28 R kb29 T kb30 kb31 kb32 kb33 kb34 kb35 kb36 kb37 kb38 kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit03 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add t u) 1;
  let ka0 := nmin b (Nat.sub q D);
  let ka1 := nmax c (Nat.sub (Nat.add r D) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a e));
  let ka3 := nmin f (Nat.sub q r);
  let ka4 := nmax g (Nat.sub v q);
  let ka5 := nmax i (Nat.sub x (Nat.add q h));
  let ka6 := nmin j (Nat.sub (Nat.add q W) v);
  let ka7 := nmax l (Nat.sub z (Nat.add q W));
  let ka8 := nmin m (Nat.sub (Nat.add q Y) x);
  let ka9 := nmax n (Nat.sub B (Nat.add q Y));
  let ka10 := nmin o (Nat.sub (Nat.add q aa) z);
  let ka11 := nmin s (Nat.sub q e);
  let ka12 := nmin q q;
  let ka13 := nmin w (Nat.add q h);
  let ka14 := nmin y (Nat.add q W);
  let ka15 := nmin A (Nat.add q Y);
  let ka16 := nmin C (Nat.add q aa);
  let ka17 := nmin E (Nat.sub q a);
  let ka18 := nmax F (Nat.sub (Nat.add v D) q);
  let ka19 := nmin G (Nat.sub (Nat.add q h) a);
  let ka20 := nmax H (Nat.sub (Nat.add x D) q);
  let ka21 := nmin I (Nat.sub (Nat.add q W) a);
  let ka22 := nmax J (Nat.sub (Nat.add z D) q);
  let ka23 := nmin K (Nat.sub (Nat.add q Y) a);
  let ka24 := nmax L (Nat.sub (Nat.add B D) q);
  let ka25 := nmin M (Nat.sub (Nat.add q aa) a);
  let ka26 := nmax N (Nat.sub (Nat.add v e) q);
  let ka27 := nmin O (Nat.sub (Nat.add q h) r);
  let ka28 := nmax P (Nat.sub (Nat.add x e) q);
  let ka29 := nmin Q (Nat.sub (Nat.add q W) r);
  let ka30 := nmax R (Nat.sub (Nat.add z e) q);
  let ka31 := nmin S (Nat.sub (Nat.add q Y) r);
  let ka32 := nmax T (Nat.sub (Nat.add B e) q);
  let ka33 := nmin U (Nat.sub (Nat.add q aa) r);
  let ka34 := nmax V (Nat.sub x q);
  let ka35 := nmax X (Nat.sub z q);
  let ka36 := nmax Z (Nat.sub B q);
  let ka37 := nmax ab (Nat.sub z (Nat.add q h));
  let ka38 := nmin ac (Nat.sub (Nat.add q Y) v);
  let ka39 := nmax ad (Nat.sub B (Nat.add q h));
  let ka40 := nmin ae (Nat.sub (Nat.add q aa) v);
  let ka41 := nmax af (Nat.sub B (Nat.add q W));
  let ka42 := nmin ag (Nat.sub (Nat.add q aa) x);
  let p := ih pos a ka0 ka1 ka2 e ka3 ka4 h ka5 ka6 ka7 ka8 ka9 ka10 r ka11 t ka12 v ka13 x ka14 z ka15 B ka16 D ka17 ka18 ka19 ka20 ka21 ka22 ka23 ka24 ka25 ka26 ka27 ka28 ka29 ka30 ka31 ka32 ka33 ka34 W ka35 Y ka36 aa ka37 ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q E);
    let kb1 := nmax c (Nat.sub q (Nat.add f b));
    let kb2 := nmin d (Nat.sub (Nat.add E s) q);
    let kb3 := nmax e (Nat.sub q s);
    let kb4 := nmin h (Nat.sub w q);
    let kb5 := nmax i (Nat.sub (Nat.add V q) w);
    let kb6 := nmin j (Nat.sub y (Nat.add g q));
    let kb7 := nmax l (Nat.sub (Nat.add X q) y);
    let kb8 := nmin m (Nat.sub A (Nat.add V q));
    let kb9 := nmax n (Nat.sub (Nat.add Z q) A);
    let kb10 := nmin o (Nat.sub C (Nat.add X q));
    let kb11 := nmax r (Nat.sub q f);
    let kb12 := nmax q q;
    let kb13 := nmax v (Nat.add g q);
    let kb14 := nmax x (Nat.add V q);
    let kb15 := nmax z (Nat.add X q);
    let kb16 := nmax B (Nat.add Z q);
    let kb17 := nmax D (Nat.sub q b);
    let kb18 := nmax F (Nat.sub (Nat.add g q) b);
    let kb19 := nmin G (Nat.sub (Nat.add E w) q);
    let kb20 := nmax H (Nat.sub (Nat.add V q) b);
    let kb21 := nmin I (Nat.sub (Nat.add E y) q);
    let kb22 := nmax J (Nat.sub (Nat.add X q) b);
    let kb23 := nmin K (Nat.sub (Nat.add E A) q);
    let kb24 := nmax L (Nat.sub (Nat.add Z q) b);
    let kb25 := nmin M (Nat.sub (Nat.add E C) q);
    let kb26 := nmax N (Nat.sub (Nat.add g q) s);
    let kb27 := nmin O (Nat.sub (Nat.add f w) q);
    let kb28 := nmax P (Nat.sub (Nat.add V q) s);
    let kb29 := nmin Q (Nat.sub (Nat.add f y) q);
    let kb30 := nmax R (Nat.sub (Nat.add X q) s);
    let kb31 := nmin S (Nat.sub (Nat.add f A) q);
    let kb32 := nmax T (Nat.sub (Nat.add Z q) s);
    let kb33 := nmin U (Nat.sub (Nat.add f C) q);
    let kb34 := nmin W (Nat.sub y q);
    let kb35 := nmin Y (Nat.sub A q);
    let kb36 := nmin aa (Nat.sub C q);
    let kb37 := nmax ab (Nat.sub (Nat.add X q) w);
    let kb38 := nmin ac (Nat.sub A (Nat.add g q));
    let kb39 := nmax ad (Nat.sub (Nat.add Z q) w);
    let kb40 := nmin ae (Nat.sub C (Nat.add g q));
    let kb41 := nmax af (Nat.sub (Nat.add Z q) y);
    let kb42 := nmin ag (Nat.sub C (Nat.add V q));
    ih p kb0 b kb1 kb2 kb3 f g kb4 kb5 kb6 kb7 kb8 kb9 kb10 kb11 s kb12 u kb13 w kb14 y kb15 A kb16 C kb17 E kb18 kb19 kb20 kb21 kb22 kb23 kb24 kb25 kb26 kb27 kb28 kb29 kb30 kb31 kb32 kb33 V kb34 X kb35 Z kb36 kb37 kb38 kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit04 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add v w) 1;
  let ka0 := nmin b (Nat.sub q F);
  let ka1 := nmax c (Nat.sub (Nat.add r F) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a N));
  let ka3 := nmax e (Nat.sub (Nat.add t N) q);
  let ka4 := nmin f (Nat.sub q (Nat.add r g));
  let ka5 := nmin h (Nat.sub q t);
  let ka6 := nmax i (Nat.sub x q);
  let ka7 := nmax l (Nat.sub z (Nat.add q j));
  let ka8 := nmin m (Nat.sub (Nat.add q ac) x);
  let ka9 := nmax n (Nat.sub B (Nat.add q ac));
  let ka10 := nmin o (Nat.sub (Nat.add q ae) z);
  let ka11 := nmin s (Nat.sub q N);
  let ka12 := nmin u (Nat.sub q g);
  let ka13 := nmin q q;
  let ka14 := nmin y (Nat.add q j);
  let ka15 := nmin A (Nat.add q ac);
  let ka16 := nmin C (Nat.add q ae);
  let ka17 := nmax D (Nat.sub (Nat.add t F) q);
  let ka18 := nmin E (Nat.sub q (Nat.add a g));
  let ka19 := nmin G (Nat.sub q a);
  let ka20 := nmax H (Nat.sub (Nat.add x F) q);
  let ka21 := nmin I (Nat.sub (Nat.add q j) a);
  let ka22 := nmax J (Nat.sub (Nat.add z F) q);
  let ka23 := nmin K (Nat.sub (Nat.add q ac) a);
  let ka24 := nmax L (Nat.sub (Nat.add B F) q);
  let ka25 := nmin M (Nat.sub (Nat.add q ae) a);
  let ka26 := nmin O (Nat.sub q r);
  let ka27 := nmax P (Nat.sub (Nat.add x N) q);
  let ka28 := nmin Q (Nat.sub (Nat.add q j) r);
  let ka29 := nmax R (Nat.sub (Nat.add z N) q);
  let ka30 := nmin S (Nat.sub (Nat.add q ac) r);
  let ka31 := nmax T (Nat.sub (Nat.add B N) q);
  let ka32 := nmin U (Nat.sub (Nat.add q ae) r);
  let ka33 := nmax V (Nat.sub (Nat.add x g) q);
  let ka34 := nmin W (Nat.sub (Nat.add q j) t);
  let ka35 := nmax X (Nat.sub (Nat.add z g) q);
  let ka36 := nmin Y (Nat.sub (Nat.add q ac) t);
  let ka37 := nmax Z (Nat.sub (Nat.add B g) q);
  let ka38 := nmin aa (Nat.sub (Nat.add q ae) t);
  let ka39 := nmax ab (Nat.sub z q);
  let ka40 := nmax ad (Nat.sub B q);
  let ka41 := nmax af (Nat.sub B (Nat.add q j));
  let ka42 := nmin ag (Nat.sub (Nat.add q ae) x);
  let p := ih pos a ka0 ka1 ka2 ka3 ka4 g ka5 ka6 j ka7 ka8 ka9 ka10 r ka11 t ka12 v ka13 x ka14 z ka15 B ka16 ka17 ka18 F ka19 ka20 ka21 ka22 ka23 ka24 ka25 N ka26 ka27 ka28 ka29 ka30 ka31 ka32 ka33 ka34 ka35 ka36 ka37 ka38 ka39 ac ka40 ae ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q G);
    let kb1 := nmax c (Nat.sub q (Nat.add O b));
    let kb2 := nmin d (Nat.sub (Nat.add G s) q);
    let kb3 := nmax e (Nat.sub q (Nat.add h s));
    let kb4 := nmin f (Nat.sub (Nat.add O u) q);
    let kb5 := nmax g (Nat.sub q u);
    let kb6 := nmin j (Nat.sub y q);
    let kb7 := nmax l (Nat.sub (Nat.add ab q) y);
    let kb8 := nmin m (Nat.sub A (Nat.add i q));
    let kb9 := nmax n (Nat.sub (Nat.add ad q) A);
    let kb10 := nmin o (Nat.sub C (Nat.add ab q));
    let kb11 := nmax r (Nat.sub q O);
    let kb12 := nmax t (Nat.sub q h);
    let kb13 := nmax q q;
    let kb14 := nmax x (Nat.add i q);
    let kb15 := nmax z (Nat.add ab q);
    let kb16 := nmax B (Nat.add ad q);
    let kb17 := nmax D (Nat.sub q (Nat.add h b));
    let kb18 := nmin E (Nat.sub (Nat.add G u) q);
    let kb19 := nmax F (Nat.sub q b);
    let kb20 := nmax H (Nat.sub (Nat.add i q) b);
    let kb21 := nmin I (Nat.sub (Nat.add G y) q);
    let kb22 := nmax J (Nat.sub (Nat.add ab q) b);
    let kb23 := nmin K (Nat.sub (Nat.add G A) q);
    let kb24 := nmax L (Nat.sub (Nat.add ad q) b);
    let kb25 := nmin M (Nat.sub (Nat.add G C) q);
    let kb26 := nmax N (Nat.sub q s);
    let kb27 := nmax P (Nat.sub (Nat.add i q) s);
    let kb28 := nmin Q (Nat.sub (Nat.add O y) q);
    let kb29 := nmax R (Nat.sub (Nat.add ab q) s);
    let kb30 := nmin S (Nat.sub (Nat.add O A) q);
    let kb31 := nmax T (Nat.sub (Nat.add ad q) s);
    let kb32 := nmin U (Nat.sub (Nat.add O C) q);
    let kb33 := nmax V (Nat.sub (Nat.add i q) u);
    let kb34 := nmin W (Nat.sub (Nat.add h y) q);
    let kb35 := nmax X (Nat.sub (Nat.add ab q) u);
    let kb36 := nmin Y (Nat.sub (Nat.add h A) q);
    let kb37 := nmax Z (Nat.sub (Nat.add ad q) u);
    let kb38 := nmin aa (Nat.sub (Nat.add h C) q);
    let kb39 := nmin ac (Nat.sub A q);
    let kb40 := nmin ae (Nat.sub C q);
    let kb41 := nmax af (Nat.sub (Nat.add ad q) y);
    let kb42 := nmin ag (Nat.sub C (Nat.add i q));
    ih p kb0 b kb1 kb2 kb3 kb4 kb5 h i kb6 kb7 kb8 kb9 kb10 kb11 s kb12 u kb13 w kb14 y kb15 A kb16 C kb17 kb18 kb19 G kb20 kb21 kb22 kb23 kb24 kb25 kb26 O kb27 kb28 kb29 kb30 kb31 kb32 kb33 kb34 kb35 kb36 kb37 kb38 ab kb39 ad kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit05 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add x y) 1;
  let ka0 := nmin b (Nat.sub q H);
  let ka1 := nmax c (Nat.sub (Nat.add r H) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a P));
  let ka3 := nmax e (Nat.sub (Nat.add t P) q);
  let ka4 := nmin f (Nat.sub q (Nat.add r V));
  let ka5 := nmax g (Nat.sub (Nat.add v V) q);
  let ka6 := nmin h (Nat.sub q (Nat.add t i));
  let ka7 := nmin j (Nat.sub q v);
  let ka8 := nmax l (Nat.sub z q);
  let ka9 := nmax n (Nat.sub B (Nat.add q m));
  let ka10 := nmin o (Nat.sub (Nat.add q ag) z);
  let ka11 := nmin s (Nat.sub q P);
  let ka12 := nmin u (Nat.sub q V);
  let ka13 := nmin w (Nat.sub q i);
  let ka14 := nmin q q;
  let ka15 := nmin A (Nat.add q m);
  let ka16 := nmin C (Nat.add q ag);
  let ka17 := nmax D (Nat.sub (Nat.add t H) q);
  let ka18 := nmin E (Nat.sub q (Nat.add a V));
  let ka19 := nmax F (Nat.sub (Nat.add v H) q);
  let ka20 := nmin G (Nat.sub q (Nat.add a i));
  let ka21 := nmin I (Nat.sub q a);
  let ka22 := nmax J (Nat.sub (Nat.add z H) q);
  let ka23 := nmin K (Nat.sub (Nat.add q m) a);
  let ka24 := nmax L (Nat.sub (Nat.add B H) q);
  let ka25 := nmin M (Nat.sub (Nat.add q ag) a);
  let ka26 := nmax N (Nat.sub (Nat.add v P) q);
  let ka27 := nmin O (Nat.sub q (Nat.add r i));
  let ka28 := nmin Q (Nat.sub q r);
  let ka29 := nmax R (Nat.sub (Nat.add z P) q);
  let ka30 := nmin S (Nat.sub (Nat.add q m) r);
  let ka31 := nmax T (Nat.sub (Nat.add B P) q);
  let ka32 := nmin U (Nat.sub (Nat.add q ag) r);
  let ka33 := nmin W (Nat.sub q t);
  let ka34 := nmax X (Nat.sub (Nat.add z V) q);
  let ka35 := nmin Y (Nat.sub (Nat.add q m) t);
  let ka36 := nmax Z (Nat.sub (Nat.add B V) q);
  let ka37 := nmin aa (Nat.sub (Nat.add q ag) t);
  let ka38 := nmax ab (Nat.sub (Nat.add z i) q);
  let ka39 := nmin ac (Nat.sub (Nat.add q m) v);
  let ka40 := nmax ad (Nat.sub (Nat.add B i) q);
  let ka41 := nmin ae (Nat.sub (Nat.add q ag) v);
  let ka42 := nmax af (Nat.sub B q);
  let p := ih pos a ka0 ka1 ka2 ka3 ka4 ka5 ka6 i ka7 ka8 m ka9 ka10 r ka11 t ka12 v ka13 x ka14 z ka15 B ka16 ka17 ka18 ka19 ka20 H ka21 ka22 ka23 ka24 ka25 ka26 ka27 P ka28 ka29 ka30 ka31 ka32 V ka33 ka34 ka35 ka36 ka37 ka38 ka39 ka40 ka41 ka42 ag ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q I);
    let kb1 := nmax c (Nat.sub q (Nat.add Q b));
    let kb2 := nmin d (Nat.sub (Nat.add I s) q);
    let kb3 := nmax e (Nat.sub q (Nat.add W s));
    let kb4 := nmin f (Nat.sub (Nat.add Q u) q);
    let kb5 := nmax g (Nat.sub q (Nat.add j u));
    let kb6 := nmin h (Nat.sub (Nat.add W w) q);
    let kb7 := nmax i (Nat.sub q w);
    let kb8 := nmin m (Nat.sub A q);
    let kb9 := nmax n (Nat.sub (Nat.add af q) A);
    let kb10 := nmin o (Nat.sub C (Nat.add l q));
    let kb11 := nmax r (Nat.sub q Q);
    let kb12 := nmax t (Nat.sub q W);
    let kb13 := nmax v (Nat.sub q j);
    let kb14 := nmax q q;
    let kb15 := nmax z (Nat.add l q);
    let kb16 := nmax B (Nat.add af q);
    let kb17 := nmax D (Nat.sub q (Nat.add W b));
    let kb18 := nmin E (Nat.sub (Nat.add I u) q);
    let kb19 := nmax F (Nat.sub q (Nat.add j b));
    let kb20 := nmin G (Nat.sub (Nat.add I w) q);
    let kb21 := nmax H (Nat.sub q b);
    let kb22 := nmax J (Nat.sub (Nat.add l q) b);
    let kb23 := nmin K (Nat.sub (Nat.add I A) q);
    let kb24 := nmax L (Nat.sub (Nat.add af q) b);
    let kb25 := nmin M (Nat.sub (Nat.add I C) q);
    let kb26 := nmax N (Nat.sub q (Nat.add j s));
    let kb27 := nmin O (Nat.sub (Nat.add Q w) q);
    let kb28 := nmax P (Nat.sub q s);
    let kb29 := nmax R (Nat.sub (Nat.add l q) s);
    let kb30 := nmin S (Nat.sub (Nat.add Q A) q);
    let kb31 := nmax T (Nat.sub (Nat.add af q) s);
    let kb32 := nmin U (Nat.sub (Nat.add Q C) q);
    let kb33 := nmax V (Nat.sub q u);
    let kb34 := nmax X (Nat.sub (Nat.add l q) u);
    let kb35 := nmin Y (Nat.sub (Nat.add W A) q);
    let kb36 := nmax Z (Nat.sub (Nat.add af q) u);
    let kb37 := nmin aa (Nat.sub (Nat.add W C) q);
    let kb38 := nmax ab (Nat.sub (Nat.add l q) w);
    let kb39 := nmin ac (Nat.sub (Nat.add j A) q);
    let kb40 := nmax ad (Nat.sub (Nat.add af q) w);
    let kb41 := nmin ae (Nat.sub (Nat.add j C) q);
    let kb42 := nmin ag (Nat.sub C q);
    ih p kb0 b kb1 kb2 kb3 kb4 kb5 kb6 kb7 j l kb8 kb9 kb10 kb11 s kb12 u kb13 w kb14 y kb15 A kb16 C kb17 kb18 kb19 kb20 kb21 I kb22 kb23 kb24 kb25 kb26 kb27 kb28 Q kb29 kb30 kb31 kb32 kb33 W kb34 kb35 kb36 kb37 kb38 kb39 kb40 kb41 af kb42 ah) 0 (Nat.beq p 0)

def ssplit06 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add z A) 1;
  let ka0 := nmin b (Nat.sub q J);
  let ka1 := nmax c (Nat.sub (Nat.add r J) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a R));
  let ka3 := nmax e (Nat.sub (Nat.add t R) q);
  let ka4 := nmin f (Nat.sub q (Nat.add r X));
  let ka5 := nmax g (Nat.sub (Nat.add v X) q);
  let ka6 := nmin h (Nat.sub q (Nat.add t ab));
  let ka7 := nmax i (Nat.sub (Nat.add x ab) q);
  let ka8 := nmin j (Nat.sub q (Nat.add v l));
  let ka9 := nmin m (Nat.sub q x);
  let ka10 := nmax n (Nat.sub B q);
  let ka11 := nmin s (Nat.sub q R);
  let ka12 := nmin u (Nat.sub q X);
  let ka13 := nmin w (Nat.sub q ab);
  let ka14 := nmin y (Nat.sub q l);
  let ka15 := nmin q q;
  let ka16 := nmin C (Nat.add q o);
  let ka17 := nmax D (Nat.sub (Nat.add t J) q);
  let ka18 := nmin E (Nat.sub q (Nat.add a X));
  let ka19 := nmax F (Nat.sub (Nat.add v J) q);
  let ka20 := nmin G (Nat.sub q (Nat.add a ab));
  let ka21 := nmax H (Nat.sub (Nat.add x J) q);
  let ka22 := nmin I (Nat.sub q (Nat.add a l));
  let ka23 := nmin K (Nat.sub q a);
  let ka24 := nmax L (Nat.sub (Nat.add B J) q);
  let ka25 := nmin M (Nat.sub (Nat.add q o) a);
  let ka26 := nmax N (Nat.sub (Nat.add v R) q);
  let ka27 := nmin O (Nat.sub q (Nat.add r ab));
  let ka28 := nmax P (Nat.sub (Nat.add x R) q);
  let ka29 := nmin Q (Nat.sub q (Nat.add r l));
  let ka30 := nmin S (Nat.sub q r);
  let ka31 := nmax T (Nat.sub (Nat.add B R) q);
  let ka32 := nmin U (Nat.sub (Nat.add q o) r);
  let ka33 := nmax V (Nat.sub (Nat.add x X) q);
  let ka34 := nmin W (Nat.sub q (Nat.add t l));
  let ka35 := nmin Y (Nat.sub q t);
  let ka36 := nmax Z (Nat.sub (Nat.add B X) q);
  let ka37 := nmin aa (Nat.sub (Nat.add q o) t);
  let ka38 := nmin ac (Nat.sub q v);
  let ka39 := nmax ad (Nat.sub (Nat.add B ab) q);
  let ka40 := nmin ae (Nat.sub (Nat.add q o) v);
  let ka41 := nmax af (Nat.sub (Nat.add B l) q);
  let ka42 := nmin ag (Nat.sub (Nat.add q o) x);
  let p := ih pos a ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 l ka9 ka10 o r ka11 t ka12 v ka13 x ka14 z ka15 B ka16 ka17 ka18 ka19 ka20 ka21 ka22 J ka23 ka24 ka25 ka26 ka27 ka28 ka29 R ka30 ka31 ka32 ka33 ka34 X ka35 ka36 ka37 ab ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q K);
    let kb1 := nmax c (Nat.sub q (Nat.add S b));
    let kb2 := nmin d (Nat.sub (Nat.add K s) q);
    let kb3 := nmax e (Nat.sub q (Nat.add Y s));
    let kb4 := nmin f (Nat.sub (Nat.add S u) q);
    let kb5 := nmax g (Nat.sub q (Nat.add ac u));
    let kb6 := nmin h (Nat.sub (Nat.add Y w) q);
    let kb7 := nmax i (Nat.sub q (Nat.add m w));
    let kb8 := nmin j (Nat.sub (Nat.add ac y) q);
    let kb9 := nmax l (Nat.sub q y);
    let kb10 := nmin o (Nat.sub C q);
    let kb11 := nmax r (Nat.sub q S);
    let kb12 := nmax t (Nat.sub q Y);
    let kb13 := nmax v (Nat.sub q ac);
    let kb14 := nmax x (Nat.sub q m);
    let kb15 := nmax q q;
    let kb16 := nmax B (Nat.add n q);
    let kb17 := nmax D (Nat.sub q (Nat.add Y b));
    let kb18 := nmin E (Nat.sub (Nat.add K u) q);
    let kb19 := nmax F (Nat.sub q (Nat.add ac b));
    let kb20 := nmin G (Nat.sub (Nat.add K w) q);
    let kb21 := nmax H (Nat.sub q (Nat.add m b));
    let kb22 := nmin I (Nat.sub (Nat.add K y) q);
    let kb23 := nmax J (Nat.sub q b);
    let kb24 := nmax L (Nat.sub (Nat.add n q) b);
    let kb25 := nmin M (Nat.sub (Nat.add K C) q);
    let kb26 := nmax N (Nat.sub q (Nat.add ac s));
    let kb27 := nmin O (Nat.sub (Nat.add S w) q);
    let kb28 := nmax P (Nat.sub q (Nat.add m s));
    let kb29 := nmin Q (Nat.sub (Nat.add S y) q);
    let kb30 := nmax R (Nat.sub q s);
    let kb31 := nmax T (Nat.sub (Nat.add n q) s);
    let kb32 := nmin U (Nat.sub (Nat.add S C) q);
    let kb33 := nmax V (Nat.sub q (Nat.add m u));
    let kb34 := nmin W (Nat.sub (Nat.add Y y) q);
    let kb35 := nmax X (Nat.sub q u);
    let kb36 := nmax Z (Nat.sub (Nat.add n q) u);
    let kb37 := nmin aa (Nat.sub (Nat.add Y C) q);
    let kb38 := nmax ab (Nat.sub q w);
    let kb39 := nmax ad (Nat.sub (Nat.add n q) w);
    let kb40 := nmin ae (Nat.sub (Nat.add ac C) q);
    let kb41 := nmax af (Nat.sub (Nat.add n q) y);
    let kb42 := nmin ag (Nat.sub (Nat.add m C) q);
    ih p kb0 b kb1 kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 m n kb10 kb11 s kb12 u kb13 w kb14 y kb15 A kb16 C kb17 kb18 kb19 kb20 kb21 kb22 kb23 K kb24 kb25 kb26 kb27 kb28 kb29 kb30 S kb31 kb32 kb33 kb34 kb35 Y kb36 kb37 kb38 ac kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit07 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add B C) 1;
  let ka0 := nmin b (Nat.sub q L);
  let ka1 := nmax c (Nat.sub (Nat.add r L) q);
  let ka2 := nmin d (Nat.sub q (Nat.add a T));
  let ka3 := nmax e (Nat.sub (Nat.add t T) q);
  let ka4 := nmin f (Nat.sub q (Nat.add r Z));
  let ka5 := nmax g (Nat.sub (Nat.add v Z) q);
  let ka6 := nmin h (Nat.sub q (Nat.add t ad));
  let ka7 := nmax i (Nat.sub (Nat.add x ad) q);
  let ka8 := nmin j (Nat.sub q (Nat.add v af));
  let ka9 := nmax l (Nat.sub (Nat.add z af) q);
  let ka10 := nmin m (Nat.sub q (Nat.add x n));
  let ka11 := nmin o (Nat.sub q z);
  let ka12 := nmin s (Nat.sub q T);
  let ka13 := nmin u (Nat.sub q Z);
  let ka14 := nmin w (Nat.sub q ad);
  let ka15 := nmin y (Nat.sub q af);
  let ka16 := nmin A (Nat.sub q n);
  let ka17 := nmin q q;
  let ka18 := nmax D (Nat.sub (Nat.add t L) q);
  let ka19 := nmin E (Nat.sub q (Nat.add a Z));
  let ka20 := nmax F (Nat.sub (Nat.add v L) q);
  let ka21 := nmin G (Nat.sub q (Nat.add a ad));
  let ka22 := nmax H (Nat.sub (Nat.add x L) q);
  let ka23 := nmin I (Nat.sub q (Nat.add a af));
  let ka24 := nmax J (Nat.sub (Nat.add z L) q);
  let ka25 := nmin K (Nat.sub q (Nat.add a n));
  let ka26 := nmin M (Nat.sub q a);
  let ka27 := nmax N (Nat.sub (Nat.add v T) q);
  let ka28 := nmin O (Nat.sub q (Nat.add r ad));
  let ka29 := nmax P (Nat.sub (Nat.add x T) q);
  let ka30 := nmin Q (Nat.sub q (Nat.add r af));
  let ka31 := nmax R (Nat.sub (Nat.add z T) q);
  let ka32 := nmin S (Nat.sub q (Nat.add r n));
  let ka33 := nmin U (Nat.sub q r);
  let ka34 := nmax V (Nat.sub (Nat.add x Z) q);
  let ka35 := nmin W (Nat.sub q (Nat.add t af));
  let ka36 := nmax X (Nat.sub (Nat.add z Z) q);
  let ka37 := nmin Y (Nat.sub q (Nat.add t n));
  let ka38 := nmin aa (Nat.sub q t);
  let ka39 := nmax ab (Nat.sub (Nat.add z ad) q);
  let ka40 := nmin ac (Nat.sub q (Nat.add v n));
  let ka41 := nmin ae (Nat.sub q v);
  let ka42 := nmin ag (Nat.sub q x);
  let p := ih pos a ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 ka9 ka10 n ka11 r ka12 t ka13 v ka14 x ka15 z ka16 B ka17 ka18 ka19 ka20 ka21 ka22 ka23 ka24 ka25 L ka26 ka27 ka28 ka29 ka30 ka31 ka32 T ka33 ka34 ka35 ka36 ka37 Z ka38 ka39 ka40 ad ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub q M);
    let kb1 := nmax c (Nat.sub q (Nat.add U b));
    let kb2 := nmin d (Nat.sub (Nat.add M s) q);
    let kb3 := nmax e (Nat.sub q (Nat.add aa s));
    let kb4 := nmin f (Nat.sub (Nat.add U u) q);
    let kb5 := nmax g (Nat.sub q (Nat.add ae u));
    let kb6 := nmin h (Nat.sub (Nat.add aa w) q);
    let kb7 := nmax i (Nat.sub q (Nat.add ag w));
    let kb8 := nmin j (Nat.sub (Nat.add ae y) q);
    let kb9 := nmax l (Nat.sub q (Nat.add o y));
    let kb10 := nmin m (Nat.sub (Nat.add ag A) q);
    let kb11 := nmax n (Nat.sub q A);
    let kb12 := nmax r (Nat.sub q U);
    let kb13 := nmax t (Nat.sub q aa);
    let kb14 := nmax v (Nat.sub q ae);
    let kb15 := nmax x (Nat.sub q ag);
    let kb16 := nmax z (Nat.sub q o);
    let kb17 := nmax q q;
    let kb18 := nmax D (Nat.sub q (Nat.add aa b));
    let kb19 := nmin E (Nat.sub (Nat.add M u) q);
    let kb20 := nmax F (Nat.sub q (Nat.add ae b));
    let kb21 := nmin G (Nat.sub (Nat.add M w) q);
    let kb22 := nmax H (Nat.sub q (Nat.add ag b));
    let kb23 := nmin I (Nat.sub (Nat.add M y) q);
    let kb24 := nmax J (Nat.sub q (Nat.add o b));
    let kb25 := nmin K (Nat.sub (Nat.add M A) q);
    let kb26 := nmax L (Nat.sub q b);
    let kb27 := nmax N (Nat.sub q (Nat.add ae s));
    let kb28 := nmin O (Nat.sub (Nat.add U w) q);
    let kb29 := nmax P (Nat.sub q (Nat.add ag s));
    let kb30 := nmin Q (Nat.sub (Nat.add U y) q);
    let kb31 := nmax R (Nat.sub q (Nat.add o s));
    let kb32 := nmin S (Nat.sub (Nat.add U A) q);
    let kb33 := nmax T (Nat.sub q s);
    let kb34 := nmax V (Nat.sub q (Nat.add ag u));
    let kb35 := nmin W (Nat.sub (Nat.add aa y) q);
    let kb36 := nmax X (Nat.sub q (Nat.add o u));
    let kb37 := nmin Y (Nat.sub (Nat.add aa A) q);
    let kb38 := nmax Z (Nat.sub q u);
    let kb39 := nmax ab (Nat.sub q (Nat.add o w));
    let kb40 := nmin ac (Nat.sub (Nat.add ae A) q);
    let kb41 := nmax ad (Nat.sub q w);
    let kb42 := nmax af (Nat.sub q y);
    ih p kb0 b kb1 kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 kb11 o kb12 s kb13 u kb14 w kb15 y kb16 A kb17 C kb18 kb19 kb20 kb21 kb22 kb23 kb24 kb25 kb26 M kb27 kb28 kb29 kb30 kb31 kb32 kb33 U kb34 kb35 kb36 kb37 kb38 aa kb39 kb40 kb41 ae kb42 ag ah) 0 (Nat.beq p 0)

def ssplit13 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add D E) 1;
  let ka0 := nmax a (Nat.sub t q);
  let ka1 := nmin d (Nat.sub q e);
  let ka2 := nmin f (Nat.sub q c);
  let ka3 := nmax g (Nat.sub F q);
  let ka4 := nmax i (Nat.sub H (Nat.add q h));
  let ka5 := nmin j (Nat.sub (Nat.add q W) F);
  let ka6 := nmax l (Nat.sub J (Nat.add q W));
  let ka7 := nmin m (Nat.sub (Nat.add q Y) H);
  let ka8 := nmax n (Nat.sub L (Nat.add q Y));
  let ka9 := nmin o (Nat.sub (Nat.add q aa) J);
  let ka10 := nmax r (Nat.sub (Nat.add c t) q);
  let ka11 := nmin s (Nat.sub (Nat.add b q) e);
  let ka12 := nmin u (Nat.add b q);
  let ka13 := nmax v (Nat.sub (Nat.add F t) q);
  let ka14 := nmin w (Nat.add (Nat.add b q) h);
  let ka15 := nmax x (Nat.sub (Nat.add H t) q);
  let ka16 := nmin y (Nat.add (Nat.add b q) W);
  let ka17 := nmax z (Nat.sub (Nat.add J t) q);
  let ka18 := nmin A (Nat.add (Nat.add b q) Y);
  let ka19 := nmax B (Nat.sub (Nat.add L t) q);
  let ka20 := nmin C (Nat.add (Nat.add b q) aa);
  let ka21 := nmin q q;
  let ka22 := nmin G (Nat.add q h);
  let ka23 := nmin I (Nat.add q W);
  let ka24 := nmin K (Nat.add q Y);
  let ka25 := nmin M (Nat.add q aa);
  let ka26 := nmax N (Nat.sub (Nat.add F e) q);
  let ka27 := nmin O (Nat.sub (Nat.add q h) c);
  let ka28 := nmax P (Nat.sub (Nat.add H e) q);
  let ka29 := nmin Q (Nat.sub (Nat.add q W) c);
  let ka30 := nmax R (Nat.sub (Nat.add J e) q);
  let ka31 := nmin S (Nat.sub (Nat.add q Y) c);
  let ka32 := nmax T (Nat.sub (Nat.add L e) q);
  let ka33 := nmin U (Nat.sub (Nat.add q aa) c);
  let ka34 := nmax V (Nat.sub H q);
  let ka35 := nmax X (Nat.sub J q);
  let ka36 := nmax Z (Nat.sub L q);
  let ka37 := nmax ab (Nat.sub J (Nat.add q h));
  let ka38 := nmin ac (Nat.sub (Nat.add q Y) F);
  let ka39 := nmax ad (Nat.sub L (Nat.add q h));
  let ka40 := nmin ae (Nat.sub (Nat.add q aa) F);
  let ka41 := nmax af (Nat.sub L (Nat.add q W));
  let ka42 := nmin ag (Nat.sub (Nat.add q aa) H);
  let p := ih pos ka0 b c ka1 e ka2 ka3 h ka4 ka5 ka6 ka7 ka8 ka9 ka10 ka11 t ka12 ka13 ka14 ka15 ka16 ka17 ka18 ka19 ka20 D ka21 F ka22 H ka23 J ka24 L ka25 ka26 ka27 ka28 ka29 ka30 ka31 ka32 ka33 ka34 W ka35 Y ka36 aa ka37 ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub u q);
    let kb1 := nmax c (Nat.sub q f);
    let kb2 := nmax e (Nat.sub q d);
    let kb3 := nmin h (Nat.sub G q);
    let kb4 := nmax i (Nat.sub (Nat.add V q) G);
    let kb5 := nmin j (Nat.sub I (Nat.add g q));
    let kb6 := nmax l (Nat.sub (Nat.add X q) I);
    let kb7 := nmin m (Nat.sub K (Nat.add V q));
    let kb8 := nmax n (Nat.sub (Nat.add Z q) K);
    let kb9 := nmin o (Nat.sub M (Nat.add X q));
    let kb10 := nmax r (Nat.sub (Nat.add q a) f);
    let kb11 := nmin s (Nat.sub (Nat.add u d) q);
    let kb12 := nmax t (Nat.add q a);
    let kb13 := nmax v (Nat.add (Nat.add g q) a);
    let kb14 := nmin w (Nat.sub (Nat.add u G) q);
    let kb15 := nmax x (Nat.add (Nat.add V q) a);
    let kb16 := nmin y (Nat.sub (Nat.add u I) q);
    let kb17 := nmax z (Nat.add (Nat.add X q) a);
    let kb18 := nmin A (Nat.sub (Nat.add u K) q);
    let kb19 := nmax B (Nat.add (Nat.add Z q) a);
    let kb20 := nmin C (Nat.sub (Nat.add u M) q);
    let kb21 := nmax q q;
    let kb22 := nmax F (Nat.add g q);
    let kb23 := nmax H (Nat.add V q);
    let kb24 := nmax J (Nat.add X q);
    let kb25 := nmax L (Nat.add Z q);
    let kb26 := nmax N (Nat.sub (Nat.add g q) d);
    let kb27 := nmin O (Nat.sub (Nat.add f G) q);
    let kb28 := nmax P (Nat.sub (Nat.add V q) d);
    let kb29 := nmin Q (Nat.sub (Nat.add f I) q);
    let kb30 := nmax R (Nat.sub (Nat.add X q) d);
    let kb31 := nmin S (Nat.sub (Nat.add f K) q);
    let kb32 := nmax T (Nat.sub (Nat.add Z q) d);
    let kb33 := nmin U (Nat.sub (Nat.add f M) q);
    let kb34 := nmin W (Nat.sub I q);
    let kb35 := nmin Y (Nat.sub K q);
    let kb36 := nmin aa (Nat.sub M q);
    let kb37 := nmax ab (Nat.sub (Nat.add X q) G);
    let kb38 := nmin ac (Nat.sub K (Nat.add g q));
    let kb39 := nmax ad (Nat.sub (Nat.add Z q) G);
    let kb40 := nmin ae (Nat.sub M (Nat.add g q));
    let kb41 := nmax af (Nat.sub (Nat.add Z q) I);
    let kb42 := nmin ag (Nat.sub M (Nat.add V q));
    ih p a kb0 kb1 d kb2 f g kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 kb11 kb12 u kb13 kb14 kb15 kb16 kb17 kb18 kb19 kb20 kb21 E kb22 G kb23 I kb24 K kb25 M kb26 kb27 kb28 kb29 kb30 kb31 kb32 kb33 V kb34 X kb35 Z kb36 kb37 kb38 kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit14 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add F G) 1;
  let ka0 := nmax a (Nat.sub v q);
  let ka1 := nmin d (Nat.sub q N);
  let ka2 := nmax e (Nat.sub (Nat.add D N) q);
  let ka3 := nmin f (Nat.sub q (Nat.add c g));
  let ka4 := nmin h (Nat.sub q D);
  let ka5 := nmax i (Nat.sub H q);
  let ka6 := nmax l (Nat.sub J (Nat.add q j));
  let ka7 := nmin m (Nat.sub (Nat.add q ac) H);
  let ka8 := nmax n (Nat.sub L (Nat.add q ac));
  let ka9 := nmin o (Nat.sub (Nat.add q ae) J);
  let ka10 := nmax r (Nat.sub (Nat.add c v) q);
  let ka11 := nmin s (Nat.sub (Nat.add b q) N);
  let ka12 := nmax t (Nat.sub (Nat.add D v) q);
  let ka13 := nmin u (Nat.sub (Nat.add b q) g);
  let ka14 := nmin w (Nat.add b q);
  let ka15 := nmax x (Nat.sub (Nat.add H v) q);
  let ka16 := nmin y (Nat.add (Nat.add b q) j);
  let ka17 := nmax z (Nat.sub (Nat.add J v) q);
  let ka18 := nmin A (Nat.add (Nat.add b q) ac);
  let ka19 := nmax B (Nat.sub (Nat.add L v) q);
  let ka20 := nmin C (Nat.add (Nat.add b q) ae);
  let ka21 := nmin E (Nat.sub q g);
  let ka22 := nmin q q;
  let ka23 := nmin I (Nat.add q j);
  let ka24 := nmin K (Nat.add q ac);
  let ka25 := nmin M (Nat.add q ae);
  let ka26 := nmin O (Nat.sub q c);
  let ka27 := nmax P (Nat.sub (Nat.add H N) q);
  let ka28 := nmin Q (Nat.sub (Nat.add q j) c);
  let ka29 := nmax R (Nat.sub (Nat.add J N) q);
  let ka30 := nmin S (Nat.sub (Nat.add q ac) c);
  let ka31 := nmax T (Nat.sub (Nat.add L N) q);
  let ka32 := nmin U (Nat.sub (Nat.add q ae) c);
  let ka33 := nmax V (Nat.sub (Nat.add H g) q);
  let ka34 := nmin W (Nat.sub (Nat.add q j) D);
  let ka35 := nmax X (Nat.sub (Nat.add J g) q);
  let ka36 := nmin Y (Nat.sub (Nat.add q ac) D);
  let ka37 := nmax Z (Nat.sub (Nat.add L g) q);
  let ka38 := nmin aa (Nat.sub (Nat.add q ae) D);
  let ka39 := nmax ab (Nat.sub J q);
  let ka40 := nmax ad (Nat.sub L q);
  let ka41 := nmax af (Nat.sub L (Nat.add q j));
  let ka42 := nmin ag (Nat.sub (Nat.add q ae) H);
  let p := ih pos ka0 b c ka1 ka2 ka3 g ka4 ka5 j ka6 ka7 ka8 ka9 ka10 ka11 ka12 ka13 v ka14 ka15 ka16 ka17 ka18 ka19 ka20 D ka21 F ka22 H ka23 J ka24 L ka25 N ka26 ka27 ka28 ka29 ka30 ka31 ka32 ka33 ka34 ka35 ka36 ka37 ka38 ka39 ac ka40 ae ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub w q);
    let kb1 := nmax c (Nat.sub q O);
    let kb2 := nmax e (Nat.sub q (Nat.add h d));
    let kb3 := nmin f (Nat.sub (Nat.add O E) q);
    let kb4 := nmax g (Nat.sub q E);
    let kb5 := nmin j (Nat.sub I q);
    let kb6 := nmax l (Nat.sub (Nat.add ab q) I);
    let kb7 := nmin m (Nat.sub K (Nat.add i q));
    let kb8 := nmax n (Nat.sub (Nat.add ad q) K);
    let kb9 := nmin o (Nat.sub M (Nat.add ab q));
    let kb10 := nmax r (Nat.sub (Nat.add q a) O);
    let kb11 := nmin s (Nat.sub (Nat.add w d) q);
    let kb12 := nmax t (Nat.sub (Nat.add q a) h);
    let kb13 := nmin u (Nat.sub (Nat.add w E) q);
    let kb14 := nmax v (Nat.add q a);
    let kb15 := nmax x (Nat.add (Nat.add i q) a);
    let kb16 := nmin y (Nat.sub (Nat.add w I) q);
    let kb17 := nmax z (Nat.add (Nat.add ab q) a);
    let kb18 := nmin A (Nat.sub (Nat.add w K) q);
    let kb19 := nmax B (Nat.add (Nat.add ad q) a);
    let kb20 := nmin C (Nat.sub (Nat.add w M) q);
    let kb21 := nmax D (Nat.sub q h);
    let kb22 := nmax q q;
    let kb23 := nmax H (Nat.add i q);
    let kb24 := nmax J (Nat.add ab q);
    let kb25 := nmax L (Nat.add ad q);
    let kb26 := nmax N (Nat.sub q d);
    let kb27 := nmax P (Nat.sub (Nat.add i q) d);
    let kb28 := nmin Q (Nat.sub (Nat.add O I) q);
    let kb29 := nmax R (Nat.sub (Nat.add ab q) d);
    let kb30 := nmin S (Nat.sub (Nat.add O K) q);
    let kb31 := nmax T (Nat.sub (Nat.add ad q) d);
    let kb32 := nmin U (Nat.sub (Nat.add O M) q);
    let kb33 := nmax V (Nat.sub (Nat.add i q) E);
    let kb34 := nmin W (Nat.sub (Nat.add h I) q);
    let kb35 := nmax X (Nat.sub (Nat.add ab q) E);
    let kb36 := nmin Y (Nat.sub (Nat.add h K) q);
    let kb37 := nmax Z (Nat.sub (Nat.add ad q) E);
    let kb38 := nmin aa (Nat.sub (Nat.add h M) q);
    let kb39 := nmin ac (Nat.sub K q);
    let kb40 := nmin ae (Nat.sub M q);
    let kb41 := nmax af (Nat.sub (Nat.add ad q) I);
    let kb42 := nmin ag (Nat.sub M (Nat.add i q));
    ih p a kb0 kb1 d kb2 kb3 kb4 h i kb5 kb6 kb7 kb8 kb9 kb10 kb11 kb12 kb13 kb14 w kb15 kb16 kb17 kb18 kb19 kb20 kb21 E kb22 G kb23 I kb24 K kb25 M kb26 O kb27 kb28 kb29 kb30 kb31 kb32 kb33 kb34 kb35 kb36 kb37 kb38 ab kb39 ad kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit15 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add H I) 1;
  let ka0 := nmax a (Nat.sub x q);
  let ka1 := nmin d (Nat.sub q P);
  let ka2 := nmax e (Nat.sub (Nat.add D P) q);
  let ka3 := nmin f (Nat.sub q (Nat.add c V));
  let ka4 := nmax g (Nat.sub (Nat.add F V) q);
  let ka5 := nmin h (Nat.sub q (Nat.add D i));
  let ka6 := nmin j (Nat.sub q F);
  let ka7 := nmax l (Nat.sub J q);
  let ka8 := nmax n (Nat.sub L (Nat.add q m));
  let ka9 := nmin o (Nat.sub (Nat.add q ag) J);
  let ka10 := nmax r (Nat.sub (Nat.add c x) q);
  let ka11 := nmin s (Nat.sub (Nat.add b q) P);
  let ka12 := nmax t (Nat.sub (Nat.add D x) q);
  let ka13 := nmin u (Nat.sub (Nat.add b q) V);
  let ka14 := nmax v (Nat.sub (Nat.add F x) q);
  let ka15 := nmin w (Nat.sub (Nat.add b q) i);
  let ka16 := nmin y (Nat.add b q);
  let ka17 := nmax z (Nat.sub (Nat.add J x) q);
  let ka18 := nmin A (Nat.add (Nat.add b q) m);
  let ka19 := nmax B (Nat.sub (Nat.add L x) q);
  let ka20 := nmin C (Nat.add (Nat.add b q) ag);
  let ka21 := nmin E (Nat.sub q V);
  let ka22 := nmin G (Nat.sub q i);
  let ka23 := nmin q q;
  let ka24 := nmin K (Nat.add q m);
  let ka25 := nmin M (Nat.add q ag);
  let ka26 := nmax N (Nat.sub (Nat.add F P) q);
  let ka27 := nmin O (Nat.sub q (Nat.add c i));
  let ka28 := nmin Q (Nat.sub q c);
  let ka29 := nmax R (Nat.sub (Nat.add J P) q);
  let ka30 := nmin S (Nat.sub (Nat.add q m) c);
  let ka31 := nmax T (Nat.sub (Nat.add L P) q);
  let ka32 := nmin U (Nat.sub (Nat.add q ag) c);
  let ka33 := nmin W (Nat.sub q D);
  let ka34 := nmax X (Nat.sub (Nat.add J V) q);
  let ka35 := nmin Y (Nat.sub (Nat.add q m) D);
  let ka36 := nmax Z (Nat.sub (Nat.add L V) q);
  let ka37 := nmin aa (Nat.sub (Nat.add q ag) D);
  let ka38 := nmax ab (Nat.sub (Nat.add J i) q);
  let ka39 := nmin ac (Nat.sub (Nat.add q m) F);
  let ka40 := nmax ad (Nat.sub (Nat.add L i) q);
  let ka41 := nmin ae (Nat.sub (Nat.add q ag) F);
  let ka42 := nmax af (Nat.sub L q);
  let p := ih pos ka0 b c ka1 ka2 ka3 ka4 ka5 i ka6 ka7 m ka8 ka9 ka10 ka11 ka12 ka13 ka14 ka15 x ka16 ka17 ka18 ka19 ka20 D ka21 F ka22 H ka23 J ka24 L ka25 ka26 ka27 P ka28 ka29 ka30 ka31 ka32 V ka33 ka34 ka35 ka36 ka37 ka38 ka39 ka40 ka41 ka42 ag ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub y q);
    let kb1 := nmax c (Nat.sub q Q);
    let kb2 := nmax e (Nat.sub q (Nat.add W d));
    let kb3 := nmin f (Nat.sub (Nat.add Q E) q);
    let kb4 := nmax g (Nat.sub q (Nat.add j E));
    let kb5 := nmin h (Nat.sub (Nat.add W G) q);
    let kb6 := nmax i (Nat.sub q G);
    let kb7 := nmin m (Nat.sub K q);
    let kb8 := nmax n (Nat.sub (Nat.add af q) K);
    let kb9 := nmin o (Nat.sub M (Nat.add l q));
    let kb10 := nmax r (Nat.sub (Nat.add q a) Q);
    let kb11 := nmin s (Nat.sub (Nat.add y d) q);
    let kb12 := nmax t (Nat.sub (Nat.add q a) W);
    let kb13 := nmin u (Nat.sub (Nat.add y E) q);
    let kb14 := nmax v (Nat.sub (Nat.add q a) j);
    let kb15 := nmin w (Nat.sub (Nat.add y G) q);
    let kb16 := nmax x (Nat.add q a);
    let kb17 := nmax z (Nat.add (Nat.add l q) a);
    let kb18 := nmin A (Nat.sub (Nat.add y K) q);
    let kb19 := nmax B (Nat.add (Nat.add af q) a);
    let kb20 := nmin C (Nat.sub (Nat.add y M) q);
    let kb21 := nmax D (Nat.sub q W);
    let kb22 := nmax F (Nat.sub q j);
    let kb23 := nmax q q;
    let kb24 := nmax J (Nat.add l q);
    let kb25 := nmax L (Nat.add af q);
    let kb26 := nmax N (Nat.sub q (Nat.add j d));
    let kb27 := nmin O (Nat.sub (Nat.add Q G) q);
    let kb28 := nmax P (Nat.sub q d);
    let kb29 := nmax R (Nat.sub (Nat.add l q) d);
    let kb30 := nmin S (Nat.sub (Nat.add Q K) q);
    let kb31 := nmax T (Nat.sub (Nat.add af q) d);
    let kb32 := nmin U (Nat.sub (Nat.add Q M) q);
    let kb33 := nmax V (Nat.sub q E);
    let kb34 := nmax X (Nat.sub (Nat.add l q) E);
    let kb35 := nmin Y (Nat.sub (Nat.add W K) q);
    let kb36 := nmax Z (Nat.sub (Nat.add af q) E);
    let kb37 := nmin aa (Nat.sub (Nat.add W M) q);
    let kb38 := nmax ab (Nat.sub (Nat.add l q) G);
    let kb39 := nmin ac (Nat.sub (Nat.add j K) q);
    let kb40 := nmax ad (Nat.sub (Nat.add af q) G);
    let kb41 := nmin ae (Nat.sub (Nat.add j M) q);
    let kb42 := nmin ag (Nat.sub M q);
    ih p a kb0 kb1 d kb2 kb3 kb4 kb5 kb6 j l kb7 kb8 kb9 kb10 kb11 kb12 kb13 kb14 kb15 kb16 y kb17 kb18 kb19 kb20 kb21 E kb22 G kb23 I kb24 K kb25 M kb26 kb27 kb28 Q kb29 kb30 kb31 kb32 kb33 W kb34 kb35 kb36 kb37 kb38 kb39 kb40 kb41 af kb42 ah) 0 (Nat.beq p 0)

def ssplit16 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add J K) 1;
  let ka0 := nmax a (Nat.sub z q);
  let ka1 := nmin d (Nat.sub q R);
  let ka2 := nmax e (Nat.sub (Nat.add D R) q);
  let ka3 := nmin f (Nat.sub q (Nat.add c X));
  let ka4 := nmax g (Nat.sub (Nat.add F X) q);
  let ka5 := nmin h (Nat.sub q (Nat.add D ab));
  let ka6 := nmax i (Nat.sub (Nat.add H ab) q);
  let ka7 := nmin j (Nat.sub q (Nat.add F l));
  let ka8 := nmin m (Nat.sub q H);
  let ka9 := nmax n (Nat.sub L q);
  let ka10 := nmax r (Nat.sub (Nat.add c z) q);
  let ka11 := nmin s (Nat.sub (Nat.add b q) R);
  let ka12 := nmax t (Nat.sub (Nat.add D z) q);
  let ka13 := nmin u (Nat.sub (Nat.add b q) X);
  let ka14 := nmax v (Nat.sub (Nat.add F z) q);
  let ka15 := nmin w (Nat.sub (Nat.add b q) ab);
  let ka16 := nmax x (Nat.sub (Nat.add H z) q);
  let ka17 := nmin y (Nat.sub (Nat.add b q) l);
  let ka18 := nmin A (Nat.add b q);
  let ka19 := nmax B (Nat.sub (Nat.add L z) q);
  let ka20 := nmin C (Nat.add (Nat.add b q) o);
  let ka21 := nmin E (Nat.sub q X);
  let ka22 := nmin G (Nat.sub q ab);
  let ka23 := nmin I (Nat.sub q l);
  let ka24 := nmin q q;
  let ka25 := nmin M (Nat.add q o);
  let ka26 := nmax N (Nat.sub (Nat.add F R) q);
  let ka27 := nmin O (Nat.sub q (Nat.add c ab));
  let ka28 := nmax P (Nat.sub (Nat.add H R) q);
  let ka29 := nmin Q (Nat.sub q (Nat.add c l));
  let ka30 := nmin S (Nat.sub q c);
  let ka31 := nmax T (Nat.sub (Nat.add L R) q);
  let ka32 := nmin U (Nat.sub (Nat.add q o) c);
  let ka33 := nmax V (Nat.sub (Nat.add H X) q);
  let ka34 := nmin W (Nat.sub q (Nat.add D l));
  let ka35 := nmin Y (Nat.sub q D);
  let ka36 := nmax Z (Nat.sub (Nat.add L X) q);
  let ka37 := nmin aa (Nat.sub (Nat.add q o) D);
  let ka38 := nmin ac (Nat.sub q F);
  let ka39 := nmax ad (Nat.sub (Nat.add L ab) q);
  let ka40 := nmin ae (Nat.sub (Nat.add q o) F);
  let ka41 := nmax af (Nat.sub (Nat.add L l) q);
  let ka42 := nmin ag (Nat.sub (Nat.add q o) H);
  let p := ih pos ka0 b c ka1 ka2 ka3 ka4 ka5 ka6 ka7 l ka8 ka9 o ka10 ka11 ka12 ka13 ka14 ka15 ka16 ka17 z ka18 ka19 ka20 D ka21 F ka22 H ka23 J ka24 L ka25 ka26 ka27 ka28 ka29 R ka30 ka31 ka32 ka33 ka34 X ka35 ka36 ka37 ab ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub A q);
    let kb1 := nmax c (Nat.sub q S);
    let kb2 := nmax e (Nat.sub q (Nat.add Y d));
    let kb3 := nmin f (Nat.sub (Nat.add S E) q);
    let kb4 := nmax g (Nat.sub q (Nat.add ac E));
    let kb5 := nmin h (Nat.sub (Nat.add Y G) q);
    let kb6 := nmax i (Nat.sub q (Nat.add m G));
    let kb7 := nmin j (Nat.sub (Nat.add ac I) q);
    let kb8 := nmax l (Nat.sub q I);
    let kb9 := nmin o (Nat.sub M q);
    let kb10 := nmax r (Nat.sub (Nat.add q a) S);
    let kb11 := nmin s (Nat.sub (Nat.add A d) q);
    let kb12 := nmax t (Nat.sub (Nat.add q a) Y);
    let kb13 := nmin u (Nat.sub (Nat.add A E) q);
    let kb14 := nmax v (Nat.sub (Nat.add q a) ac);
    let kb15 := nmin w (Nat.sub (Nat.add A G) q);
    let kb16 := nmax x (Nat.sub (Nat.add q a) m);
    let kb17 := nmin y (Nat.sub (Nat.add A I) q);
    let kb18 := nmax z (Nat.add q a);
    let kb19 := nmax B (Nat.add (Nat.add n q) a);
    let kb20 := nmin C (Nat.sub (Nat.add A M) q);
    let kb21 := nmax D (Nat.sub q Y);
    let kb22 := nmax F (Nat.sub q ac);
    let kb23 := nmax H (Nat.sub q m);
    let kb24 := nmax q q;
    let kb25 := nmax L (Nat.add n q);
    let kb26 := nmax N (Nat.sub q (Nat.add ac d));
    let kb27 := nmin O (Nat.sub (Nat.add S G) q);
    let kb28 := nmax P (Nat.sub q (Nat.add m d));
    let kb29 := nmin Q (Nat.sub (Nat.add S I) q);
    let kb30 := nmax R (Nat.sub q d);
    let kb31 := nmax T (Nat.sub (Nat.add n q) d);
    let kb32 := nmin U (Nat.sub (Nat.add S M) q);
    let kb33 := nmax V (Nat.sub q (Nat.add m E));
    let kb34 := nmin W (Nat.sub (Nat.add Y I) q);
    let kb35 := nmax X (Nat.sub q E);
    let kb36 := nmax Z (Nat.sub (Nat.add n q) E);
    let kb37 := nmin aa (Nat.sub (Nat.add Y M) q);
    let kb38 := nmax ab (Nat.sub q G);
    let kb39 := nmax ad (Nat.sub (Nat.add n q) G);
    let kb40 := nmin ae (Nat.sub (Nat.add ac M) q);
    let kb41 := nmax af (Nat.sub (Nat.add n q) I);
    let kb42 := nmin ag (Nat.sub (Nat.add m M) q);
    ih p a kb0 kb1 d kb2 kb3 kb4 kb5 kb6 kb7 kb8 m n kb9 kb10 kb11 kb12 kb13 kb14 kb15 kb16 kb17 kb18 A kb19 kb20 kb21 E kb22 G kb23 I kb24 K kb25 M kb26 kb27 kb28 kb29 kb30 S kb31 kb32 kb33 kb34 kb35 Y kb36 kb37 kb38 ac kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit17 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add L M) 1;
  let ka0 := nmax a (Nat.sub B q);
  let ka1 := nmin d (Nat.sub q T);
  let ka2 := nmax e (Nat.sub (Nat.add D T) q);
  let ka3 := nmin f (Nat.sub q (Nat.add c Z));
  let ka4 := nmax g (Nat.sub (Nat.add F Z) q);
  let ka5 := nmin h (Nat.sub q (Nat.add D ad));
  let ka6 := nmax i (Nat.sub (Nat.add H ad) q);
  let ka7 := nmin j (Nat.sub q (Nat.add F af));
  let ka8 := nmax l (Nat.sub (Nat.add J af) q);
  let ka9 := nmin m (Nat.sub q (Nat.add H n));
  let ka10 := nmin o (Nat.sub q J);
  let ka11 := nmax r (Nat.sub (Nat.add c B) q);
  let ka12 := nmin s (Nat.sub (Nat.add b q) T);
  let ka13 := nmax t (Nat.sub (Nat.add D B) q);
  let ka14 := nmin u (Nat.sub (Nat.add b q) Z);
  let ka15 := nmax v (Nat.sub (Nat.add F B) q);
  let ka16 := nmin w (Nat.sub (Nat.add b q) ad);
  let ka17 := nmax x (Nat.sub (Nat.add H B) q);
  let ka18 := nmin y (Nat.sub (Nat.add b q) af);
  let ka19 := nmax z (Nat.sub (Nat.add J B) q);
  let ka20 := nmin A (Nat.sub (Nat.add b q) n);
  let ka21 := nmin C (Nat.add b q);
  let ka22 := nmin E (Nat.sub q Z);
  let ka23 := nmin G (Nat.sub q ad);
  let ka24 := nmin I (Nat.sub q af);
  let ka25 := nmin K (Nat.sub q n);
  let ka26 := nmin q q;
  let ka27 := nmax N (Nat.sub (Nat.add F T) q);
  let ka28 := nmin O (Nat.sub q (Nat.add c ad));
  let ka29 := nmax P (Nat.sub (Nat.add H T) q);
  let ka30 := nmin Q (Nat.sub q (Nat.add c af));
  let ka31 := nmax R (Nat.sub (Nat.add J T) q);
  let ka32 := nmin S (Nat.sub q (Nat.add c n));
  let ka33 := nmin U (Nat.sub q c);
  let ka34 := nmax V (Nat.sub (Nat.add H Z) q);
  let ka35 := nmin W (Nat.sub q (Nat.add D af));
  let ka36 := nmax X (Nat.sub (Nat.add J Z) q);
  let ka37 := nmin Y (Nat.sub q (Nat.add D n));
  let ka38 := nmin aa (Nat.sub q D);
  let ka39 := nmax ab (Nat.sub (Nat.add J ad) q);
  let ka40 := nmin ac (Nat.sub q (Nat.add F n));
  let ka41 := nmin ae (Nat.sub q F);
  let ka42 := nmin ag (Nat.sub q H);
  let p := ih pos ka0 b c ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 ka9 n ka10 ka11 ka12 ka13 ka14 ka15 ka16 ka17 ka18 ka19 ka20 B ka21 D ka22 F ka23 H ka24 J ka25 L ka26 ka27 ka28 ka29 ka30 ka31 ka32 T ka33 ka34 ka35 ka36 ka37 Z ka38 ka39 ka40 ad ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmin b (Nat.sub C q);
    let kb1 := nmax c (Nat.sub q U);
    let kb2 := nmax e (Nat.sub q (Nat.add aa d));
    let kb3 := nmin f (Nat.sub (Nat.add U E) q);
    let kb4 := nmax g (Nat.sub q (Nat.add ae E));
    let kb5 := nmin h (Nat.sub (Nat.add aa G) q);
    let kb6 := nmax i (Nat.sub q (Nat.add ag G));
    let kb7 := nmin j (Nat.sub (Nat.add ae I) q);
    let kb8 := nmax l (Nat.sub q (Nat.add o I));
    let kb9 := nmin m (Nat.sub (Nat.add ag K) q);
    let kb10 := nmax n (Nat.sub q K);
    let kb11 := nmax r (Nat.sub (Nat.add q a) U);
    let kb12 := nmin s (Nat.sub (Nat.add C d) q);
    let kb13 := nmax t (Nat.sub (Nat.add q a) aa);
    let kb14 := nmin u (Nat.sub (Nat.add C E) q);
    let kb15 := nmax v (Nat.sub (Nat.add q a) ae);
    let kb16 := nmin w (Nat.sub (Nat.add C G) q);
    let kb17 := nmax x (Nat.sub (Nat.add q a) ag);
    let kb18 := nmin y (Nat.sub (Nat.add C I) q);
    let kb19 := nmax z (Nat.sub (Nat.add q a) o);
    let kb20 := nmin A (Nat.sub (Nat.add C K) q);
    let kb21 := nmax B (Nat.add q a);
    let kb22 := nmax D (Nat.sub q aa);
    let kb23 := nmax F (Nat.sub q ae);
    let kb24 := nmax H (Nat.sub q ag);
    let kb25 := nmax J (Nat.sub q o);
    let kb26 := nmax q q;
    let kb27 := nmax N (Nat.sub q (Nat.add ae d));
    let kb28 := nmin O (Nat.sub (Nat.add U G) q);
    let kb29 := nmax P (Nat.sub q (Nat.add ag d));
    let kb30 := nmin Q (Nat.sub (Nat.add U I) q);
    let kb31 := nmax R (Nat.sub q (Nat.add o d));
    let kb32 := nmin S (Nat.sub (Nat.add U K) q);
    let kb33 := nmax T (Nat.sub q d);
    let kb34 := nmax V (Nat.sub q (Nat.add ag E));
    let kb35 := nmin W (Nat.sub (Nat.add aa I) q);
    let kb36 := nmax X (Nat.sub q (Nat.add o E));
    let kb37 := nmin Y (Nat.sub (Nat.add aa K) q);
    let kb38 := nmax Z (Nat.sub q E);
    let kb39 := nmax ab (Nat.sub q (Nat.add o G));
    let kb40 := nmin ac (Nat.sub (Nat.add ae K) q);
    let kb41 := nmax ad (Nat.sub q G);
    let kb42 := nmax af (Nat.sub q I);
    ih p a kb0 kb1 d kb2 kb3 kb4 kb5 kb6 kb7 kb8 kb9 kb10 o kb11 kb12 kb13 kb14 kb15 kb16 kb17 kb18 kb19 kb20 kb21 C kb22 E kb23 G kb24 I kb25 K kb26 M kb27 kb28 kb29 kb30 kb31 kb32 kb33 U kb34 kb35 kb36 kb37 kb38 aa kb39 kb40 kb41 ae kb42 ag ah) 0 (Nat.beq p 0)

def ssplit24 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add N O) 1;
  let ka0 := nmax a (Nat.sub v (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) F);
  let ka2 := nmax c (Nat.sub F q);
  let ka3 := nmin f (Nat.sub q g);
  let ka4 := nmin h (Nat.sub q e);
  let ka5 := nmax i (Nat.sub P q);
  let ka6 := nmax l (Nat.sub R (Nat.add q j));
  let ka7 := nmin m (Nat.sub (Nat.add q ac) P);
  let ka8 := nmax n (Nat.sub T (Nat.add q ac));
  let ka9 := nmin o (Nat.sub (Nat.add q ae) R);
  let ka10 := nmax r (Nat.sub v q);
  let ka11 := nmax t (Nat.sub (Nat.add e v) q);
  let ka12 := nmin u (Nat.sub (Nat.add s q) g);
  let ka13 := nmin w (Nat.add s q);
  let ka14 := nmax x (Nat.sub (Nat.add P v) q);
  let ka15 := nmin y (Nat.add (Nat.add s q) j);
  let ka16 := nmax z (Nat.sub (Nat.add R v) q);
  let ka17 := nmin A (Nat.add (Nat.add s q) ac);
  let ka18 := nmax B (Nat.sub (Nat.add T v) q);
  let ka19 := nmin C (Nat.add (Nat.add s q) ae);
  let ka20 := nmax D (Nat.sub (Nat.add e F) q);
  let ka21 := nmin E (Nat.sub (Nat.add d q) g);
  let ka22 := nmin G (Nat.add d q);
  let ka23 := nmax H (Nat.sub (Nat.add P F) q);
  let ka24 := nmin I (Nat.add (Nat.add d q) j);
  let ka25 := nmax J (Nat.sub (Nat.add R F) q);
  let ka26 := nmin K (Nat.add (Nat.add d q) ac);
  let ka27 := nmax L (Nat.sub (Nat.add T F) q);
  let ka28 := nmin M (Nat.add (Nat.add d q) ae);
  let ka29 := nmin q q;
  let ka30 := nmin Q (Nat.add q j);
  let ka31 := nmin S (Nat.add q ac);
  let ka32 := nmin U (Nat.add q ae);
  let ka33 := nmax V (Nat.sub (Nat.add P g) q);
  let ka34 := nmin W (Nat.sub (Nat.add q j) e);
  let ka35 := nmax X (Nat.sub (Nat.add R g) q);
  let ka36 := nmin Y (Nat.sub (Nat.add q ac) e);
  let ka37 := nmax Z (Nat.sub (Nat.add T g) q);
  let ka38 := nmin aa (Nat.sub (Nat.add q ae) e);
  let ka39 := nmax ab (Nat.sub R q);
  let ka40 := nmax ad (Nat.sub T q);
  let ka41 := nmax af (Nat.sub T (Nat.add q j));
  let ka42 := nmin ag (Nat.sub (Nat.add q ae) P);
  let p := ih pos ka0 ka1 ka2 d e ka3 g ka4 ka5 j ka6 ka7 ka8 ka9 ka10 s ka11 ka12 v ka13 ka14 ka15 ka16 ka17 ka18 ka19 ka20 ka21 F ka22 ka23 ka24 ka25 ka26 ka27 ka28 N ka29 P ka30 R ka31 T ka32 ka33 ka34 ka35 ka36 ka37 ka38 ka39 ac ka40 ae ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) G);
    let kb1 := nmin b (Nat.sub w (Nat.add q c));
    let kb2 := nmin d (Nat.sub G q);
    let kb3 := nmax e (Nat.sub q h);
    let kb4 := nmax g (Nat.sub q f);
    let kb5 := nmin j (Nat.sub Q q);
    let kb6 := nmax l (Nat.sub (Nat.add ab q) Q);
    let kb7 := nmin m (Nat.sub S (Nat.add i q));
    let kb8 := nmax n (Nat.sub (Nat.add ad q) S);
    let kb9 := nmin o (Nat.sub U (Nat.add ab q));
    let kb10 := nmin s (Nat.sub w q);
    let kb11 := nmax t (Nat.sub (Nat.add q r) h);
    let kb12 := nmin u (Nat.sub (Nat.add w f) q);
    let kb13 := nmax v (Nat.add q r);
    let kb14 := nmax x (Nat.add (Nat.add i q) r);
    let kb15 := nmin y (Nat.sub (Nat.add w Q) q);
    let kb16 := nmax z (Nat.add (Nat.add ab q) r);
    let kb17 := nmin A (Nat.sub (Nat.add w S) q);
    let kb18 := nmax B (Nat.add (Nat.add ad q) r);
    let kb19 := nmin C (Nat.sub (Nat.add w U) q);
    let kb20 := nmax D (Nat.sub (Nat.add q c) h);
    let kb21 := nmin E (Nat.sub (Nat.add G f) q);
    let kb22 := nmax F (Nat.add q c);
    let kb23 := nmax H (Nat.add (Nat.add i q) c);
    let kb24 := nmin I (Nat.sub (Nat.add G Q) q);
    let kb25 := nmax J (Nat.add (Nat.add ab q) c);
    let kb26 := nmin K (Nat.sub (Nat.add G S) q);
    let kb27 := nmax L (Nat.add (Nat.add ad q) c);
    let kb28 := nmin M (Nat.sub (Nat.add G U) q);
    let kb29 := nmax q q;
    let kb30 := nmax P (Nat.add i q);
    let kb31 := nmax R (Nat.add ab q);
    let kb32 := nmax T (Nat.add ad q);
    let kb33 := nmax V (Nat.sub (Nat.add i q) f);
    let kb34 := nmin W (Nat.sub (Nat.add h Q) q);
    let kb35 := nmax X (Nat.sub (Nat.add ab q) f);
    let kb36 := nmin Y (Nat.sub (Nat.add h S) q);
    let kb37 := nmax Z (Nat.sub (Nat.add ad q) f);
    let kb38 := nmin aa (Nat.sub (Nat.add h U) q);
    let kb39 := nmin ac (Nat.sub S q);
    let kb40 := nmin ae (Nat.sub U q);
    let kb41 := nmax af (Nat.sub (Nat.add ad q) Q);
    let kb42 := nmin ag (Nat.sub U (Nat.add i q));
    ih p kb0 kb1 c kb2 kb3 f kb4 h i kb5 kb6 kb7 kb8 kb9 r kb10 kb11 kb12 kb13 w kb14 kb15 kb16 kb17 kb18 kb19 kb20 kb21 kb22 G kb23 kb24 kb25 kb26 kb27 kb28 kb29 O kb30 Q kb31 S kb32 U kb33 kb34 kb35 kb36 kb37 kb38 ab kb39 ad kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit25 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add P Q) 1;
  let ka0 := nmax a (Nat.sub x (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) H);
  let ka2 := nmax c (Nat.sub H q);
  let ka3 := nmin f (Nat.sub q V);
  let ka4 := nmax g (Nat.sub (Nat.add N V) q);
  let ka5 := nmin h (Nat.sub q (Nat.add e i));
  let ka6 := nmin j (Nat.sub q N);
  let ka7 := nmax l (Nat.sub R q);
  let ka8 := nmax n (Nat.sub T (Nat.add q m));
  let ka9 := nmin o (Nat.sub (Nat.add q ag) R);
  let ka10 := nmax r (Nat.sub x q);
  let ka11 := nmax t (Nat.sub (Nat.add e x) q);
  let ka12 := nmin u (Nat.sub (Nat.add s q) V);
  let ka13 := nmax v (Nat.sub (Nat.add N x) q);
  let ka14 := nmin w (Nat.sub (Nat.add s q) i);
  let ka15 := nmin y (Nat.add s q);
  let ka16 := nmax z (Nat.sub (Nat.add R x) q);
  let ka17 := nmin A (Nat.add (Nat.add s q) m);
  let ka18 := nmax B (Nat.sub (Nat.add T x) q);
  let ka19 := nmin C (Nat.add (Nat.add s q) ag);
  let ka20 := nmax D (Nat.sub (Nat.add e H) q);
  let ka21 := nmin E (Nat.sub (Nat.add d q) V);
  let ka22 := nmax F (Nat.sub (Nat.add N H) q);
  let ka23 := nmin G (Nat.sub (Nat.add d q) i);
  let ka24 := nmin I (Nat.add d q);
  let ka25 := nmax J (Nat.sub (Nat.add R H) q);
  let ka26 := nmin K (Nat.add (Nat.add d q) m);
  let ka27 := nmax L (Nat.sub (Nat.add T H) q);
  let ka28 := nmin M (Nat.add (Nat.add d q) ag);
  let ka29 := nmin O (Nat.sub q i);
  let ka30 := nmin q q;
  let ka31 := nmin S (Nat.add q m);
  let ka32 := nmin U (Nat.add q ag);
  let ka33 := nmin W (Nat.sub q e);
  let ka34 := nmax X (Nat.sub (Nat.add R V) q);
  let ka35 := nmin Y (Nat.sub (Nat.add q m) e);
  let ka36 := nmax Z (Nat.sub (Nat.add T V) q);
  let ka37 := nmin aa (Nat.sub (Nat.add q ag) e);
  let ka38 := nmax ab (Nat.sub (Nat.add R i) q);
  let ka39 := nmin ac (Nat.sub (Nat.add q m) N);
  let ka40 := nmax ad (Nat.sub (Nat.add T i) q);
  let ka41 := nmin ae (Nat.sub (Nat.add q ag) N);
  let ka42 := nmax af (Nat.sub T q);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 ka5 i ka6 ka7 m ka8 ka9 ka10 s ka11 ka12 ka13 ka14 x ka15 ka16 ka17 ka18 ka19 ka20 ka21 ka22 ka23 H ka24 ka25 ka26 ka27 ka28 N ka29 P ka30 R ka31 T ka32 V ka33 ka34 ka35 ka36 ka37 ka38 ka39 ka40 ka41 ka42 ag ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) I);
    let kb1 := nmin b (Nat.sub y (Nat.add q c));
    let kb2 := nmin d (Nat.sub I q);
    let kb3 := nmax e (Nat.sub q W);
    let kb4 := nmax g (Nat.sub q (Nat.add j f));
    let kb5 := nmin h (Nat.sub (Nat.add W O) q);
    let kb6 := nmax i (Nat.sub q O);
    let kb7 := nmin m (Nat.sub S q);
    let kb8 := nmax n (Nat.sub (Nat.add af q) S);
    let kb9 := nmin o (Nat.sub U (Nat.add l q));
    let kb10 := nmin s (Nat.sub y q);
    let kb11 := nmax t (Nat.sub (Nat.add q r) W);
    let kb12 := nmin u (Nat.sub (Nat.add y f) q);
    let kb13 := nmax v (Nat.sub (Nat.add q r) j);
    let kb14 := nmin w (Nat.sub (Nat.add y O) q);
    let kb15 := nmax x (Nat.add q r);
    let kb16 := nmax z (Nat.add (Nat.add l q) r);
    let kb17 := nmin A (Nat.sub (Nat.add y S) q);
    let kb18 := nmax B (Nat.add (Nat.add af q) r);
    let kb19 := nmin C (Nat.sub (Nat.add y U) q);
    let kb20 := nmax D (Nat.sub (Nat.add q c) W);
    let kb21 := nmin E (Nat.sub (Nat.add I f) q);
    let kb22 := nmax F (Nat.sub (Nat.add q c) j);
    let kb23 := nmin G (Nat.sub (Nat.add I O) q);
    let kb24 := nmax H (Nat.add q c);
    let kb25 := nmax J (Nat.add (Nat.add l q) c);
    let kb26 := nmin K (Nat.sub (Nat.add I S) q);
    let kb27 := nmax L (Nat.add (Nat.add af q) c);
    let kb28 := nmin M (Nat.sub (Nat.add I U) q);
    let kb29 := nmax N (Nat.sub q j);
    let kb30 := nmax q q;
    let kb31 := nmax R (Nat.add l q);
    let kb32 := nmax T (Nat.add af q);
    let kb33 := nmax V (Nat.sub q f);
    let kb34 := nmax X (Nat.sub (Nat.add l q) f);
    let kb35 := nmin Y (Nat.sub (Nat.add W S) q);
    let kb36 := nmax Z (Nat.sub (Nat.add af q) f);
    let kb37 := nmin aa (Nat.sub (Nat.add W U) q);
    let kb38 := nmax ab (Nat.sub (Nat.add l q) O);
    let kb39 := nmin ac (Nat.sub (Nat.add j S) q);
    let kb40 := nmax ad (Nat.sub (Nat.add af q) O);
    let kb41 := nmin ae (Nat.sub (Nat.add j U) q);
    let kb42 := nmin ag (Nat.sub U q);
    ih p kb0 kb1 c kb2 kb3 f kb4 kb5 kb6 j l kb7 kb8 kb9 r kb10 kb11 kb12 kb13 kb14 kb15 y kb16 kb17 kb18 kb19 kb20 kb21 kb22 kb23 kb24 I kb25 kb26 kb27 kb28 kb29 O kb30 Q kb31 S kb32 U kb33 W kb34 kb35 kb36 kb37 kb38 kb39 kb40 kb41 af kb42 ah) 0 (Nat.beq p 0)

def ssplit26 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add R S) 1;
  let ka0 := nmax a (Nat.sub z (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) J);
  let ka2 := nmax c (Nat.sub J q);
  let ka3 := nmin f (Nat.sub q X);
  let ka4 := nmax g (Nat.sub (Nat.add N X) q);
  let ka5 := nmin h (Nat.sub q (Nat.add e ab));
  let ka6 := nmax i (Nat.sub (Nat.add P ab) q);
  let ka7 := nmin j (Nat.sub q (Nat.add N l));
  let ka8 := nmin m (Nat.sub q P);
  let ka9 := nmax n (Nat.sub T q);
  let ka10 := nmax r (Nat.sub z q);
  let ka11 := nmax t (Nat.sub (Nat.add e z) q);
  let ka12 := nmin u (Nat.sub (Nat.add s q) X);
  let ka13 := nmax v (Nat.sub (Nat.add N z) q);
  let ka14 := nmin w (Nat.sub (Nat.add s q) ab);
  let ka15 := nmax x (Nat.sub (Nat.add P z) q);
  let ka16 := nmin y (Nat.sub (Nat.add s q) l);
  let ka17 := nmin A (Nat.add s q);
  let ka18 := nmax B (Nat.sub (Nat.add T z) q);
  let ka19 := nmin C (Nat.add (Nat.add s q) o);
  let ka20 := nmax D (Nat.sub (Nat.add e J) q);
  let ka21 := nmin E (Nat.sub (Nat.add d q) X);
  let ka22 := nmax F (Nat.sub (Nat.add N J) q);
  let ka23 := nmin G (Nat.sub (Nat.add d q) ab);
  let ka24 := nmax H (Nat.sub (Nat.add P J) q);
  let ka25 := nmin I (Nat.sub (Nat.add d q) l);
  let ka26 := nmin K (Nat.add d q);
  let ka27 := nmax L (Nat.sub (Nat.add T J) q);
  let ka28 := nmin M (Nat.add (Nat.add d q) o);
  let ka29 := nmin O (Nat.sub q ab);
  let ka30 := nmin Q (Nat.sub q l);
  let ka31 := nmin q q;
  let ka32 := nmin U (Nat.add q o);
  let ka33 := nmax V (Nat.sub (Nat.add P X) q);
  let ka34 := nmin W (Nat.sub q (Nat.add e l));
  let ka35 := nmin Y (Nat.sub q e);
  let ka36 := nmax Z (Nat.sub (Nat.add T X) q);
  let ka37 := nmin aa (Nat.sub (Nat.add q o) e);
  let ka38 := nmin ac (Nat.sub q N);
  let ka39 := nmax ad (Nat.sub (Nat.add T ab) q);
  let ka40 := nmin ae (Nat.sub (Nat.add q o) N);
  let ka41 := nmax af (Nat.sub (Nat.add T l) q);
  let ka42 := nmin ag (Nat.sub (Nat.add q o) P);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 ka5 ka6 ka7 l ka8 ka9 o ka10 s ka11 ka12 ka13 ka14 ka15 ka16 z ka17 ka18 ka19 ka20 ka21 ka22 ka23 ka24 ka25 J ka26 ka27 ka28 N ka29 P ka30 R ka31 T ka32 ka33 ka34 X ka35 ka36 ka37 ab ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) K);
    let kb1 := nmin b (Nat.sub A (Nat.add q c));
    let kb2 := nmin d (Nat.sub K q);
    let kb3 := nmax e (Nat.sub q Y);
    let kb4 := nmax g (Nat.sub q (Nat.add ac f));
    let kb5 := nmin h (Nat.sub (Nat.add Y O) q);
    let kb6 := nmax i (Nat.sub q (Nat.add m O));
    let kb7 := nmin j (Nat.sub (Nat.add ac Q) q);
    let kb8 := nmax l (Nat.sub q Q);
    let kb9 := nmin o (Nat.sub U q);
    let kb10 := nmin s (Nat.sub A q);
    let kb11 := nmax t (Nat.sub (Nat.add q r) Y);
    let kb12 := nmin u (Nat.sub (Nat.add A f) q);
    let kb13 := nmax v (Nat.sub (Nat.add q r) ac);
    let kb14 := nmin w (Nat.sub (Nat.add A O) q);
    let kb15 := nmax x (Nat.sub (Nat.add q r) m);
    let kb16 := nmin y (Nat.sub (Nat.add A Q) q);
    let kb17 := nmax z (Nat.add q r);
    let kb18 := nmax B (Nat.add (Nat.add n q) r);
    let kb19 := nmin C (Nat.sub (Nat.add A U) q);
    let kb20 := nmax D (Nat.sub (Nat.add q c) Y);
    let kb21 := nmin E (Nat.sub (Nat.add K f) q);
    let kb22 := nmax F (Nat.sub (Nat.add q c) ac);
    let kb23 := nmin G (Nat.sub (Nat.add K O) q);
    let kb24 := nmax H (Nat.sub (Nat.add q c) m);
    let kb25 := nmin I (Nat.sub (Nat.add K Q) q);
    let kb26 := nmax J (Nat.add q c);
    let kb27 := nmax L (Nat.add (Nat.add n q) c);
    let kb28 := nmin M (Nat.sub (Nat.add K U) q);
    let kb29 := nmax N (Nat.sub q ac);
    let kb30 := nmax P (Nat.sub q m);
    let kb31 := nmax q q;
    let kb32 := nmax T (Nat.add n q);
    let kb33 := nmax V (Nat.sub q (Nat.add m f));
    let kb34 := nmin W (Nat.sub (Nat.add Y Q) q);
    let kb35 := nmax X (Nat.sub q f);
    let kb36 := nmax Z (Nat.sub (Nat.add n q) f);
    let kb37 := nmin aa (Nat.sub (Nat.add Y U) q);
    let kb38 := nmax ab (Nat.sub q O);
    let kb39 := nmax ad (Nat.sub (Nat.add n q) O);
    let kb40 := nmin ae (Nat.sub (Nat.add ac U) q);
    let kb41 := nmax af (Nat.sub (Nat.add n q) Q);
    let kb42 := nmin ag (Nat.sub (Nat.add m U) q);
    ih p kb0 kb1 c kb2 kb3 f kb4 kb5 kb6 kb7 kb8 m n kb9 r kb10 kb11 kb12 kb13 kb14 kb15 kb16 kb17 A kb18 kb19 kb20 kb21 kb22 kb23 kb24 kb25 kb26 K kb27 kb28 kb29 O kb30 Q kb31 S kb32 U kb33 kb34 kb35 Y kb36 kb37 kb38 ac kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit27 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add T U) 1;
  let ka0 := nmax a (Nat.sub B (Nat.add d q));
  let ka1 := nmin b (Nat.sub (Nat.add s q) L);
  let ka2 := nmax c (Nat.sub L q);
  let ka3 := nmin f (Nat.sub q Z);
  let ka4 := nmax g (Nat.sub (Nat.add N Z) q);
  let ka5 := nmin h (Nat.sub q (Nat.add e ad));
  let ka6 := nmax i (Nat.sub (Nat.add P ad) q);
  let ka7 := nmin j (Nat.sub q (Nat.add N af));
  let ka8 := nmax l (Nat.sub (Nat.add R af) q);
  let ka9 := nmin m (Nat.sub q (Nat.add P n));
  let ka10 := nmin o (Nat.sub q R);
  let ka11 := nmax r (Nat.sub B q);
  let ka12 := nmax t (Nat.sub (Nat.add e B) q);
  let ka13 := nmin u (Nat.sub (Nat.add s q) Z);
  let ka14 := nmax v (Nat.sub (Nat.add N B) q);
  let ka15 := nmin w (Nat.sub (Nat.add s q) ad);
  let ka16 := nmax x (Nat.sub (Nat.add P B) q);
  let ka17 := nmin y (Nat.sub (Nat.add s q) af);
  let ka18 := nmax z (Nat.sub (Nat.add R B) q);
  let ka19 := nmin A (Nat.sub (Nat.add s q) n);
  let ka20 := nmin C (Nat.add s q);
  let ka21 := nmax D (Nat.sub (Nat.add e L) q);
  let ka22 := nmin E (Nat.sub (Nat.add d q) Z);
  let ka23 := nmax F (Nat.sub (Nat.add N L) q);
  let ka24 := nmin G (Nat.sub (Nat.add d q) ad);
  let ka25 := nmax H (Nat.sub (Nat.add P L) q);
  let ka26 := nmin I (Nat.sub (Nat.add d q) af);
  let ka27 := nmax J (Nat.sub (Nat.add R L) q);
  let ka28 := nmin K (Nat.sub (Nat.add d q) n);
  let ka29 := nmin M (Nat.add d q);
  let ka30 := nmin O (Nat.sub q ad);
  let ka31 := nmin Q (Nat.sub q af);
  let ka32 := nmin S (Nat.sub q n);
  let ka33 := nmin q q;
  let ka34 := nmax V (Nat.sub (Nat.add P Z) q);
  let ka35 := nmin W (Nat.sub q (Nat.add e af));
  let ka36 := nmax X (Nat.sub (Nat.add R Z) q);
  let ka37 := nmin Y (Nat.sub q (Nat.add e n));
  let ka38 := nmin aa (Nat.sub q e);
  let ka39 := nmax ab (Nat.sub (Nat.add R ad) q);
  let ka40 := nmin ac (Nat.sub q (Nat.add N n));
  let ka41 := nmin ae (Nat.sub q N);
  let ka42 := nmin ag (Nat.sub q P);
  let p := ih pos ka0 ka1 ka2 d e ka3 ka4 ka5 ka6 ka7 ka8 ka9 n ka10 ka11 s ka12 ka13 ka14 ka15 ka16 ka17 ka18 ka19 B ka20 ka21 ka22 ka23 ka24 ka25 ka26 ka27 ka28 L ka29 N ka30 P ka31 R ka32 T ka33 ka34 ka35 ka36 ka37 Z ka38 ka39 ka40 ad ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q r) M);
    let kb1 := nmin b (Nat.sub C (Nat.add q c));
    let kb2 := nmin d (Nat.sub M q);
    let kb3 := nmax e (Nat.sub q aa);
    let kb4 := nmax g (Nat.sub q (Nat.add ae f));
    let kb5 := nmin h (Nat.sub (Nat.add aa O) q);
    let kb6 := nmax i (Nat.sub q (Nat.add ag O));
    let kb7 := nmin j (Nat.sub (Nat.add ae Q) q);
    let kb8 := nmax l (Nat.sub q (Nat.add o Q));
    let kb9 := nmin m (Nat.sub (Nat.add ag S) q);
    let kb10 := nmax n (Nat.sub q S);
    let kb11 := nmin s (Nat.sub C q);
    let kb12 := nmax t (Nat.sub (Nat.add q r) aa);
    let kb13 := nmin u (Nat.sub (Nat.add C f) q);
    let kb14 := nmax v (Nat.sub (Nat.add q r) ae);
    let kb15 := nmin w (Nat.sub (Nat.add C O) q);
    let kb16 := nmax x (Nat.sub (Nat.add q r) ag);
    let kb17 := nmin y (Nat.sub (Nat.add C Q) q);
    let kb18 := nmax z (Nat.sub (Nat.add q r) o);
    let kb19 := nmin A (Nat.sub (Nat.add C S) q);
    let kb20 := nmax B (Nat.add q r);
    let kb21 := nmax D (Nat.sub (Nat.add q c) aa);
    let kb22 := nmin E (Nat.sub (Nat.add M f) q);
    let kb23 := nmax F (Nat.sub (Nat.add q c) ae);
    let kb24 := nmin G (Nat.sub (Nat.add M O) q);
    let kb25 := nmax H (Nat.sub (Nat.add q c) ag);
    let kb26 := nmin I (Nat.sub (Nat.add M Q) q);
    let kb27 := nmax J (Nat.sub (Nat.add q c) o);
    let kb28 := nmin K (Nat.sub (Nat.add M S) q);
    let kb29 := nmax L (Nat.add q c);
    let kb30 := nmax N (Nat.sub q ae);
    let kb31 := nmax P (Nat.sub q ag);
    let kb32 := nmax R (Nat.sub q o);
    let kb33 := nmax q q;
    let kb34 := nmax V (Nat.sub q (Nat.add ag f));
    let kb35 := nmin W (Nat.sub (Nat.add aa Q) q);
    let kb36 := nmax X (Nat.sub q (Nat.add o f));
    let kb37 := nmin Y (Nat.sub (Nat.add aa S) q);
    let kb38 := nmax Z (Nat.sub q f);
    let kb39 := nmax ab (Nat.sub q (Nat.add o O));
    let kb40 := nmin ac (Nat.sub (Nat.add ae S) q);
    let kb41 := nmax ad (Nat.sub q O);
    let kb42 := nmax af (Nat.sub q Q);
    ih p kb0 kb1 c kb2 kb3 f kb4 kb5 kb6 kb7 kb8 kb9 kb10 o r kb11 kb12 kb13 kb14 kb15 kb16 kb17 kb18 kb19 kb20 C kb21 kb22 kb23 kb24 kb25 kb26 kb27 kb28 kb29 M kb30 O kb31 Q kb32 S kb33 U kb34 kb35 kb36 kb37 kb38 aa kb39 kb40 kb41 ae kb42 ag ah) 0 (Nat.beq p 0)

def ssplit35 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add V W) 1;
  let ka0 := nmax a (Nat.sub x (Nat.add E q));
  let ka1 := nmin b (Nat.sub (Nat.add u q) H);
  let ka2 := nmax c (Nat.sub H (Nat.add f q));
  let ka3 := nmin d (Nat.sub (Nat.add E q) P);
  let ka4 := nmax e (Nat.sub P q);
  let ka5 := nmin h (Nat.sub q i);
  let ka6 := nmin j (Nat.sub q g);
  let ka7 := nmax l (Nat.sub X q);
  let ka8 := nmax n (Nat.sub Z (Nat.add q m));
  let ka9 := nmin o (Nat.sub (Nat.add q ag) X);
  let ka10 := nmax r (Nat.sub x (Nat.add f q));
  let ka11 := nmin s (Nat.sub (Nat.add u q) P);
  let ka12 := nmax t (Nat.sub x q);
  let ka13 := nmax v (Nat.sub (Nat.add g x) q);
  let ka14 := nmin w (Nat.sub (Nat.add u q) i);
  let ka15 := nmin y (Nat.add u q);
  let ka16 := nmax z (Nat.sub (Nat.add X x) q);
  let ka17 := nmin A (Nat.add (Nat.add u q) m);
  let ka18 := nmax B (Nat.sub (Nat.add Z x) q);
  let ka19 := nmin C (Nat.add (Nat.add u q) ag);
  let ka20 := nmax D (Nat.sub H q);
  let ka21 := nmax F (Nat.sub (Nat.add g H) q);
  let ka22 := nmin G (Nat.sub (Nat.add E q) i);
  let ka23 := nmin I (Nat.add E q);
  let ka24 := nmax J (Nat.sub (Nat.add X H) q);
  let ka25 := nmin K (Nat.add (Nat.add E q) m);
  let ka26 := nmax L (Nat.sub (Nat.add Z H) q);
  let ka27 := nmin M (Nat.add (Nat.add E q) ag);
  let ka28 := nmax N (Nat.sub (Nat.add g P) q);
  let ka29 := nmin O (Nat.sub (Nat.add f q) i);
  let ka30 := nmin Q (Nat.add f q);
  let ka31 := nmax R (Nat.sub (Nat.add X P) q);
  let ka32 := nmin S (Nat.add (Nat.add f q) m);
  let ka33 := nmax T (Nat.sub (Nat.add Z P) q);
  let ka34 := nmin U (Nat.add (Nat.add f q) ag);
  let ka35 := nmin q q;
  let ka36 := nmin Y (Nat.add q m);
  let ka37 := nmin aa (Nat.add q ag);
  let ka38 := nmax ab (Nat.sub (Nat.add X i) q);
  let ka39 := nmin ac (Nat.sub (Nat.add q m) g);
  let ka40 := nmax ad (Nat.sub (Nat.add Z i) q);
  let ka41 := nmin ae (Nat.sub (Nat.add q ag) g);
  let ka42 := nmax af (Nat.sub Z q);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 f g ka5 i ka6 ka7 m ka8 ka9 ka10 ka11 ka12 u ka13 ka14 x ka15 ka16 ka17 ka18 ka19 ka20 E ka21 ka22 H ka23 ka24 ka25 ka26 ka27 ka28 ka29 P ka30 ka31 ka32 ka33 ka34 V ka35 X ka36 Z ka37 ka38 ka39 ka40 ka41 ka42 ag ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q t) I);
    let kb1 := nmin b (Nat.sub y (Nat.add q D));
    let kb2 := nmax c (Nat.sub (Nat.add q D) Q);
    let kb3 := nmin d (Nat.sub I (Nat.add q e));
    let kb4 := nmin f (Nat.sub Q q);
    let kb5 := nmax g (Nat.sub q j);
    let kb6 := nmax i (Nat.sub q h);
    let kb7 := nmin m (Nat.sub Y q);
    let kb8 := nmax n (Nat.sub (Nat.add af q) Y);
    let kb9 := nmin o (Nat.sub aa (Nat.add l q));
    let kb10 := nmax r (Nat.sub (Nat.add q t) Q);
    let kb11 := nmin s (Nat.sub y (Nat.add q e));
    let kb12 := nmin u (Nat.sub y q);
    let kb13 := nmax v (Nat.sub (Nat.add q t) j);
    let kb14 := nmin w (Nat.sub (Nat.add y h) q);
    let kb15 := nmax x (Nat.add q t);
    let kb16 := nmax z (Nat.add (Nat.add l q) t);
    let kb17 := nmin A (Nat.sub (Nat.add y Y) q);
    let kb18 := nmax B (Nat.add (Nat.add af q) t);
    let kb19 := nmin C (Nat.sub (Nat.add y aa) q);
    let kb20 := nmin E (Nat.sub I q);
    let kb21 := nmax F (Nat.sub (Nat.add q D) j);
    let kb22 := nmin G (Nat.sub (Nat.add I h) q);
    let kb23 := nmax H (Nat.add q D);
    let kb24 := nmax J (Nat.add (Nat.add l q) D);
    let kb25 := nmin K (Nat.sub (Nat.add I Y) q);
    let kb26 := nmax L (Nat.add (Nat.add af q) D);
    let kb27 := nmin M (Nat.sub (Nat.add I aa) q);
    let kb28 := nmax N (Nat.sub (Nat.add q e) j);
    let kb29 := nmin O (Nat.sub (Nat.add Q h) q);
    let kb30 := nmax P (Nat.add q e);
    let kb31 := nmax R (Nat.add (Nat.add l q) e);
    let kb32 := nmin S (Nat.sub (Nat.add Q Y) q);
    let kb33 := nmax T (Nat.add (Nat.add af q) e);
    let kb34 := nmin U (Nat.sub (Nat.add Q aa) q);
    let kb35 := nmax q q;
    let kb36 := nmax X (Nat.add l q);
    let kb37 := nmax Z (Nat.add af q);
    let kb38 := nmax ab (Nat.sub (Nat.add l q) h);
    let kb39 := nmin ac (Nat.sub (Nat.add j Y) q);
    let kb40 := nmax ad (Nat.sub (Nat.add af q) h);
    let kb41 := nmin ae (Nat.sub (Nat.add j aa) q);
    let kb42 := nmin ag (Nat.sub aa q);
    ih p kb0 kb1 kb2 kb3 e kb4 kb5 h kb6 j l kb7 kb8 kb9 kb10 kb11 t kb12 kb13 kb14 kb15 y kb16 kb17 kb18 kb19 D kb20 kb21 kb22 kb23 I kb24 kb25 kb26 kb27 kb28 kb29 kb30 Q kb31 kb32 kb33 kb34 kb35 W kb36 Y kb37 aa kb38 kb39 kb40 kb41 af kb42 ah) 0 (Nat.beq p 0)

def ssplit36 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add X Y) 1;
  let ka0 := nmax a (Nat.sub z (Nat.add E q));
  let ka1 := nmin b (Nat.sub (Nat.add u q) J);
  let ka2 := nmax c (Nat.sub J (Nat.add f q));
  let ka3 := nmin d (Nat.sub (Nat.add E q) R);
  let ka4 := nmax e (Nat.sub R q);
  let ka5 := nmin h (Nat.sub q ab);
  let ka6 := nmax i (Nat.sub (Nat.add V ab) q);
  let ka7 := nmin j (Nat.sub q (Nat.add g l));
  let ka8 := nmin m (Nat.sub q V);
  let ka9 := nmax n (Nat.sub Z q);
  let ka10 := nmax r (Nat.sub z (Nat.add f q));
  let ka11 := nmin s (Nat.sub (Nat.add u q) R);
  let ka12 := nmax t (Nat.sub z q);
  let ka13 := nmax v (Nat.sub (Nat.add g z) q);
  let ka14 := nmin w (Nat.sub (Nat.add u q) ab);
  let ka15 := nmax x (Nat.sub (Nat.add V z) q);
  let ka16 := nmin y (Nat.sub (Nat.add u q) l);
  let ka17 := nmin A (Nat.add u q);
  let ka18 := nmax B (Nat.sub (Nat.add Z z) q);
  let ka19 := nmin C (Nat.add (Nat.add u q) o);
  let ka20 := nmax D (Nat.sub J q);
  let ka21 := nmax F (Nat.sub (Nat.add g J) q);
  let ka22 := nmin G (Nat.sub (Nat.add E q) ab);
  let ka23 := nmax H (Nat.sub (Nat.add V J) q);
  let ka24 := nmin I (Nat.sub (Nat.add E q) l);
  let ka25 := nmin K (Nat.add E q);
  let ka26 := nmax L (Nat.sub (Nat.add Z J) q);
  let ka27 := nmin M (Nat.add (Nat.add E q) o);
  let ka28 := nmax N (Nat.sub (Nat.add g R) q);
  let ka29 := nmin O (Nat.sub (Nat.add f q) ab);
  let ka30 := nmax P (Nat.sub (Nat.add V R) q);
  let ka31 := nmin Q (Nat.sub (Nat.add f q) l);
  let ka32 := nmin S (Nat.add f q);
  let ka33 := nmax T (Nat.sub (Nat.add Z R) q);
  let ka34 := nmin U (Nat.add (Nat.add f q) o);
  let ka35 := nmin W (Nat.sub q l);
  let ka36 := nmin q q;
  let ka37 := nmin aa (Nat.add q o);
  let ka38 := nmin ac (Nat.sub q g);
  let ka39 := nmax ad (Nat.sub (Nat.add Z ab) q);
  let ka40 := nmin ae (Nat.sub (Nat.add q o) g);
  let ka41 := nmax af (Nat.sub (Nat.add Z l) q);
  let ka42 := nmin ag (Nat.sub (Nat.add q o) V);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 f g ka5 ka6 ka7 l ka8 ka9 o ka10 ka11 ka12 u ka13 ka14 ka15 ka16 z ka17 ka18 ka19 ka20 E ka21 ka22 ka23 ka24 J ka25 ka26 ka27 ka28 ka29 ka30 ka31 R ka32 ka33 ka34 V ka35 X ka36 Z ka37 ab ka38 ka39 ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q t) K);
    let kb1 := nmin b (Nat.sub A (Nat.add q D));
    let kb2 := nmax c (Nat.sub (Nat.add q D) S);
    let kb3 := nmin d (Nat.sub K (Nat.add q e));
    let kb4 := nmin f (Nat.sub S q);
    let kb5 := nmax g (Nat.sub q ac);
    let kb6 := nmax i (Nat.sub q (Nat.add m h));
    let kb7 := nmin j (Nat.sub (Nat.add ac W) q);
    let kb8 := nmax l (Nat.sub q W);
    let kb9 := nmin o (Nat.sub aa q);
    let kb10 := nmax r (Nat.sub (Nat.add q t) S);
    let kb11 := nmin s (Nat.sub A (Nat.add q e));
    let kb12 := nmin u (Nat.sub A q);
    let kb13 := nmax v (Nat.sub (Nat.add q t) ac);
    let kb14 := nmin w (Nat.sub (Nat.add A h) q);
    let kb15 := nmax x (Nat.sub (Nat.add q t) m);
    let kb16 := nmin y (Nat.sub (Nat.add A W) q);
    let kb17 := nmax z (Nat.add q t);
    let kb18 := nmax B (Nat.add (Nat.add n q) t);
    let kb19 := nmin C (Nat.sub (Nat.add A aa) q);
    let kb20 := nmin E (Nat.sub K q);
    let kb21 := nmax F (Nat.sub (Nat.add q D) ac);
    let kb22 := nmin G (Nat.sub (Nat.add K h) q);
    let kb23 := nmax H (Nat.sub (Nat.add q D) m);
    let kb24 := nmin I (Nat.sub (Nat.add K W) q);
    let kb25 := nmax J (Nat.add q D);
    let kb26 := nmax L (Nat.add (Nat.add n q) D);
    let kb27 := nmin M (Nat.sub (Nat.add K aa) q);
    let kb28 := nmax N (Nat.sub (Nat.add q e) ac);
    let kb29 := nmin O (Nat.sub (Nat.add S h) q);
    let kb30 := nmax P (Nat.sub (Nat.add q e) m);
    let kb31 := nmin Q (Nat.sub (Nat.add S W) q);
    let kb32 := nmax R (Nat.add q e);
    let kb33 := nmax T (Nat.add (Nat.add n q) e);
    let kb34 := nmin U (Nat.sub (Nat.add S aa) q);
    let kb35 := nmax V (Nat.sub q m);
    let kb36 := nmax q q;
    let kb37 := nmax Z (Nat.add n q);
    let kb38 := nmax ab (Nat.sub q h);
    let kb39 := nmax ad (Nat.sub (Nat.add n q) h);
    let kb40 := nmin ae (Nat.sub (Nat.add ac aa) q);
    let kb41 := nmax af (Nat.sub (Nat.add n q) W);
    let kb42 := nmin ag (Nat.sub (Nat.add m aa) q);
    ih p kb0 kb1 kb2 kb3 e kb4 kb5 h kb6 kb7 kb8 m n kb9 kb10 kb11 t kb12 kb13 kb14 kb15 kb16 kb17 A kb18 kb19 D kb20 kb21 kb22 kb23 kb24 kb25 K kb26 kb27 kb28 kb29 kb30 kb31 kb32 S kb33 kb34 kb35 W kb36 Y kb37 aa kb38 ac kb39 kb40 kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit37 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add Z aa) 1;
  let ka0 := nmax a (Nat.sub B (Nat.add E q));
  let ka1 := nmin b (Nat.sub (Nat.add u q) L);
  let ka2 := nmax c (Nat.sub L (Nat.add f q));
  let ka3 := nmin d (Nat.sub (Nat.add E q) T);
  let ka4 := nmax e (Nat.sub T q);
  let ka5 := nmin h (Nat.sub q ad);
  let ka6 := nmax i (Nat.sub (Nat.add V ad) q);
  let ka7 := nmin j (Nat.sub q (Nat.add g af));
  let ka8 := nmax l (Nat.sub (Nat.add X af) q);
  let ka9 := nmin m (Nat.sub q (Nat.add V n));
  let ka10 := nmin o (Nat.sub q X);
  let ka11 := nmax r (Nat.sub B (Nat.add f q));
  let ka12 := nmin s (Nat.sub (Nat.add u q) T);
  let ka13 := nmax t (Nat.sub B q);
  let ka14 := nmax v (Nat.sub (Nat.add g B) q);
  let ka15 := nmin w (Nat.sub (Nat.add u q) ad);
  let ka16 := nmax x (Nat.sub (Nat.add V B) q);
  let ka17 := nmin y (Nat.sub (Nat.add u q) af);
  let ka18 := nmax z (Nat.sub (Nat.add X B) q);
  let ka19 := nmin A (Nat.sub (Nat.add u q) n);
  let ka20 := nmin C (Nat.add u q);
  let ka21 := nmax D (Nat.sub L q);
  let ka22 := nmax F (Nat.sub (Nat.add g L) q);
  let ka23 := nmin G (Nat.sub (Nat.add E q) ad);
  let ka24 := nmax H (Nat.sub (Nat.add V L) q);
  let ka25 := nmin I (Nat.sub (Nat.add E q) af);
  let ka26 := nmax J (Nat.sub (Nat.add X L) q);
  let ka27 := nmin K (Nat.sub (Nat.add E q) n);
  let ka28 := nmin M (Nat.add E q);
  let ka29 := nmax N (Nat.sub (Nat.add g T) q);
  let ka30 := nmin O (Nat.sub (Nat.add f q) ad);
  let ka31 := nmax P (Nat.sub (Nat.add V T) q);
  let ka32 := nmin Q (Nat.sub (Nat.add f q) af);
  let ka33 := nmax R (Nat.sub (Nat.add X T) q);
  let ka34 := nmin S (Nat.sub (Nat.add f q) n);
  let ka35 := nmin U (Nat.add f q);
  let ka36 := nmin W (Nat.sub q af);
  let ka37 := nmin Y (Nat.sub q n);
  let ka38 := nmin q q;
  let ka39 := nmax ab (Nat.sub (Nat.add X ad) q);
  let ka40 := nmin ac (Nat.sub q (Nat.add g n));
  let ka41 := nmin ae (Nat.sub q g);
  let ka42 := nmin ag (Nat.sub q V);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 f g ka5 ka6 ka7 ka8 ka9 n ka10 ka11 ka12 ka13 u ka14 ka15 ka16 ka17 ka18 ka19 B ka20 ka21 E ka22 ka23 ka24 ka25 ka26 ka27 L ka28 ka29 ka30 ka31 ka32 ka33 ka34 T ka35 V ka36 X ka37 Z ka38 ka39 ka40 ad ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q t) M);
    let kb1 := nmin b (Nat.sub C (Nat.add q D));
    let kb2 := nmax c (Nat.sub (Nat.add q D) U);
    let kb3 := nmin d (Nat.sub M (Nat.add q e));
    let kb4 := nmin f (Nat.sub U q);
    let kb5 := nmax g (Nat.sub q ae);
    let kb6 := nmax i (Nat.sub q (Nat.add ag h));
    let kb7 := nmin j (Nat.sub (Nat.add ae W) q);
    let kb8 := nmax l (Nat.sub q (Nat.add o W));
    let kb9 := nmin m (Nat.sub (Nat.add ag Y) q);
    let kb10 := nmax n (Nat.sub q Y);
    let kb11 := nmax r (Nat.sub (Nat.add q t) U);
    let kb12 := nmin s (Nat.sub C (Nat.add q e));
    let kb13 := nmin u (Nat.sub C q);
    let kb14 := nmax v (Nat.sub (Nat.add q t) ae);
    let kb15 := nmin w (Nat.sub (Nat.add C h) q);
    let kb16 := nmax x (Nat.sub (Nat.add q t) ag);
    let kb17 := nmin y (Nat.sub (Nat.add C W) q);
    let kb18 := nmax z (Nat.sub (Nat.add q t) o);
    let kb19 := nmin A (Nat.sub (Nat.add C Y) q);
    let kb20 := nmax B (Nat.add q t);
    let kb21 := nmin E (Nat.sub M q);
    let kb22 := nmax F (Nat.sub (Nat.add q D) ae);
    let kb23 := nmin G (Nat.sub (Nat.add M h) q);
    let kb24 := nmax H (Nat.sub (Nat.add q D) ag);
    let kb25 := nmin I (Nat.sub (Nat.add M W) q);
    let kb26 := nmax J (Nat.sub (Nat.add q D) o);
    let kb27 := nmin K (Nat.sub (Nat.add M Y) q);
    let kb28 := nmax L (Nat.add q D);
    let kb29 := nmax N (Nat.sub (Nat.add q e) ae);
    let kb30 := nmin O (Nat.sub (Nat.add U h) q);
    let kb31 := nmax P (Nat.sub (Nat.add q e) ag);
    let kb32 := nmin Q (Nat.sub (Nat.add U W) q);
    let kb33 := nmax R (Nat.sub (Nat.add q e) o);
    let kb34 := nmin S (Nat.sub (Nat.add U Y) q);
    let kb35 := nmax T (Nat.add q e);
    let kb36 := nmax V (Nat.sub q ag);
    let kb37 := nmax X (Nat.sub q o);
    let kb38 := nmax q q;
    let kb39 := nmax ab (Nat.sub q (Nat.add o h));
    let kb40 := nmin ac (Nat.sub (Nat.add ae Y) q);
    let kb41 := nmax ad (Nat.sub q h);
    let kb42 := nmax af (Nat.sub q W);
    ih p kb0 kb1 kb2 kb3 e kb4 kb5 h kb6 kb7 kb8 kb9 kb10 o kb11 kb12 t kb13 kb14 kb15 kb16 kb17 kb18 kb19 kb20 C D kb21 kb22 kb23 kb24 kb25 kb26 kb27 kb28 M kb29 kb30 kb31 kb32 kb33 kb34 kb35 U kb36 W kb37 Y kb38 aa kb39 kb40 kb41 ae kb42 ag ah) 0 (Nat.beq p 0)

def ssplit46 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add ab ac) 1;
  let ka0 := nmax a (Nat.sub z (Nat.add G q));
  let ka1 := nmin b (Nat.sub (Nat.add w q) J);
  let ka2 := nmax c (Nat.sub J (Nat.add O q));
  let ka3 := nmin d (Nat.sub (Nat.add G q) R);
  let ka4 := nmax e (Nat.sub R (Nat.add h q));
  let ka5 := nmin f (Nat.sub (Nat.add O q) X);
  let ka6 := nmax g (Nat.sub X q);
  let ka7 := nmin j (Nat.sub q l);
  let ka8 := nmin m (Nat.sub q i);
  let ka9 := nmax n (Nat.sub ad q);
  let ka10 := nmax r (Nat.sub z (Nat.add O q));
  let ka11 := nmin s (Nat.sub (Nat.add w q) R);
  let ka12 := nmax t (Nat.sub z (Nat.add h q));
  let ka13 := nmin u (Nat.sub (Nat.add w q) X);
  let ka14 := nmax v (Nat.sub z q);
  let ka15 := nmax x (Nat.sub (Nat.add i z) q);
  let ka16 := nmin y (Nat.sub (Nat.add w q) l);
  let ka17 := nmin A (Nat.add w q);
  let ka18 := nmax B (Nat.sub (Nat.add ad z) q);
  let ka19 := nmin C (Nat.add (Nat.add w q) o);
  let ka20 := nmax D (Nat.sub J (Nat.add h q));
  let ka21 := nmin E (Nat.sub (Nat.add G q) X);
  let ka22 := nmax F (Nat.sub J q);
  let ka23 := nmax H (Nat.sub (Nat.add i J) q);
  let ka24 := nmin I (Nat.sub (Nat.add G q) l);
  let ka25 := nmin K (Nat.add G q);
  let ka26 := nmax L (Nat.sub (Nat.add ad J) q);
  let ka27 := nmin M (Nat.add (Nat.add G q) o);
  let ka28 := nmax N (Nat.sub R q);
  let ka29 := nmax P (Nat.sub (Nat.add i R) q);
  let ka30 := nmin Q (Nat.sub (Nat.add O q) l);
  let ka31 := nmin S (Nat.add O q);
  let ka32 := nmax T (Nat.sub (Nat.add ad R) q);
  let ka33 := nmin U (Nat.add (Nat.add O q) o);
  let ka34 := nmax V (Nat.sub (Nat.add i X) q);
  let ka35 := nmin W (Nat.sub (Nat.add h q) l);
  let ka36 := nmin Y (Nat.add h q);
  let ka37 := nmax Z (Nat.sub (Nat.add ad X) q);
  let ka38 := nmin aa (Nat.add (Nat.add h q) o);
  let ka39 := nmin q q;
  let ka40 := nmin ae (Nat.add q o);
  let ka41 := nmax af (Nat.sub (Nat.add ad l) q);
  let ka42 := nmin ag (Nat.sub (Nat.add q o) i);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 h i ka7 l ka8 ka9 o ka10 ka11 ka12 ka13 ka14 w ka15 ka16 z ka17 ka18 ka19 ka20 ka21 ka22 G ka23 ka24 J ka25 ka26 ka27 ka28 O ka29 ka30 R ka31 ka32 ka33 ka34 ka35 X ka36 ka37 ka38 ab ka39 ad ka40 ka41 ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q v) K);
    let kb1 := nmin b (Nat.sub A (Nat.add q F));
    let kb2 := nmax c (Nat.sub (Nat.add q F) S);
    let kb3 := nmin d (Nat.sub K (Nat.add q N));
    let kb4 := nmax e (Nat.sub (Nat.add q N) Y);
    let kb5 := nmin f (Nat.sub S (Nat.add q g));
    let kb6 := nmin h (Nat.sub Y q);
    let kb7 := nmax i (Nat.sub q m);
    let kb8 := nmax l (Nat.sub q j);
    let kb9 := nmin o (Nat.sub ae q);
    let kb10 := nmax r (Nat.sub (Nat.add q v) S);
    let kb11 := nmin s (Nat.sub A (Nat.add q N));
    let kb12 := nmax t (Nat.sub (Nat.add q v) Y);
    let kb13 := nmin u (Nat.sub A (Nat.add q g));
    let kb14 := nmin w (Nat.sub A q);
    let kb15 := nmax x (Nat.sub (Nat.add q v) m);
    let kb16 := nmin y (Nat.sub (Nat.add A j) q);
    let kb17 := nmax z (Nat.add q v);
    let kb18 := nmax B (Nat.add (Nat.add n q) v);
    let kb19 := nmin C (Nat.sub (Nat.add A ae) q);
    let kb20 := nmax D (Nat.sub (Nat.add q F) Y);
    let kb21 := nmin E (Nat.sub K (Nat.add q g));
    let kb22 := nmin G (Nat.sub K q);
    let kb23 := nmax H (Nat.sub (Nat.add q F) m);
    let kb24 := nmin I (Nat.sub (Nat.add K j) q);
    let kb25 := nmax J (Nat.add q F);
    let kb26 := nmax L (Nat.add (Nat.add n q) F);
    let kb27 := nmin M (Nat.sub (Nat.add K ae) q);
    let kb28 := nmin O (Nat.sub S q);
    let kb29 := nmax P (Nat.sub (Nat.add q N) m);
    let kb30 := nmin Q (Nat.sub (Nat.add S j) q);
    let kb31 := nmax R (Nat.add q N);
    let kb32 := nmax T (Nat.add (Nat.add n q) N);
    let kb33 := nmin U (Nat.sub (Nat.add S ae) q);
    let kb34 := nmax V (Nat.sub (Nat.add q g) m);
    let kb35 := nmin W (Nat.sub (Nat.add Y j) q);
    let kb36 := nmax X (Nat.add q g);
    let kb37 := nmax Z (Nat.add (Nat.add n q) g);
    let kb38 := nmin aa (Nat.sub (Nat.add Y ae) q);
    let kb39 := nmax q q;
    let kb40 := nmax ad (Nat.add n q);
    let kb41 := nmax af (Nat.sub (Nat.add n q) j);
    let kb42 := nmin ag (Nat.sub (Nat.add m ae) q);
    ih p kb0 kb1 kb2 kb3 kb4 kb5 g kb6 kb7 j kb8 m n kb9 kb10 kb11 kb12 kb13 v kb14 kb15 kb16 kb17 A kb18 kb19 kb20 kb21 F kb22 kb23 kb24 kb25 K kb26 kb27 N kb28 kb29 kb30 kb31 S kb32 kb33 kb34 kb35 kb36 Y kb37 kb38 kb39 ac kb40 ae kb41 kb42 ah) 0 (Nat.beq p 0)

def ssplit47 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add ad ae) 1;
  let ka0 := nmax a (Nat.sub B (Nat.add G q));
  let ka1 := nmin b (Nat.sub (Nat.add w q) L);
  let ka2 := nmax c (Nat.sub L (Nat.add O q));
  let ka3 := nmin d (Nat.sub (Nat.add G q) T);
  let ka4 := nmax e (Nat.sub T (Nat.add h q));
  let ka5 := nmin f (Nat.sub (Nat.add O q) Z);
  let ka6 := nmax g (Nat.sub Z q);
  let ka7 := nmin j (Nat.sub q af);
  let ka8 := nmax l (Nat.sub (Nat.add ab af) q);
  let ka9 := nmin m (Nat.sub q (Nat.add i n));
  let ka10 := nmin o (Nat.sub q ab);
  let ka11 := nmax r (Nat.sub B (Nat.add O q));
  let ka12 := nmin s (Nat.sub (Nat.add w q) T);
  let ka13 := nmax t (Nat.sub B (Nat.add h q));
  let ka14 := nmin u (Nat.sub (Nat.add w q) Z);
  let ka15 := nmax v (Nat.sub B q);
  let ka16 := nmax x (Nat.sub (Nat.add i B) q);
  let ka17 := nmin y (Nat.sub (Nat.add w q) af);
  let ka18 := nmax z (Nat.sub (Nat.add ab B) q);
  let ka19 := nmin A (Nat.sub (Nat.add w q) n);
  let ka20 := nmin C (Nat.add w q);
  let ka21 := nmax D (Nat.sub L (Nat.add h q));
  let ka22 := nmin E (Nat.sub (Nat.add G q) Z);
  let ka23 := nmax F (Nat.sub L q);
  let ka24 := nmax H (Nat.sub (Nat.add i L) q);
  let ka25 := nmin I (Nat.sub (Nat.add G q) af);
  let ka26 := nmax J (Nat.sub (Nat.add ab L) q);
  let ka27 := nmin K (Nat.sub (Nat.add G q) n);
  let ka28 := nmin M (Nat.add G q);
  let ka29 := nmax N (Nat.sub T q);
  let ka30 := nmax P (Nat.sub (Nat.add i T) q);
  let ka31 := nmin Q (Nat.sub (Nat.add O q) af);
  let ka32 := nmax R (Nat.sub (Nat.add ab T) q);
  let ka33 := nmin S (Nat.sub (Nat.add O q) n);
  let ka34 := nmin U (Nat.add O q);
  let ka35 := nmax V (Nat.sub (Nat.add i Z) q);
  let ka36 := nmin W (Nat.sub (Nat.add h q) af);
  let ka37 := nmax X (Nat.sub (Nat.add ab Z) q);
  let ka38 := nmin Y (Nat.sub (Nat.add h q) n);
  let ka39 := nmin aa (Nat.add h q);
  let ka40 := nmin ac (Nat.sub q n);
  let ka41 := nmin q q;
  let ka42 := nmin ag (Nat.sub q i);
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 h i ka7 ka8 ka9 n ka10 ka11 ka12 ka13 ka14 ka15 w ka16 ka17 ka18 ka19 B ka20 ka21 ka22 ka23 G ka24 ka25 ka26 ka27 L ka28 ka29 O ka30 ka31 ka32 ka33 T ka34 ka35 ka36 ka37 ka38 Z ka39 ab ka40 ad ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q v) M);
    let kb1 := nmin b (Nat.sub C (Nat.add q F));
    let kb2 := nmax c (Nat.sub (Nat.add q F) U);
    let kb3 := nmin d (Nat.sub M (Nat.add q N));
    let kb4 := nmax e (Nat.sub (Nat.add q N) aa);
    let kb5 := nmin f (Nat.sub U (Nat.add q g));
    let kb6 := nmin h (Nat.sub aa q);
    let kb7 := nmax i (Nat.sub q ag);
    let kb8 := nmax l (Nat.sub q (Nat.add o j));
    let kb9 := nmin m (Nat.sub (Nat.add ag ac) q);
    let kb10 := nmax n (Nat.sub q ac);
    let kb11 := nmax r (Nat.sub (Nat.add q v) U);
    let kb12 := nmin s (Nat.sub C (Nat.add q N));
    let kb13 := nmax t (Nat.sub (Nat.add q v) aa);
    let kb14 := nmin u (Nat.sub C (Nat.add q g));
    let kb15 := nmin w (Nat.sub C q);
    let kb16 := nmax x (Nat.sub (Nat.add q v) ag);
    let kb17 := nmin y (Nat.sub (Nat.add C j) q);
    let kb18 := nmax z (Nat.sub (Nat.add q v) o);
    let kb19 := nmin A (Nat.sub (Nat.add C ac) q);
    let kb20 := nmax B (Nat.add q v);
    let kb21 := nmax D (Nat.sub (Nat.add q F) aa);
    let kb22 := nmin E (Nat.sub M (Nat.add q g));
    let kb23 := nmin G (Nat.sub M q);
    let kb24 := nmax H (Nat.sub (Nat.add q F) ag);
    let kb25 := nmin I (Nat.sub (Nat.add M j) q);
    let kb26 := nmax J (Nat.sub (Nat.add q F) o);
    let kb27 := nmin K (Nat.sub (Nat.add M ac) q);
    let kb28 := nmax L (Nat.add q F);
    let kb29 := nmin O (Nat.sub U q);
    let kb30 := nmax P (Nat.sub (Nat.add q N) ag);
    let kb31 := nmin Q (Nat.sub (Nat.add U j) q);
    let kb32 := nmax R (Nat.sub (Nat.add q N) o);
    let kb33 := nmin S (Nat.sub (Nat.add U ac) q);
    let kb34 := nmax T (Nat.add q N);
    let kb35 := nmax V (Nat.sub (Nat.add q g) ag);
    let kb36 := nmin W (Nat.sub (Nat.add aa j) q);
    let kb37 := nmax X (Nat.sub (Nat.add q g) o);
    let kb38 := nmin Y (Nat.sub (Nat.add aa ac) q);
    let kb39 := nmax Z (Nat.add q g);
    let kb40 := nmax ab (Nat.sub q o);
    let kb41 := nmax q q;
    let kb42 := nmax af (Nat.sub q j);
    ih p kb0 kb1 kb2 kb3 kb4 kb5 g kb6 kb7 j kb8 kb9 kb10 o kb11 kb12 kb13 kb14 v kb15 kb16 kb17 kb18 kb19 kb20 C kb21 kb22 F kb23 kb24 kb25 kb26 kb27 kb28 M N kb29 kb30 kb31 kb32 kb33 kb34 U kb35 kb36 kb37 kb38 kb39 aa kb40 ac kb41 ae kb42 ag ah) 0 (Nat.beq p 0)

def ssplit57 (ih : WF) (pos a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  let q := Nat.shiftRight (Nat.add af ag) 1;
  let ka0 := nmax a (Nat.sub B (Nat.add I q));
  let ka1 := nmin b (Nat.sub (Nat.add y q) L);
  let ka2 := nmax c (Nat.sub L (Nat.add Q q));
  let ka3 := nmin d (Nat.sub (Nat.add I q) T);
  let ka4 := nmax e (Nat.sub T (Nat.add W q));
  let ka5 := nmin f (Nat.sub (Nat.add Q q) Z);
  let ka6 := nmax g (Nat.sub Z (Nat.add j q));
  let ka7 := nmin h (Nat.sub (Nat.add W q) ad);
  let ka8 := nmax i (Nat.sub ad q);
  let ka9 := nmin m (Nat.sub q n);
  let ka10 := nmin o (Nat.sub q l);
  let ka11 := nmax r (Nat.sub B (Nat.add Q q));
  let ka12 := nmin s (Nat.sub (Nat.add y q) T);
  let ka13 := nmax t (Nat.sub B (Nat.add W q));
  let ka14 := nmin u (Nat.sub (Nat.add y q) Z);
  let ka15 := nmax v (Nat.sub B (Nat.add j q));
  let ka16 := nmin w (Nat.sub (Nat.add y q) ad);
  let ka17 := nmax x (Nat.sub B q);
  let ka18 := nmax z (Nat.sub (Nat.add l B) q);
  let ka19 := nmin A (Nat.sub (Nat.add y q) n);
  let ka20 := nmin C (Nat.add y q);
  let ka21 := nmax D (Nat.sub L (Nat.add W q));
  let ka22 := nmin E (Nat.sub (Nat.add I q) Z);
  let ka23 := nmax F (Nat.sub L (Nat.add j q));
  let ka24 := nmin G (Nat.sub (Nat.add I q) ad);
  let ka25 := nmax H (Nat.sub L q);
  let ka26 := nmax J (Nat.sub (Nat.add l L) q);
  let ka27 := nmin K (Nat.sub (Nat.add I q) n);
  let ka28 := nmin M (Nat.add I q);
  let ka29 := nmax N (Nat.sub T (Nat.add j q));
  let ka30 := nmin O (Nat.sub (Nat.add Q q) ad);
  let ka31 := nmax P (Nat.sub T q);
  let ka32 := nmax R (Nat.sub (Nat.add l T) q);
  let ka33 := nmin S (Nat.sub (Nat.add Q q) n);
  let ka34 := nmin U (Nat.add Q q);
  let ka35 := nmax V (Nat.sub Z q);
  let ka36 := nmax X (Nat.sub (Nat.add l Z) q);
  let ka37 := nmin Y (Nat.sub (Nat.add W q) n);
  let ka38 := nmin aa (Nat.add W q);
  let ka39 := nmax ab (Nat.sub (Nat.add l ad) q);
  let ka40 := nmin ac (Nat.sub (Nat.add j q) n);
  let ka41 := nmin ae (Nat.add j q);
  let ka42 := nmin q q;
  let p := ih pos ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 ka8 j l ka9 n ka10 ka11 ka12 ka13 ka14 ka15 ka16 ka17 y ka18 ka19 B ka20 ka21 ka22 ka23 ka24 ka25 I ka26 ka27 L ka28 ka29 ka30 ka31 Q ka32 ka33 T ka34 ka35 W ka36 ka37 Z ka38 ka39 ka40 ad ka41 af ka42 ah
  Bool.rec (motive := fun _ => ℕ) (let kb0 := nmax a (Nat.sub (Nat.add q x) M);
    let kb1 := nmin b (Nat.sub C (Nat.add q H));
    let kb2 := nmax c (Nat.sub (Nat.add q H) U);
    let kb3 := nmin d (Nat.sub M (Nat.add q P));
    let kb4 := nmax e (Nat.sub (Nat.add q P) aa);
    let kb5 := nmin f (Nat.sub U (Nat.add q V));
    let kb6 := nmax g (Nat.sub (Nat.add q V) ae);
    let kb7 := nmin h (Nat.sub aa (Nat.add q i));
    let kb8 := nmin j (Nat.sub ae q);
    let kb9 := nmax l (Nat.sub q o);
    let kb10 := nmax n (Nat.sub q m);
    let kb11 := nmax r (Nat.sub (Nat.add q x) U);
    let kb12 := nmin s (Nat.sub C (Nat.add q P));
    let kb13 := nmax t (Nat.sub (Nat.add q x) aa);
    let kb14 := nmin u (Nat.sub C (Nat.add q V));
    let kb15 := nmax v (Nat.sub (Nat.add q x) ae);
    let kb16 := nmin w (Nat.sub C (Nat.add q i));
    let kb17 := nmin y (Nat.sub C q);
    let kb18 := nmax z (Nat.sub (Nat.add q x) o);
    let kb19 := nmin A (Nat.sub (Nat.add C m) q);
    let kb20 := nmax B (Nat.add q x);
    let kb21 := nmax D (Nat.sub (Nat.add q H) aa);
    let kb22 := nmin E (Nat.sub M (Nat.add q V));
    let kb23 := nmax F (Nat.sub (Nat.add q H) ae);
    let kb24 := nmin G (Nat.sub M (Nat.add q i));
    let kb25 := nmin I (Nat.sub M q);
    let kb26 := nmax J (Nat.sub (Nat.add q H) o);
    let kb27 := nmin K (Nat.sub (Nat.add M m) q);
    let kb28 := nmax L (Nat.add q H);
    let kb29 := nmax N (Nat.sub (Nat.add q P) ae);
    let kb30 := nmin O (Nat.sub U (Nat.add q i));
    let kb31 := nmin Q (Nat.sub U q);
    let kb32 := nmax R (Nat.sub (Nat.add q P) o);
    let kb33 := nmin S (Nat.sub (Nat.add U m) q);
    let kb34 := nmax T (Nat.add q P);
    let kb35 := nmin W (Nat.sub aa q);
    let kb36 := nmax X (Nat.sub (Nat.add q V) o);
    let kb37 := nmin Y (Nat.sub (Nat.add aa m) q);
    let kb38 := nmax Z (Nat.add q V);
    let kb39 := nmax ab (Nat.sub (Nat.add q i) o);
    let kb40 := nmin ac (Nat.sub (Nat.add ae m) q);
    let kb41 := nmax ad (Nat.add q i);
    let kb42 := nmax q q;
    ih p kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 i kb8 kb9 m kb10 o kb11 kb12 kb13 kb14 kb15 kb16 x kb17 kb18 kb19 kb20 C kb21 kb22 kb23 kb24 H kb25 kb26 kb27 kb28 M kb29 kb30 P kb31 kb32 kb33 kb34 U V kb35 kb36 kb37 kb38 aa kb39 kb40 kb41 ae kb42 ag ah) 0 (Nat.beq p 0)

section
variable {ih : WF} (hih : WalkOK ih) (pos : ℕ)
include hih
set_option hygiene false in
/-- a split node's link: unfold, then the generic midpoint split -/
macro "pc_spl " n:ident c:term : term =>
  `(fun s h => by simp only [U, $n:ident] at h; exact sp_ok hih (pos := pos) $c h ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩)
theorem gsplit0_ok : CovK (gsplit0 ih pos) := pc_spl gsplit0 (cov_gmidC hSL hPR 0 rfl rfl (by decide))
theorem gsplit1_ok : CovK (gsplit1 ih pos) := pc_spl gsplit1 (cov_gmidC hSL hPR 1 rfl rfl (by decide))
theorem gsplit2_ok : CovK (gsplit2 ih pos) := pc_spl gsplit2 (cov_gmidC hSL hPR 2 rfl rfl (by decide))
theorem gsplit3_ok : CovK (gsplit3 ih pos) := pc_spl gsplit3 (cov_gmidC hSL hPR 3 rfl rfl (by decide))
theorem gsplit4_ok : CovK (gsplit4 ih pos) := pc_spl gsplit4 (cov_gmidC hSL hPR 4 rfl rfl (by decide))
theorem gsplit5_ok : CovK (gsplit5 ih pos) := pc_spl gsplit5 (cov_gmidC hSL hPR 5 rfl rfl (by decide))
theorem gsplit6_ok : CovK (gsplit6 ih pos) := pc_spl gsplit6 (cov_gmidC hSL hPR 6 rfl rfl (by decide))
theorem ssplit02_ok : CovK (ssplit02 ih pos) := pc_spl ssplit02 (cov_rmidC hSL hPR 0 rfl rfl (by decide))
theorem ssplit03_ok : CovK (ssplit03 ih pos) := pc_spl ssplit03 (cov_rmidC hSL hPR 1 rfl rfl (by decide))
theorem ssplit04_ok : CovK (ssplit04 ih pos) := pc_spl ssplit04 (cov_rmidC hSL hPR 2 rfl rfl (by decide))
theorem ssplit05_ok : CovK (ssplit05 ih pos) := pc_spl ssplit05 (cov_rmidC hSL hPR 3 rfl rfl (by decide))
theorem ssplit06_ok : CovK (ssplit06 ih pos) := pc_spl ssplit06 (cov_rmidC hSL hPR 4 rfl rfl (by decide))
theorem ssplit07_ok : CovK (ssplit07 ih pos) := pc_spl ssplit07 (cov_rmidC hSL hPR 5 rfl rfl (by decide))
theorem ssplit13_ok : CovK (ssplit13 ih pos) := pc_spl ssplit13 (cov_rmidC hSL hPR 6 rfl rfl (by decide))
theorem ssplit14_ok : CovK (ssplit14 ih pos) := pc_spl ssplit14 (cov_rmidC hSL hPR 7 rfl rfl (by decide))
theorem ssplit15_ok : CovK (ssplit15 ih pos) := pc_spl ssplit15 (cov_rmidC hSL hPR 8 rfl rfl (by decide))
theorem ssplit16_ok : CovK (ssplit16 ih pos) := pc_spl ssplit16 (cov_rmidC hSL hPR 9 rfl rfl (by decide))
theorem ssplit17_ok : CovK (ssplit17 ih pos) := pc_spl ssplit17 (cov_rmidC hSL hPR 10 rfl rfl (by decide))
theorem ssplit24_ok : CovK (ssplit24 ih pos) := pc_spl ssplit24 (cov_rmidC hSL hPR 11 rfl rfl (by decide))
theorem ssplit25_ok : CovK (ssplit25 ih pos) := pc_spl ssplit25 (cov_rmidC hSL hPR 12 rfl rfl (by decide))
theorem ssplit26_ok : CovK (ssplit26 ih pos) := pc_spl ssplit26 (cov_rmidC hSL hPR 13 rfl rfl (by decide))
theorem ssplit27_ok : CovK (ssplit27 ih pos) := pc_spl ssplit27 (cov_rmidC hSL hPR 14 rfl rfl (by decide))
theorem ssplit35_ok : CovK (ssplit35 ih pos) := pc_spl ssplit35 (cov_rmidC hSL hPR 15 rfl rfl (by decide))
theorem ssplit36_ok : CovK (ssplit36 ih pos) := pc_spl ssplit36 (cov_rmidC hSL hPR 16 rfl rfl (by decide))
theorem ssplit37_ok : CovK (ssplit37 ih pos) := pc_spl ssplit37 (cov_rmidC hSL hPR 17 rfl rfl (by decide))
theorem ssplit46_ok : CovK (ssplit46 ih pos) := pc_spl ssplit46 (cov_rmidC hSL hPR 18 rfl rfl (by decide))
theorem ssplit47_ok : CovK (ssplit47 ih pos) := pc_spl ssplit47 (cov_rmidC hSL hPR 19 rfl rfl (by decide))
theorem ssplit57_ok : CovK (ssplit57 ih pos) := pc_spl ssplit57 (cov_rmidC hSL hPR 20 rfl rfl (by decide))
end

/-- a split node: axis `0 … 6` a gap, `7 … 27` a pair (pair order) -/
def splitAx (ih : WF) (pos ax : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (zK) (ssplit57 ih pos) (Nat.beq ax 27)) (ssplit47 ih pos) (Nat.beq ax 26)) (ssplit46 ih pos) (Nat.beq ax 25)) (ssplit37 ih pos) (Nat.beq ax 24)) (ssplit36 ih pos) (Nat.beq ax 23)) (ssplit35 ih pos) (Nat.beq ax 22)) (ssplit27 ih pos) (Nat.beq ax 21)) (ssplit26 ih pos) (Nat.beq ax 20)) (ssplit25 ih pos) (Nat.beq ax 19)) (ssplit24 ih pos) (Nat.beq ax 18)) (ssplit17 ih pos) (Nat.beq ax 17)) (ssplit16 ih pos) (Nat.beq ax 16)) (ssplit15 ih pos) (Nat.beq ax 15)) (ssplit14 ih pos) (Nat.beq ax 14)) (ssplit13 ih pos) (Nat.beq ax 13)) (ssplit07 ih pos) (Nat.beq ax 12)) (ssplit06 ih pos) (Nat.beq ax 11)) (ssplit05 ih pos) (Nat.beq ax 10)) (ssplit04 ih pos) (Nat.beq ax 9)) (ssplit03 ih pos) (Nat.beq ax 8)) (ssplit02 ih pos) (Nat.beq ax 7)) (gsplit6 ih pos) (Nat.beq ax 6)) (gsplit5 ih pos) (Nat.beq ax 5)) (gsplit4 ih pos) (Nat.beq ax 4)) (gsplit3 ih pos) (Nat.beq ax 3)) (gsplit2 ih pos) (Nat.beq ax 2)) (gsplit1 ih pos) (Nat.beq ax 1)) (gsplit0 ih pos) (Nat.beq ax 0)

theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (pos ax : ℕ) : CovK (splitAx ih pos ax) :=
  brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => zK_ok) (fun _ => ssplit57_ok hih pos)) (fun _ => ssplit47_ok hih pos)) (fun _ => ssplit46_ok hih pos)) (fun _ => ssplit37_ok hih pos)) (fun _ => ssplit36_ok hih pos)) (fun _ => ssplit35_ok hih pos)) (fun _ => ssplit27_ok hih pos)) (fun _ => ssplit26_ok hih pos)) (fun _ => ssplit25_ok hih pos)) (fun _ => ssplit24_ok hih pos)) (fun _ => ssplit17_ok hih pos)) (fun _ => ssplit16_ok hih pos)) (fun _ => ssplit15_ok hih pos)) (fun _ => ssplit14_ok hih pos)) (fun _ => ssplit13_ok hih pos)) (fun _ => ssplit07_ok hih pos)) (fun _ => ssplit06_ok hih pos)) (fun _ => ssplit05_ok hih pos)) (fun _ => ssplit04_ok hih pos)) (fun _ => ssplit03_ok hih pos)) (fun _ => ssplit02_ok hih pos)) (fun _ => gsplit6_ok hih pos)) (fun _ => gsplit5_ok hih pos)) (fun _ => gsplit4_ok hih pos)) (fun _ => gsplit3_ok hih pos)) (fun _ => gsplit2_ok hih pos)) (fun _ => gsplit1_ok hih pos)) (fun _ => gsplit0_ok hih pos)

-- (5) the root: the box sums written into the pair bounds (`matC`), once, which closes the root box (TZ.md §5)

def tm (k : ST) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah : ℕ) : ℕ :=
  forceR (nmax r (Nat.add a c)) fun r' => forceR (nmin s (Nat.add b d)) fun s' =>
  forceR (nmax t (Nat.add (Nat.add a c) e)) fun t' => forceR (nmin u (Nat.add (Nat.add b d) f)) fun u' =>
  forceR (nmax v (Nat.add (Nat.add (Nat.add a c) e) g)) fun v' => forceR (nmin w (Nat.add (Nat.add (Nat.add b d) f) h)) fun w' =>
  forceR (nmax x (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i)) fun x' => forceR (nmin y (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j)) fun y' =>
  forceR (nmax z (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l)) fun z' => forceR (nmin A (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m)) fun A' =>
  forceR (nmax B (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l) n)) fun B' => forceR (nmin C (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m) o)) fun C' =>
  forceR (nmax D (Nat.add c e)) fun D' => forceR (nmin E (Nat.add d f)) fun E' =>
  forceR (nmax F (Nat.add (Nat.add c e) g)) fun F' => forceR (nmin G (Nat.add (Nat.add d f) h)) fun G' =>
  forceR (nmax H (Nat.add (Nat.add (Nat.add c e) g) i)) fun H' => forceR (nmin I (Nat.add (Nat.add (Nat.add d f) h) j)) fun I' =>
  forceR (nmax J (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l)) fun J' => forceR (nmin K (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m)) fun K' =>
  forceR (nmax L (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l) n)) fun L' => forceR (nmin M (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m) o)) fun M' =>
  forceR (nmax N (Nat.add e g)) fun N' => forceR (nmin O (Nat.add f h)) fun O' =>
  forceR (nmax P (Nat.add (Nat.add e g) i)) fun P' => forceR (nmin Q (Nat.add (Nat.add f h) j)) fun Q' =>
  forceR (nmax R (Nat.add (Nat.add (Nat.add e g) i) l)) fun R' => forceR (nmin S (Nat.add (Nat.add (Nat.add f h) j) m)) fun S' =>
  forceR (nmax T (Nat.add (Nat.add (Nat.add (Nat.add e g) i) l) n)) fun T' => forceR (nmin U (Nat.add (Nat.add (Nat.add (Nat.add f h) j) m) o)) fun U' =>
  forceR (nmax V (Nat.add g i)) fun V' => forceR (nmin W (Nat.add h j)) fun W' =>
  forceR (nmax X (Nat.add (Nat.add g i) l)) fun X' => forceR (nmin Y (Nat.add (Nat.add h j) m)) fun Y' =>
  forceR (nmax Z (Nat.add (Nat.add (Nat.add g i) l) n)) fun Z' => forceR (nmin aa (Nat.add (Nat.add (Nat.add h j) m) o)) fun aa' =>
  forceR (nmax ab (Nat.add i l)) fun ab' => forceR (nmin ac (Nat.add j m)) fun ac' =>
  forceR (nmax ad (Nat.add (Nat.add i l) n)) fun ad' => forceR (nmin ae (Nat.add (Nat.add j m) o)) fun ae' =>
  forceR (nmax af (Nat.add l n)) fun af' => forceR (nmin ag (Nat.add m o)) fun ag' =>
  k a b c d e f g h i j l m n o r' s' t' u' v' w' x' y' z' A' B' C' D' E' F' G' H' I' J' K' L' M' N' O' P' Q' R' S' T' U' V' W' X' Y' Z' aa' ab' ac' ad' ae' af' ag' ah

theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2

-- (3) multipliers (HUFF.md §5.2): entries `[1][c code][side][Yq: qb bits]`, closed by `[0]`
structure YA where
  (o P0 P1 P2 P3 P4 P5 P6 S0 S1 S2 S3 S4 S5 S6 Cp Cm : ℕ)

def MulOK (s : St) (y : YA) : Prop :=
  MulOKg 7 PR (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6] y.Cp y.Cm

def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) ⟨(Nat.add o 1), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.Cp, y.Cm⟩
    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) 31) fun c => forceT (Nat.add o 6) fun o1 =>
     Bool.rec (motive := fun _ => YA) ⟨(Nat.add o1 (Nat.add qb 1)), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.Cp, y.Cm⟩
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih ⟨(Nat.add o1 (Nat.add qb 1)), (Nat.add y.P0 (Nat.mul Ylo (ind (inr 0 i j)))), (Nat.add y.P1 (Nat.mul Ylo (ind (inr 1 i j)))), (Nat.add y.P2 (Nat.mul Ylo (ind (inr 2 i j)))), (Nat.add y.P3 (Nat.mul Ylo (ind (inr 3 i j)))), (Nat.add y.P4 (Nat.mul Ylo (ind (inr 4 i j)))), (Nat.add y.P5 (Nat.mul Ylo (ind (inr 5 i j)))), (Nat.add y.P6 (Nat.mul Ylo (ind (inr 6 i j)))), (Nat.add y.S0 (Nat.mul Yhi (ind (inr 0 i j)))), (Nat.add y.S1 (Nat.mul Yhi (ind (inr 1 i j)))), (Nat.add y.S2 (Nat.mul Yhi (ind (inr 2 i j)))), (Nat.add y.S3 (Nat.mul Yhi (ind (inr 3 i j)))), (Nat.add y.S4 (Nat.mul Yhi (ind (inr 4 i j)))), (Nat.add y.S5 (Nat.mul Yhi (ind (inr 5 i j)))), (Nat.add y.S6 (Nat.mul Yhi (ind (inr 6 i j)))), (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))), (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0))))⟩)
      (Nat.blt c 21))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)

def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel

theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := fun _ _ => by simp

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
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k56 m56 p56 r56 k67 m67 p67 r67 : ℕ) (P0 P1 P2 P3 P4 P5 P6 S0 S1 S2 S3 S4 S5 S6 Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mcK f false s.l0 k01 m01 p01 r01))) (Nat.mul 19565904 (mcK f false (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 20317441 (mcK f false (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 45030671 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 100000000 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 200000000 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 29997996 (mcK f false s.l1 k12 m12 p12 r12))) (Nat.mul 30621878 (mcK f false (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 47766489 (mcK f false (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 79682558 (mcK f false (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 109938656 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 100000000 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 37356140 (mcK f false s.l2 k23 m23 p23 r23))) (Nat.mul 69378121 (mcK f false (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 65335210 (mcK f false (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 79682558 (mcK f false (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 45030671 (mcK f false (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 38030065 (mcK f false s.l3 k34 m34 p34 r34))) (Nat.mul 69378121 (mcK f false (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 47766489 (mcK f false (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 20317441 (mcK f false (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 37356140 (mcK f false s.l4 k45 m45 p45 r45))) (Nat.mul 30621878 (mcK f false (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 19565904 (mcK f false (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 29997996 (mcK f false s.l5 k56 m56 p56 r56))) (Nat.mul 13630830 (mcK f false s.l6 k67 m67 p67 r67))) Cp) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub s.u0 s.l0) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mwT k01 m01))) (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 200000000 (mwT k07 m07)))) P0) (Nat.add (Nat.add (Nat.mul 1024000000000 28898) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mslK f k01 m01 p01 r01))) (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 200000000 (mslK f k07 m07 p07 r07)))) S0)))) (Nat.mul (Nat.sub s.u1 s.l1) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 200000000 (mwT k07 m07))) (Nat.mul 29997996 (mwT k12 m12))) (Nat.mul 30621878 (mwT k13 m13))) (Nat.mul 47766489 (mwT k14 m14))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 100000000 (mwT k17 m17)))) P1) (Nat.add (Nat.add (Nat.mul 1024000000000 57272) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 200000000 (mslK f k07 m07 p07 r07))) (Nat.mul 29997996 (mslK f k12 m12 p12 r12))) (Nat.mul 30621878 (mslK f k13 m13 p13 r13))) (Nat.mul 47766489 (mslK f k14 m14 p14 r14))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 100000000 (mslK f k17 m17 p17 r17)))) S1)))) (Nat.mul (Nat.sub s.u2 s.l2) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mwT k03 m03))) (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 200000000 (mwT k07 m07))) (Nat.mul 30621878 (mwT k13 m13))) (Nat.mul 47766489 (mwT k14 m14))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 100000000 (mwT k17 m17))) (Nat.mul 37356140 (mwT k23 m23))) (Nat.mul 69378121 (mwT k24 m24))) (Nat.mul 65335210 (mwT k25 m25))) (Nat.mul 79682558 (mwT k26 m26))) (Nat.mul 45030671 (mwT k27 m27)))) P2) (Nat.add (Nat.add (Nat.mul 1024000000000 75526) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 19565904 (mslK f k03 m03 p03 r03))) (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 200000000 (mslK f k07 m07 p07 r07))) (Nat.mul 30621878 (mslK f k13 m13 p13 r13))) (Nat.mul 47766489 (mslK f k14 m14 p14 r14))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 100000000 (mslK f k17 m17 p17 r17))) (Nat.mul 37356140 (mslK f k23 m23 p23 r23))) (Nat.mul 69378121 (mslK f k24 m24 p24 r24))) (Nat.mul 65335210 (mslK f k25 m25 p25 r25))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26))) (Nat.mul 45030671 (mslK f k27 m27 p27 r27)))) S2)))) (Nat.mul (Nat.sub s.u3 s.l3) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 20317441 (mwT k04 m04))) (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 200000000 (mwT k07 m07))) (Nat.mul 47766489 (mwT k14 m14))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 100000000 (mwT k17 m17))) (Nat.mul 69378121 (mwT k24 m24))) (Nat.mul 65335210 (mwT k25 m25))) (Nat.mul 79682558 (mwT k26 m26))) (Nat.mul 45030671 (mwT k27 m27))) (Nat.mul 38030065 (mwT k34 m34))) (Nat.mul 69378121 (mwT k35 m35))) (Nat.mul 47766489 (mwT k36 m36))) (Nat.mul 20317441 (mwT k37 m37)))) P3) (Nat.add (Nat.add (Nat.mul 1024000000000 80958) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 20317441 (mslK f k04 m04 p04 r04))) (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 200000000 (mslK f k07 m07 p07 r07))) (Nat.mul 47766489 (mslK f k14 m14 p14 r14))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 100000000 (mslK f k17 m17 p17 r17))) (Nat.mul 69378121 (mslK f k24 m24 p24 r24))) (Nat.mul 65335210 (mslK f k25 m25 p25 r25))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26))) (Nat.mul 45030671 (mslK f k27 m27 p27 r27))) (Nat.mul 38030065 (mslK f k34 m34 p34 r34))) (Nat.mul 69378121 (mslK f k35 m35 p35 r35))) (Nat.mul 47766489 (mslK f k36 m36 p36 r36))) (Nat.mul 20317441 (mslK f k37 m37 p37 r37)))) S3)))) (Nat.mul (Nat.sub s.u4 s.l4) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 45030671 (mwT k05 m05))) (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 200000000 (mwT k07 m07))) (Nat.mul 79682558 (mwT k15 m15))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 100000000 (mwT k17 m17))) (Nat.mul 65335210 (mwT k25 m25))) (Nat.mul 79682558 (mwT k26 m26))) (Nat.mul 45030671 (mwT k27 m27))) (Nat.mul 69378121 (mwT k35 m35))) (Nat.mul 47766489 (mwT k36 m36))) (Nat.mul 20317441 (mwT k37 m37))) (Nat.mul 37356140 (mwT k45 m45))) (Nat.mul 30621878 (mwT k46 m46))) (Nat.mul 19565904 (mwT k47 m47)))) P4) (Nat.add (Nat.add (Nat.mul 1024000000000 75526) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 45030671 (mslK f k05 m05 p05 r05))) (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 200000000 (mslK f k07 m07 p07 r07))) (Nat.mul 79682558 (mslK f k15 m15 p15 r15))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 100000000 (mslK f k17 m17 p17 r17))) (Nat.mul 65335210 (mslK f k25 m25 p25 r25))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26))) (Nat.mul 45030671 (mslK f k27 m27 p27 r27))) (Nat.mul 69378121 (mslK f k35 m35 p35 r35))) (Nat.mul 47766489 (mslK f k36 m36 p36 r36))) (Nat.mul 20317441 (mslK f k37 m37 p37 r37))) (Nat.mul 37356140 (mslK f k45 m45 p45 r45))) (Nat.mul 30621878 (mslK f k46 m46 p46 r46))) (Nat.mul 19565904 (mslK f k47 m47 p47 r47)))) S4)))) (Nat.mul (Nat.sub s.u5 s.l5) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000 (mwT k06 m06))) (Nat.mul 200000000 (mwT k07 m07))) (Nat.mul 109938656 (mwT k16 m16))) (Nat.mul 100000000 (mwT k17 m17))) (Nat.mul 79682558 (mwT k26 m26))) (Nat.mul 45030671 (mwT k27 m27))) (Nat.mul 47766489 (mwT k36 m36))) (Nat.mul 20317441 (mwT k37 m37))) (Nat.mul 30621878 (mwT k46 m46))) (Nat.mul 19565904 (mwT k47 m47))) (Nat.mul 29997996 (mwT k56 m56)))) P5) (Nat.add (Nat.add (Nat.mul 1024000000000 57272) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000 (mslK f k06 m06 p06 r06))) (Nat.mul 200000000 (mslK f k07 m07 p07 r07))) (Nat.mul 109938656 (mslK f k16 m16 p16 r16))) (Nat.mul 100000000 (mslK f k17 m17 p17 r17))) (Nat.mul 79682558 (mslK f k26 m26 p26 r26))) (Nat.mul 45030671 (mslK f k27 m27 p27 r27))) (Nat.mul 47766489 (mslK f k36 m36 p36 r36))) (Nat.mul 20317441 (mslK f k37 m37 p37 r37))) (Nat.mul 30621878 (mslK f k46 m46 p46 r46))) (Nat.mul 19565904 (mslK f k47 m47 p47 r47))) (Nat.mul 29997996 (mslK f k56 m56 p56 r56)))) S5)))) (Nat.mul (Nat.sub s.u6 s.l6) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000 (mwT k07 m07))) (Nat.mul 100000000 (mwT k17 m17))) (Nat.mul 45030671 (mwT k27 m27))) (Nat.mul 20317441 (mwT k37 m37))) (Nat.mul 19565904 (mwT k47 m47))) (Nat.mul 13630830 (mwT k67 m67)))) P6) (Nat.add (Nat.add (Nat.mul 1024000000000 28898) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000 (mslK f k07 m07 p07 r07))) (Nat.mul 100000000 (mslK f k17 m17 p17 r17))) (Nat.mul 45030671 (mslK f k27 m27 p27 r27))) (Nat.mul 20317441 (mslK f k37 m37 p37 r37))) (Nat.mul 19565904 (mslK f k47 m47 p47 r47))) (Nat.mul 13630830 (mslK f k67 m67 p67 r67)))) S6))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 28898 s.l0)) (Nat.mul 57272 s.l1)) (Nat.mul 75526 s.l2)) (Nat.mul 80958 s.l3)) (Nat.mul 75526 s.l4)) (Nat.mul 57272 s.l5)) (Nat.mul 28898 s.l6))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mvK top bk f s.l0 (uc s.l0 s.u0) k01 m01 p01 r01))) (Nat.mul 19565904 (mvK top bk f (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (uc (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2))) k03 m03 p03 r03))) (Nat.mul 20317441 (mvK top bk f (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (uc (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3))) k04 m04 p04 r04))) (Nat.mul 45030671 (mvK top bk f (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (uc (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4))) k05 m05 p05 r05))) (Nat.mul 100000000 (mvK top bk f (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5))) k06 m06 p06 r06))) (Nat.mul 200000000 (mvK top bk f (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6))) k07 m07 p07 r07))) (Nat.mul 29997996 (mvK top bk f s.l1 (uc s.l1 s.u1) k12 m12 p12 r12))) (Nat.mul 30621878 (mvK top bk f (nmax s.A13 (Nat.add s.l1 s.l2)) (uc (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2))) k13 m13 p13 r13))) (Nat.mul 47766489 (mvK top bk f (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (uc (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3))) k14 m14 p14 r14))) (Nat.mul 79682558 (mvK top bk f (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (uc (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4))) k15 m15 p15 r15))) (Nat.mul 109938656 (mvK top bk f (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5))) k16 m16 p16 r16))) (Nat.mul 100000000 (mvK top bk f (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6))) k17 m17 p17 r17))) (Nat.mul 37356140 (mvK top bk f s.l2 (uc s.l2 s.u2) k23 m23 p23 r23))) (Nat.mul 69378121 (mvK top bk f (nmax s.A24 (Nat.add s.l2 s.l3)) (uc (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3))) k24 m24 p24 r24))) (Nat.mul 65335210 (mvK top bk f (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (uc (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4))) k25 m25 p25 r25))) (Nat.mul 79682558 (mvK top bk f (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (uc (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5))) k26 m26 p26 r26))) (Nat.mul 45030671 (mvK top bk f (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6))) k27 m27 p27 r27))) (Nat.mul 38030065 (mvK top bk f s.l3 (uc s.l3 s.u3) k34 m34 p34 r34))) (Nat.mul 69378121 (mvK top bk f (nmax s.A35 (Nat.add s.l3 s.l4)) (uc (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4))) k35 m35 p35 r35))) (Nat.mul 47766489 (mvK top bk f (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (uc (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5))) k36 m36 p36 r36))) (Nat.mul 20317441 (mvK top bk f (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (uc (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6))) k37 m37 p37 r37))) (Nat.mul 37356140 (mvK top bk f s.l4 (uc s.l4 s.u4) k45 m45 p45 r45))) (Nat.mul 30621878 (mvK top bk f (nmax s.A46 (Nat.add s.l4 s.l5)) (uc (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5))) k46 m46 p46 r46))) (Nat.mul 19565904 (mvK top bk f (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (uc (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6))) k47 m47 p47 r47))) (Nat.mul 29997996 (mvK top bk f s.l5 (uc s.l5 s.u5) k56 m56 p56 r56))) (Nat.mul 13630830 (mvK top bk f s.l6 (uc s.l6 s.u6) k67 m67 p67 r67))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 13630830 (mcK f true s.l0 k01 m01 p01 r01))) (Nat.mul 19565904 (mcK f true (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 20317441 (mcK f true (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 45030671 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 100000000 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 200000000 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 29997996 (mcK f true s.l1 k12 m12 p12 r12))) (Nat.mul 30621878 (mcK f true (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 47766489 (mcK f true (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 79682558 (mcK f true (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 109938656 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 100000000 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 37356140 (mcK f true s.l2 k23 m23 p23 r23))) (Nat.mul 69378121 (mcK f true (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 65335210 (mcK f true (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 79682558 (mcK f true (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 45030671 (mcK f true (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 38030065 (mcK f true s.l3 k34 m34 p34 r34))) (Nat.mul 69378121 (mcK f true (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 47766489 (mcK f true (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 20317441 (mcK f true (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 37356140 (mcK f true s.l4 k45 m45 p45 r45))) (Nat.mul 30621878 (mcK f true (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 19565904 (mcK f true (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 29997996 (mcK f true s.l5 k56 m56 p56 r56))) (Nat.mul 13630830 (mcK f true s.l6 k67 m67 p67 r67))) Cm)))) (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 s.l6 s.u6 k67 m67 p67 r67) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 s.l5 s.u5 k56 m56 p56 r56) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) k47 m47 p47 r47) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5)) k46 m46 p46 r46) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 s.l4 s.u4 k45 m45 p45 r45) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) k37 m37 p37 r37) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) k36 m36 p36 r36) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4)) k35 m35 p35 r35) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 s.l3 s.u3 k34 m34 p34 r34) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) k27 m27 p27 r27) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) k26 m26 p26 r26) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) k25 m25 p25 r25) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3)) k24 m24 p24 r24) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 s.l2 s.u2 k23 m23 p23 r23) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) k17 m17 p17 r17) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) k16 m16 p16 r16) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) k15 m15 p15 r15) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) k14 m14 p14 r14) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2)) k13 m13 p13 r13) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 s.l1 s.u1 k12 m12 p12 r12) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) k07 m07 p07 r07) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) k06 m06 p06 r06) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) k05 m05 p05 r05) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) k04 m04 p04 r04) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) k03 m03 p03 r03) (Bool.rec (motive := fun _ => Bool) false (mokTZ R top bk tD bD f 8 s.l0 s.u0 k01 m01 p01 r01) (true))))))))))))))))))))))))))) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l6 s.u6) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l5 s.u5) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l4 s.u4) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l3 s.u3) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l2 s.u2) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l1 s.u1) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l0 s.u0) (true)))))))))

theorem mcheckP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k56 m56 p56 r56 k67 m67 p67 r67 : ℕ) (P0 P1 P2 P3 P4 P5 P6 S0 S1 S2 S3 S4 S5 S6 Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k56 m56 p56 r56 k67 m67 p67 r67 P0 P1 P2 P3 P4 P5 P6 S0 S1 S2 S3 S4 S5 S6 Cp Cm = true) :
    mcheckGZ top bk tD bD f R 8 7 BS TS cN (toCl s) [(k01, m01, p01, r01), (k03, m03, p03, r03), (k04, m04, p04, r04), (k05, m05, p05, r05), (k06, m06, p06, r06), (k07, m07, p07, r07), (k12, m12, p12, r12), (k13, m13, p13, r13), (k14, m14, p14, r14), (k15, m15, p15, r15), (k16, m16, p16, r16), (k17, m17, p17, r17), (k23, m23, p23, r23), (k24, m24, p24, r24), (k25, m25, p25, r25), (k26, m26, p26, r26), (k27, m27, p27, r27), (k34, m34, p34, r34), (k35, m35, p35, r35), (k36, m36, p36, r36), (k37, m37, p37, r37), (k45, m45, p45, r45), (k46, m46, p46, r46), (k47, m47, p47, r47), (k56, m56, p56, r56), (k67, m67, p67, r67)]
      [P0, P1, P2, P3, P4, P5, P6] [S0, S1, S2, S3, S4, S5, S6] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq] at h; exact h

/-- the polytope minorant leaf (HUFF.md §5): the payload length when the check passes, else `0` -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  forceR (nmax s.A02 (Nat.add s.l0 s.l1)) fun L02 => forceR (nmin s.B02 (Nat.add s.u0 s.u1)) fun U02 =>
  forceR (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) fun L03 => forceR (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) fun U03 =>
  forceR (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) fun L04 => forceR (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) fun U04 =>
  forceR (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) fun L05 => forceR (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) fun U05 =>
  forceR (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) fun L06 => forceR (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) fun U06 =>
  forceR (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) fun L07 => forceR (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) fun U07 =>
  forceR (nmax s.A13 (Nat.add s.l1 s.l2)) fun L13 => forceR (nmin s.B13 (Nat.add s.u1 s.u2)) fun U13 =>
  forceR (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) fun L14 => forceR (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) fun U14 =>
  forceR (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) fun L15 => forceR (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) fun U15 =>
  forceR (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) fun L16 => forceR (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) fun U16 =>
  forceR (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) fun L17 => forceR (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) fun U17 =>
  forceR (nmax s.A24 (Nat.add s.l2 s.l3)) fun L24 => forceR (nmin s.B24 (Nat.add s.u2 s.u3)) fun U24 =>
  forceR (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) fun L25 => forceR (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) fun U25 =>
  forceR (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) fun L26 => forceR (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) fun U26 =>
  forceR (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) fun L27 => forceR (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) fun U27 =>
  forceR (nmax s.A35 (Nat.add s.l3 s.l4)) fun L35 => forceR (nmin s.B35 (Nat.add s.u3 s.u4)) fun U35 =>
  forceR (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) fun L36 => forceR (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) fun U36 =>
  forceR (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) fun L37 => forceR (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) fun U37 =>
  forceR (nmax s.A46 (Nat.add s.l4 s.l5)) fun L46 => forceR (nmin s.B46 (Nat.add s.u4 s.u5)) fun U46 =>
  forceR (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) fun L47 => forceR (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) fun U47 =>
  forceR (nmax s.A57 (Nat.add s.l5 s.l6)) fun L57 => forceR (nmin s.B57 (Nat.add s.u5 s.u6)) fun U57 =>
  forceR 0 fun o0 =>
  dec4F 8 w o0 s.l0 s.u0 fun k01 m01 p01 r01 o1 =>
  dec4F 8 w o1 L03 U03 fun k03 m03 p03 r03 o2 =>
  dec4F 8 w o2 L04 U04 fun k04 m04 p04 r04 o3 =>
  dec4F 8 w o3 L05 U05 fun k05 m05 p05 r05 o4 =>
  dec4F 8 w o4 L06 U06 fun k06 m06 p06 r06 o5 =>
  dec4F 8 w o5 L07 U07 fun k07 m07 p07 r07 o6 =>
  dec4F 8 w o6 s.l1 s.u1 fun k12 m12 p12 r12 o7 =>
  dec4F 8 w o7 L13 U13 fun k13 m13 p13 r13 o8 =>
  dec4F 8 w o8 L14 U14 fun k14 m14 p14 r14 o9 =>
  dec4F 8 w o9 L15 U15 fun k15 m15 p15 r15 o10 =>
  dec4F 8 w o10 L16 U16 fun k16 m16 p16 r16 o11 =>
  dec4F 8 w o11 L17 U17 fun k17 m17 p17 r17 o12 =>
  dec4F 8 w o12 s.l2 s.u2 fun k23 m23 p23 r23 o13 =>
  dec4F 8 w o13 L24 U24 fun k24 m24 p24 r24 o14 =>
  dec4F 8 w o14 L25 U25 fun k25 m25 p25 r25 o15 =>
  dec4F 8 w o15 L26 U26 fun k26 m26 p26 r26 o16 =>
  dec4F 8 w o16 L27 U27 fun k27 m27 p27 r27 o17 =>
  dec4F 8 w o17 s.l3 s.u3 fun k34 m34 p34 r34 o18 =>
  dec4F 8 w o18 L35 U35 fun k35 m35 p35 r35 o19 =>
  dec4F 8 w o19 L36 U36 fun k36 m36 p36 r36 o20 =>
  dec4F 8 w o20 L37 U37 fun k37 m37 p37 r37 o21 =>
  dec4F 8 w o21 s.l4 s.u4 fun k45 m45 p45 r45 o22 =>
  dec4F 8 w o22 L46 U46 fun k46 m46 p46 r46 o23 =>
  dec4F 8 w o23 L47 U47 fun k47 m47 p47 r47 o24 =>
  dec4F 8 w o24 s.l5 s.u5 fun k56 m56 p56 r56 o25 =>
  dec4F 8 w o25 s.l6 s.u6 fun k67 m67 p67 r67 o26 =>
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k56 m56 p56 r56 k67 m67 p67 r67 y.P0 y.P1 y.P2 y.P3 y.P4 y.P5 y.P6 y.S0 y.S1 y.S2 y.S3 y.S4 y.S5 y.S6 y.Cp y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨o26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  unfold mleafP at h
  simp only [dec4F, forceR_eq] at h
  exact mcheckGZ_sound (f := pb) hlb hD hpt hR (by decide : 0 < 8) hPR hTS (ydec_ok s 12 w 42 _ (MulOK_zero s _)) (mcheckP_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h))

/-- (kind 8) the Farkas leaf (HUFF.md §6): the multiplier list only (`Yq` in 12 bits), accepted when the multiplier form
is negative on the whole box -/
def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6] 7)) y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)

/-- a leaf (bit 0 clear): the reflected half-space (`u6 < l0`, no further bits), else bit 1 the kind (minorant leaf, or
Farkas leaf) with its payload from bit 2 -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A24 B24 A25 B25 A26 B26 A27 B27 A35 B35 A36 B36 A37 B37 A46 B46 A47 B47 A57 B57 M => Bool.rec (motive := fun _ => ℕ)
    (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A24, B24, A25, B25, A26, B26, A27, B27, A35, B35, A36, B36, A37, B37, A46, B46, A47, B47, A57, B57, M⟩)
        (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A24, B24, A25, B25, A26, B26, A27, B27, A35, B35, A36, B36, A37, B37, A46, B46, A47, B47, A57, B57, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1) (Nat.blt u6 l0)

theorem fleaf_ok (w : ℕ) (s : St) (h : fleaf w s ≠ 0) : Covered (toCl s) :=
  farkas_cov (ydec_ok s 12 w 42 _ (MulOK_zero s 0)) (brec_ne h)

theorem leafStep_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (pos w : ℕ) :
    CovK (leafStep top bk tD bD pb R pos w) := by
  intro s h
  have h' : Bool.rec (motive := fun _ => ℕ) (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)
      (fleaf (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) (Nat.add pos 1) (Nat.blt s.u6 s.l0) ≠ 0 := h
  cases hs : Nat.blt s.u6 s.l0
  · rw [hs, forceR_eq] at h'
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h'; exact h' rfl
    · rw [hk] at h'; exact fleaf_ok _ s fun h0 => by rw [h0] at h'; exact h' rfl
  · intro g hg
    right
    have h1 : g 6 ≤ (s.u6 : ℝ) / SC := (hg.1 6 (by norm_num)).2
    have h2 : (s.l0 : ℝ) / SC ≤ g 0 := (hg.1 0 (by norm_num)).1
    have : (s.u6 : ℝ) / SC < (s.l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast Nat.blt_eq.mp hs) SC_pos
    show g 6 < g 0
    linarith

/-- a node: bit `pos` selects split (`[1]`, then the axis codeword; the children from the bit after it) or leaf (`[0]`) -/
def node (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos (Nat.shiftRight bits pos))
    (splitAx ih (Nat.add pos 6) (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 31))
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
      (splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _)

theorem walk_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) :=
  fun fuel pos => tm_ok (walkC_ok hlb hD hpt hR bits fuel pos)

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits fuel e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)

/-- (chunked walks) field-wise equality of two states -/
def stEq (a b : St) : Bool := Nat.beq a.l0 b.l0 && Nat.beq a.u0 b.u0 && Nat.beq a.l1 b.l1 && Nat.beq a.u1 b.u1 && Nat.beq a.l2 b.l2 && Nat.beq a.u2 b.u2 && Nat.beq a.l3 b.l3 && Nat.beq a.u3 b.u3 && Nat.beq a.l4 b.l4 && Nat.beq a.u4 b.u4 && Nat.beq a.l5 b.l5 && Nat.beq a.u5 b.u5 && Nat.beq a.l6 b.l6 && Nat.beq a.u6 b.u6 && Nat.beq a.A02 b.A02 && Nat.beq a.B02 b.B02 && Nat.beq a.A03 b.A03 && Nat.beq a.B03 b.B03 && Nat.beq a.A04 b.A04 && Nat.beq a.B04 b.B04 && Nat.beq a.A05 b.A05 && Nat.beq a.B05 b.B05 && Nat.beq a.A06 b.A06 && Nat.beq a.B06 b.B06 && Nat.beq a.A07 b.A07 && Nat.beq a.B07 b.B07 && Nat.beq a.A13 b.A13 && Nat.beq a.B13 b.B13 && Nat.beq a.A14 b.A14 && Nat.beq a.B14 b.B14 && Nat.beq a.A15 b.A15 && Nat.beq a.B15 b.B15 && Nat.beq a.A16 b.A16 && Nat.beq a.B16 b.B16 && Nat.beq a.A17 b.A17 && Nat.beq a.B17 b.B17 && Nat.beq a.A24 b.A24 && Nat.beq a.B24 b.B24 && Nat.beq a.A25 b.A25 && Nat.beq a.B25 b.B25 && Nat.beq a.A26 b.A26 && Nat.beq a.B26 b.B26 && Nat.beq a.A27 b.A27 && Nat.beq a.B27 b.B27 && Nat.beq a.A35 b.A35 && Nat.beq a.B35 b.B35 && Nat.beq a.A36 b.A36 && Nat.beq a.B36 b.B36 && Nat.beq a.A37 b.A37 && Nat.beq a.B37 b.B37 && Nat.beq a.A46 b.A46 && Nat.beq a.B46 b.B46 && Nat.beq a.A47 b.A47 && Nat.beq a.B47 b.B47 && Nat.beq a.A57 b.A57 && Nat.beq a.B57 b.B57 && Nat.beq a.M b.M
theorem St_eq {a b : St} (h : stEq a b = true) : a = b := by
  cases a; cases b
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩, h36⟩, h37⟩, h38⟩, h39⟩, h40⟩, h41⟩, h42⟩, h43⟩, h44⟩, h45⟩, h46⟩, h47⟩, h48⟩, h49⟩, h50⟩, h51⟩, h52⟩, h53⟩, h54⟩, h55⟩, h56⟩ := h
  subst_vars; rfl
/-- the continuation that accepts exactly the state `t` -/
def kEq (t : St) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A24 B24 A25 B25 A26 B26 A27 B27 A35 B35 A36 B36 A37 B37 A46 B46 A47 B47 A57 B57 M => Bool.rec (motive := fun _ => ℕ) 0 1 (stEq ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A24, B24, A25, B25, A26, B26, A27, B27, A35, B35, A36, B36, A37, B37, A46, B46, A47, B47, A57, B57, M⟩ t)
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
theorem gsplit_to (r : ℕ) (hr : r < 7) {t sA sB : St}
    (eA : toCl sA = cupd 7 PR SL ⟨(toCl t).L, (toCl t).U.set r (qG (toCl t) r), (toCl t).A, (toCl t).B⟩ r (r + 1))
    (eB : toCl sB = cupd 7 PR SL ⟨(toCl t).L.set r (qG (toCl t) r), (toCl t).U, (toCl t).A, (toCl t).B⟩ (r + 1) r)
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_gmidC hSL hPR r rfl rfl hr (eA ▸ hA) (eB ▸ hB)
/-- a chunk boundary's split on pair `k` at the raw midpoint of its bounds, the children closed (`cupd`) -/
theorem ssplit_to (k : ℕ) (hk : k < 21) {t sA sB : St}
    (eA : toCl sA = cupd 7 PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A, (toCl t).B.set k (qR (toCl t) k)⟩ (pI PR k) (pJ PR k))
    (eB : toCl sB = cupd 7 PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A.set k (qR (toCl t) k), (toCl t).B⟩ (pJ PR k) (pI PR k))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_rmidC hSL hPR k rfl rfl hk (eA ▸ hA) (eB ▸ hB)
/-- a walk from any bit position -/
theorem covered_of_walkP {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (bits fuel pos e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel pos s (h ▸ he)

/-- the adjacent term of each gap (its index in `TS`) -/
def ADJ : List ℕ := [0, 6, 12, 17, 21, 24, 25]
theorem hADJ : ∀ r < 7, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide

/-- (root) the certificate on every point with nonnegative gaps, from the per-gap covers (`coverChk`) and the walks over
the root cells (`rootCl`: a bad segment per gap, pair bounds absent) -/
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < 7, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < 7, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 7, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : 7 * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < 7, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl 7 21 W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < 7, 0 ≤ g r) → Pg cN 7 BS TS g :=
  root_cover hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun

/-- the root: every pair bound absent (`A = 0`, `B = W ≥ Σ u`) -/
theorem covered_box (s : St) (W : ℕ) (hA : ∀ k < 21, (toCl s).A.getD k 0 = 0) (hB : ∀ k < 21, (toCl s).B.getD k 0 = W)
    (hW : sumR (toCl s).U 0 7 ≤ W) (h : Covered (toCl s)) (g : ℕ → ℝ) (hb : InBox 7 (toCl s) g) : Pg cN 7 BS TS g :=
  h g (incell_root hPR hA hB hW hb)


end AMW.Cert.PC8CK
