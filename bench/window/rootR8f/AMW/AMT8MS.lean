import AMW.AMT8Inst

set_option maxRecDepth 100000

noncomputable section

namespace AMW.Cert.AMT8MS

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.AMT8

/-- the accumulator of a minorant leaf -/
structure MA where
  (ok : Bool) (o A B p0 p1 p2 p3 p4 p5 p6 s0 s1 s2 s3 s4 s5 s6 : ℕ)

/-- evaluate a natural before continuing with an accumulator -/
def forceM (a : ℕ) (k : ℕ → MA) : MA := Nat.rec (motive := fun _ => MA) (k 0) (fun n _ => k (Nat.succ n)) a

def ta0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 16682481664 (lo32 (hi32 X))) fun sp =>
  forceM 33364963328000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 533839413248 (Nat.mul 1024 (lo32 X))) (Nat.mul 162914860 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 16291486 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, (Nat.add acc.s0 sw), acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩

def tb0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 16291486 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 32582972000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 162914860 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 16291486 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, (Nat.add acc.s0 sw), acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩

def tc0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 33364963328000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 162914860 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), (Nat.add acc.p0 sp), acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, (Nat.add acc.s0 sw), acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩

def st0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc0 top bk tD bD pb R w L U o acc) (tb0 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta0 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 546651559165952 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tb3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 200000000000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tc3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def st3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc3 top bk tD bD pb R w L U o acc) (tb3 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta3 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 3355443200000000 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 39942497280 (lo32 (hi32 X))) fun sp =>
  forceM 79884994560000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1278159912960 (Nat.mul 1024 (lo32 X))) (Nat.mul 390063450 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 39006345 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tb4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 39006345 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 78012690000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 390063450 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 39006345 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tc4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 79884994560000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 390063450 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def st4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc4 top bk tD bD pb R w L U o acc) (tb4 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta4 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 1308835750871040 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tb5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 200000000000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tc5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def st5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc5 top bk tD bD pb R w L U o acc) (tb5 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta5 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 3355443200000000 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 204800000000 (lo32 (hi32 X))) fun sp =>
  forceM 409600000000000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 6553600000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 2000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 200000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tb6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 200000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 400000000000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 6553600000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 2000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 200000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tc6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 200000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 409600000000000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 6553600000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 2000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 200000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), (Nat.add acc.p0 sp), (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), (Nat.add acc.s0 sw), (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def st6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc6 top bk tD bD pb R w L U o acc) (tb6 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta6 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 6710886400000000 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 32852407296 (lo32 (hi32 X))) fun sp =>
  forceM 65704814592000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1051277033472 (Nat.mul 1024 (lo32 X))) (Nat.mul 320824290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32082429 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩

def tb7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 32082429 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 64164858000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 320824290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32082429 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩

def tc7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 65704814592000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 320824290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, (Nat.add acc.p1 sp), acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩

def st7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc7 top bk tD bD pb R w L U o acc) (tb7 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta7 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 1076507682275328 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 3837002752 (lo32 (hi32 X))) fun sp =>
  forceM 7674005504000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 122784088064 (Nat.mul 1024 (lo32 X))) (Nat.mul 37470730 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 3747073 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), acc.s3, acc.s4, acc.s5, acc.s6⟩

def tb8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 3747073 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 7494146000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 37470730 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 3747073 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), acc.s3, acc.s4, acc.s5, acc.s6⟩

def tc8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 7674005504000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 37470730 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), acc.s3, acc.s4, acc.s5, acc.s6⟩

def st8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc8 top bk tD bD pb R w L U o acc) (tb8 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta8 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 125730906177536 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 61062890496 (lo32 (hi32 X))) fun sp =>
  forceM 122125780992000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1954012495872 (Nat.mul 1024 (lo32 X))) (Nat.mul 596317290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 59631729 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tb9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 59631729 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 119263458000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 596317290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 59631729 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tc9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 122125780992000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 596317290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def st9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc9 top bk tD bD pb R w L U o acc) (tb9 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta9 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 2000908795772928 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 124915005440 (lo32 (hi32 X))) fun sp =>
  forceM 249830010880000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 3997280174080 (Nat.mul 1024 (lo32 X))) (Nat.mul 1219873100 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 121987310 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tb11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 121987310 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 243974620000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 3997280174080 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 1219873100 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 121987310 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tc11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 121987310 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 249830010880000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 3997280174080 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1219873100 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 121987310 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def st11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc11 top bk tD bD pb R w L U o acc) (tb11 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta11 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 4093214898257920 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tb12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 200000000000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tc12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, (Nat.add acc.p1 sp), (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, (Nat.add acc.s1 sw), (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def st12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc12 top bk tD bD pb R w L U o acc) (tb12 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta12 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 3355443200000000 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 33509000192 (lo32 (hi32 X))) fun sp =>
  forceM 67018000384000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1072288006144 (Nat.mul 1024 (lo32 X))) (Nat.mul 327236330 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32723633 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), acc.s3, acc.s4, acc.s5, acc.s6⟩

def tb13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 32723633 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 65447266000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 327236330 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32723633 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), acc.s3, acc.s4, acc.s5, acc.s6⟩

def tc13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 67018000384000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 327236330 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, (Nat.add acc.p2 sp), acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), acc.s3, acc.s4, acc.s5, acc.s6⟩

def st13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc13 top bk tD bD pb R w L U o acc) (tb13 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta13 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 1098022918291456 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 98562997248 (lo32 (hi32 X))) fun sp =>
  forceM 197125994496000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 3154015911936 (Nat.mul 1024 (lo32 X))) (Nat.mul 962529270 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 96252927 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tb14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 96252927 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 192505854000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 962529270 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 96252927 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tc14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 197125994496000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 962529270 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def st14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc14 top bk tD bD pb R w L U o acc) (tb14 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta14 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 3229712293822464 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 82674219008 (lo32 (hi32 X))) fun sp =>
  forceM 165348438016000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 2645575008256 (Nat.mul 1024 (lo32 X))) (Nat.mul 807365420 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 80736542 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tb15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 80736542 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 161473084000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 2645575008256 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 807365420 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 80736542 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tc15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 80736542 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 165348438016000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 2645575008256 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 807365420 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 80736542 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def st15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc15 top bk tD bD pb R w L U o acc) (tb15 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta15 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 2709068808454144 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 39942497280 (lo32 (hi32 X))) fun sp =>
  forceM 79884994560000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1278159912960 (Nat.mul 1024 (lo32 X))) (Nat.mul 390063450 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 39006345 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tb17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 39006345 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 78012690000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 390063450 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 39006345 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tc17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 79884994560000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 390063450 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, (Nat.add acc.p2 sp), (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, acc.s1, (Nat.add acc.s2 sw), (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def st17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc17 top bk tD bD pb R w L U o acc) (tb17 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta17 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 1308835750871040 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 38712221696 (lo32 (hi32 X))) fun sp =>
  forceM 77424443392000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1238791094272 (Nat.mul 1024 (lo32 X))) (Nat.mul 378049040 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 37804904 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tb18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 37804904 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 75609808000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1238791094272 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 378049040 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 37804904 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def tc18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 37804904 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 77424443392000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1238791094272 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 378049040 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 37804904 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), acc.s4, acc.s5, acc.s6⟩

def st18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc18 top bk tD bD pb R w L U o acc) (tb18 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta18 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 1268522080534528 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 98562997248 (lo32 (hi32 X))) fun sp =>
  forceM 197125994496000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 3154015911936 (Nat.mul 1024 (lo32 X))) (Nat.mul 962529270 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 96252927 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tb19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 96252927 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 192505854000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 962529270 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 96252927 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tc19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 197125994496000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 962529270 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def st19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc19 top bk tD bD pb R w L U o acc) (tb19 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta19 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 3229712293822464 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 61062890496 (lo32 (hi32 X))) fun sp =>
  forceM 122125780992000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1954012495872 (Nat.mul 1024 (lo32 X))) (Nat.mul 596317290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 59631729 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tb20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 59631729 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 119263458000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 596317290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 59631729 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tc20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 122125780992000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 596317290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def st20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc20 top bk tD bD pb R w L U o acc) (tb20 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta20 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 2000908795772928 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tb21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 200000000000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def tc21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 204800000000000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, (Nat.add acc.p3 sp), (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), (Nat.add acc.p6 sp), acc.s0, acc.s1, acc.s2, (Nat.add acc.s3 sw), (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), (Nat.add acc.s6 sw)⟩

def st21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc21 top bk tD bD pb R w L U o acc) (tb21 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta21 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 3355443200000000 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 33509000192 (lo32 (hi32 X))) fun sp =>
  forceM 67018000384000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1072288006144 (Nat.mul 1024 (lo32 X))) (Nat.mul 327236330 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32723633 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tb22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 32723633 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 65447266000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 327236330 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32723633 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def tc22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 67018000384000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 327236330 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, acc.p3, (Nat.add acc.p4 sp), acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, (Nat.add acc.s4 sw), acc.s5, acc.s6⟩

def st22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc22 top bk tD bD pb R w L U o acc) (tb22 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta22 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 1098022918291456 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 3837002752 (lo32 (hi32 X))) fun sp =>
  forceM 7674005504000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 122784088064 (Nat.mul 1024 (lo32 X))) (Nat.mul 37470730 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 3747073 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tb23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 3747073 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 7494146000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 37470730 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 3747073 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def tc23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 7674005504000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 37470730 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, acc.p3, (Nat.add acc.p4 sp), (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, (Nat.add acc.s4 sw), (Nat.add acc.s5 sw), acc.s6⟩

def st23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc23 top bk tD bD pb R w L U o acc) (tb23 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta23 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 125730906177536 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 32852407296 (lo32 (hi32 X))) fun sp =>
  forceM 65704814592000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 1051277033472 (Nat.mul 1024 (lo32 X))) (Nat.mul 320824290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32082429 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, (Nat.add acc.s5 sw), acc.s6⟩

def tb25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 32082429 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 64164858000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 320824290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 32082429 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, (Nat.add acc.s5 sw), acc.s6⟩

def tc25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 65704814592000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 320824290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, (Nat.add acc.p5 sp), acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, (Nat.add acc.s5 sw), acc.s6⟩

def st25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc25 top bk tD bD pb R w L U o acc) (tb25 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta25 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 1076507682275328 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def ta27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 16682481664 (lo32 (hi32 X))) fun sp =>
  forceM 33364963328000000000 fun sw =>
  ⟨(acc.ok && (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))), (Nat.add acc.o 6), (Nat.add acc.A (Nat.add (Nat.mul 533839413248 (Nat.mul 1024 (lo32 X))) (Nat.mul 162914860 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 16291486 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, (Nat.add acc.p6 sp), acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, (Nat.add acc.s6 sw)⟩

def tb27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (pt3 pb p) fun X =>
  forceM (Nat.mul 16291486 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceM (Nat.mul 32582972000000000 m) fun sw =>
  ⟨(acc.ok && (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))), (Nat.add acc.o 16), (Nat.add acc.A (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 X)))) (Nat.mul 162914860 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L))))), (Nat.add acc.B (Nat.mul 16291486 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)))), acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, (Nat.add acc.p6 sp), acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, (Nat.add acc.s6 sw)⟩

def tc27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U o : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceM (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceM (pt3 pb p) fun X => forceM (pt3 pb r) fun Y =>
  forceM (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceM 33364963328000000000 fun sw =>
  ⟨(acc.ok && ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))), (Nat.add acc.o 20), (Nat.add acc.A (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 162914860 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L)))))), (Nat.add acc.B (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L))))), acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, (Nat.add acc.p6 sp), acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, (Nat.add acc.s6 sw)⟩

def st27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (Bool.rec (motive := fun _ => MA) (tc27 top bk tD bD pb R w L U o acc) (tb27 top bk tD bD pb R w L U o acc) (Nat.beq k 2))
      (ta27 top bk tD bD pb R w L U o acc) (Nat.beq k 1))
    ⟨acc.ok, (Nat.add acc.o 2), (Nat.add acc.A (Nat.mul 546651559165952 (lb top bk L U))), acc.B, acc.p0, acc.p1, acc.p2, acc.p3, acc.p4, acc.p5, acc.p6, acc.s0, acc.s1, acc.s2, acc.s3, acc.s4, acc.s5, acc.s6⟩ (Nat.beq k 0)

def mleafS (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  let acc := (st27 top bk tD bD pb R w l6 u6 (st25 top bk tD bD pb R w l5 u5 (st23 top bk tD bD pb R w (Nat.add l4 l5) (Nat.add u4 u5) (st22 top bk tD bD pb R w l4 u4 (st21 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (st20 top bk tD bD pb R w (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (st19 top bk tD bD pb R w (Nat.add l3 l4) (Nat.add u3 u4) (st18 top bk tD bD pb R w l3 u3 (st17 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (st15 top bk tD bD pb R w (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (st14 top bk tD bD pb R w (Nat.add l2 l3) (Nat.add u2 u3) (st13 top bk tD bD pb R w l2 u2 (st12 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (st11 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (st9 top bk tD bD pb R w (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (st8 top bk tD bD pb R w (Nat.add l1 l2) (Nat.add u1 u2) (st7 top bk tD bD pb R w l1 u1 (st6 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (st5 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (st4 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (st3 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (st0 top bk tD bD pb R w l0 u0 ⟨true, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩))))))))))))))))))))))
  Bool.rec (motive := fun _ => ℕ) 0 acc.o (acc.ok && Nat.ble (Nat.add 187231046205440000000000 (Nat.mul 10 (Nat.add acc.B (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub u0 l0) (Nat.sub acc.s0 (Nat.add 32596992000000000 acc.p0)))) (Nat.mul (Nat.sub u1 l1) (Nat.sub acc.s1 (Nat.add 60342272000000000 acc.p1)))) (Nat.mul (Nat.sub u2 l2) (Nat.sub acc.s2 (Nat.add 71417856000000000 acc.p2)))) (Nat.mul (Nat.sub u3 l3) (Nat.sub acc.s3 (Nat.add 85339136000000000 acc.p3)))) (Nat.mul (Nat.sub u4 l4) (Nat.sub acc.s4 (Nat.add 71417856000000000 acc.p4)))) (Nat.mul (Nat.sub u5 l5) (Nat.sub acc.s5 (Nat.add 60342272000000000 acc.p5)))) (Nat.mul (Nat.sub u6 l6) (Nat.sub acc.s6 (Nat.add 32596992000000000 acc.p6))))))) (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 31833 l0)) (Nat.mul 58928 l1)) (Nat.mul 69744 l2)) (Nat.mul 83339 l3)) (Nat.mul 69744 l4)) (Nat.mul 58928 l5)) (Nat.mul 31833 l6))) acc.A))

end AMW.Cert.AMT8MS
