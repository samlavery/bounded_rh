import AMW.AMT8Inst

set_option maxRecDepth 100000

noncomputable section

namespace AMW.Cert.AMT8MO

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.AMT8

/-- term 0, kind 1: the tangent at `p` -/
def ta0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 16682481664 (lo32 (hi32 X))) fun sp =>
  forceR 33364963328000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 533839413248 (Nat.mul 1024 (lo32 X))) (Nat.mul 162914860 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 16291486 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 0, kind 2: the constant and the tangent at `p` -/
def tb0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 16291486 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 32582972000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 162914860 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 16291486 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 0, kind 3: the tangents at `p` and `r` -/
def tc0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 33364963328000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 162914860 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 0 (gaps 0..0, weight 16291486) -/
def st0 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc0 top bk tD bD pb R w L U acc o) (tb0 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta0 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 546651559165952 7) 100)) true

/-- term 3, kind 1: the tangent at `p` -/
def ta3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 3, kind 2: the constant and the tangent at `p` -/
def tb3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 200000000000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 3, kind 3: the tangents at `p` and `r` -/
def tc3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 3 (gaps 0..3, weight 100000000) -/
def st3 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc3 top bk tD bD pb R w L U acc o) (tb3 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta3 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 3355443200000000 7) 100)) true

/-- term 4, kind 1: the tangent at `p` -/
def ta4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 39942497280 (lo32 (hi32 X))) fun sp =>
  forceR 79884994560000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1278159912960 (Nat.mul 1024 (lo32 X))) (Nat.mul 390063450 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 39006345 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 4, kind 2: the constant and the tangent at `p` -/
def tb4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 39006345 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 78012690000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 390063450 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 39006345 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 4, kind 3: the tangents at `p` and `r` -/
def tc4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 79884994560000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 390063450 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 4 (gaps 0..4, weight 39006345) -/
def st4 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc4 top bk tD bD pb R w L U acc o) (tb4 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta4 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 1308835750871040 7) 100)) true

/-- term 5, kind 1: the tangent at `p` -/
def ta5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 5, kind 2: the constant and the tangent at `p` -/
def tb5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 200000000000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 5, kind 3: the tangents at `p` and `r` -/
def tc5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 5 (gaps 0..5, weight 100000000) -/
def st5 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc5 top bk tD bD pb R w L U acc o) (tb5 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta5 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 3355443200000000 7) 100)) true

/-- term 6, kind 1: the tangent at `p` -/
def ta6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 204800000000 (lo32 (hi32 X))) fun sp =>
  forceR 409600000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 6553600000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 2000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 200000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 6, kind 2: the constant and the tangent at `p` -/
def tb6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 200000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 400000000000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 6553600000000 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 2000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 200000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 6, kind 3: the tangents at `p` and `r` -/
def tc6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 200000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 409600000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 6553600000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 2000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 200000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 300) (Nat.shiftLeft sw 1000))) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 6 (gaps 0..6, weight 200000000) -/
def st6 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc6 top bk tD bD pb R w L U acc o) (tb6 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta6 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 6710886400000000 7) 100)) true

/-- term 7, kind 1: the tangent at `p` -/
def ta7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 32852407296 (lo32 (hi32 X))) fun sp =>
  forceR 65704814592000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1051277033472 (Nat.mul 1024 (lo32 X))) (Nat.mul 320824290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32082429 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 7, kind 2: the constant and the tangent at `p` -/
def tb7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 32082429 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 64164858000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 320824290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32082429 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 7, kind 3: the tangents at `p` and `r` -/
def tc7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 65704814592000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 320824290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 7 (gaps 1..1, weight 32082429) -/
def st7 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc7 top bk tD bD pb R w L U acc o) (tb7 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta7 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 1076507682275328 7) 100)) true

/-- term 8, kind 1: the tangent at `p` -/
def ta8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 3837002752 (lo32 (hi32 X))) fun sp =>
  forceR 7674005504000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 122784088064 (Nat.mul 1024 (lo32 X))) (Nat.mul 37470730 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 3747073 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 8, kind 2: the constant and the tangent at `p` -/
def tb8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 3747073 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 7494146000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 37470730 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 3747073 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 8, kind 3: the tangents at `p` and `r` -/
def tc8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 7674005504000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 37470730 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 8 (gaps 1..2, weight 3747073) -/
def st8 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc8 top bk tD bD pb R w L U acc o) (tb8 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta8 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 125730906177536 7) 100)) true

/-- term 9, kind 1: the tangent at `p` -/
def ta9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 61062890496 (lo32 (hi32 X))) fun sp =>
  forceR 122125780992000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1954012495872 (Nat.mul 1024 (lo32 X))) (Nat.mul 596317290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 59631729 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 9, kind 2: the constant and the tangent at `p` -/
def tb9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 59631729 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 119263458000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 596317290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 59631729 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 9, kind 3: the tangents at `p` and `r` -/
def tc9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 122125780992000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 596317290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 9 (gaps 1..3, weight 59631729) -/
def st9 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc9 top bk tD bD pb R w L U acc o) (tb9 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta9 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 2000908795772928 7) 100)) true

/-- term 11, kind 1: the tangent at `p` -/
def ta11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 124915005440 (lo32 (hi32 X))) fun sp =>
  forceR 249830010880000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 3997280174080 (Nat.mul 1024 (lo32 X))) (Nat.mul 1219873100 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 121987310 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 11, kind 2: the constant and the tangent at `p` -/
def tb11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 121987310 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 243974620000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 3997280174080 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 1219873100 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 121987310 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 11, kind 3: the tangents at `p` and `r` -/
def tc11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 121987310 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 249830010880000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 3997280174080 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1219873100 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 121987310 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 11 (gaps 1..5, weight 121987310) -/
def st11 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc11 top bk tD bD pb R w L U acc o) (tb11 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta11 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 4093214898257920 7) 100)) true

/-- term 12, kind 1: the tangent at `p` -/
def ta12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 12, kind 2: the constant and the tangent at `p` -/
def tb12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 200000000000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 12, kind 3: the tangents at `p` and `r` -/
def tc12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 400) (Nat.shiftLeft sw 1100))) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 12 (gaps 1..6, weight 100000000) -/
def st12 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc12 top bk tD bD pb R w L U acc o) (tb12 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta12 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 3355443200000000 7) 100)) true

/-- term 13, kind 1: the tangent at `p` -/
def ta13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 33509000192 (lo32 (hi32 X))) fun sp =>
  forceR 67018000384000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1072288006144 (Nat.mul 1024 (lo32 X))) (Nat.mul 327236330 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32723633 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 13, kind 2: the constant and the tangent at `p` -/
def tb13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 32723633 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 65447266000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 327236330 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32723633 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 13, kind 3: the tangents at `p` and `r` -/
def tc13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 67018000384000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 327236330 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 13 (gaps 2..2, weight 32723633) -/
def st13 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc13 top bk tD bD pb R w L U acc o) (tb13 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta13 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 1098022918291456 7) 100)) true

/-- term 14, kind 1: the tangent at `p` -/
def ta14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 98562997248 (lo32 (hi32 X))) fun sp =>
  forceR 197125994496000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 3154015911936 (Nat.mul 1024 (lo32 X))) (Nat.mul 962529270 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 96252927 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 14, kind 2: the constant and the tangent at `p` -/
def tb14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 96252927 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 192505854000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 962529270 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 96252927 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 14, kind 3: the tangents at `p` and `r` -/
def tc14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 197125994496000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 962529270 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 14 (gaps 2..3, weight 96252927) -/
def st14 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc14 top bk tD bD pb R w L U acc o) (tb14 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta14 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 3229712293822464 7) 100)) true

/-- term 15, kind 1: the tangent at `p` -/
def ta15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 82674219008 (lo32 (hi32 X))) fun sp =>
  forceR 165348438016000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 2645575008256 (Nat.mul 1024 (lo32 X))) (Nat.mul 807365420 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 80736542 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 15, kind 2: the constant and the tangent at `p` -/
def tb15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 80736542 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 161473084000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 2645575008256 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 807365420 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 80736542 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 15, kind 3: the tangents at `p` and `r` -/
def tc15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 80736542 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 165348438016000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 2645575008256 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 807365420 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 80736542 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 15 (gaps 2..4, weight 80736542) -/
def st15 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc15 top bk tD bD pb R w L U acc o) (tb15 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta15 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 2709068808454144 7) 100)) true

/-- term 17, kind 1: the tangent at `p` -/
def ta17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 39942497280 (lo32 (hi32 X))) fun sp =>
  forceR 79884994560000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1278159912960 (Nat.mul 1024 (lo32 X))) (Nat.mul 390063450 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 39006345 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 17, kind 2: the constant and the tangent at `p` -/
def tb17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 39006345 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 78012690000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 390063450 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 39006345 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 17, kind 3: the tangents at `p` and `r` -/
def tc17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 79884994560000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1278159912960 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 390063450 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 39006345 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 500) (Nat.shiftLeft sw 1200))) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 17 (gaps 2..6, weight 39006345) -/
def st17 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc17 top bk tD bD pb R w L U acc o) (tb17 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta17 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 1308835750871040 7) 100)) true

/-- term 18, kind 1: the tangent at `p` -/
def ta18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 38712221696 (lo32 (hi32 X))) fun sp =>
  forceR 77424443392000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1238791094272 (Nat.mul 1024 (lo32 X))) (Nat.mul 378049040 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 37804904 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 18, kind 2: the constant and the tangent at `p` -/
def tb18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 37804904 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 75609808000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1238791094272 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 378049040 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 37804904 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 18, kind 3: the tangents at `p` and `r` -/
def tc18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 37804904 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 77424443392000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1238791094272 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 378049040 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 37804904 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 18 (gaps 3..3, weight 37804904) -/
def st18 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc18 top bk tD bD pb R w L U acc o) (tb18 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta18 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 1268522080534528 7) 100)) true

/-- term 19, kind 1: the tangent at `p` -/
def ta19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 98562997248 (lo32 (hi32 X))) fun sp =>
  forceR 197125994496000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 3154015911936 (Nat.mul 1024 (lo32 X))) (Nat.mul 962529270 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 96252927 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 19, kind 2: the constant and the tangent at `p` -/
def tb19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 96252927 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 192505854000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 962529270 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 96252927 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 19, kind 3: the tangents at `p` and `r` -/
def tc19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 197125994496000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 3154015911936 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 962529270 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 96252927 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 19 (gaps 3..4, weight 96252927) -/
def st19 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc19 top bk tD bD pb R w L U acc o) (tb19 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta19 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 3229712293822464 7) 100)) true

/-- term 20, kind 1: the tangent at `p` -/
def ta20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 61062890496 (lo32 (hi32 X))) fun sp =>
  forceR 122125780992000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1954012495872 (Nat.mul 1024 (lo32 X))) (Nat.mul 596317290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 59631729 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 20, kind 2: the constant and the tangent at `p` -/
def tb20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 59631729 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 119263458000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 596317290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 59631729 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 20, kind 3: the tangents at `p` and `r` -/
def tc20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 122125780992000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1954012495872 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 596317290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 59631729 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 20 (gaps 3..5, weight 59631729) -/
def st20 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc20 top bk tD bD pb R w L U acc o) (tb20 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta20 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 2000908795772928 7) 100)) true

/-- term 21, kind 1: the tangent at `p` -/
def ta21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 102400000000 (lo32 (hi32 X))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.mul 1024 (lo32 X))) (Nat.mul 1000000000 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 21, kind 2: the constant and the tangent at `p` -/
def tb21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 100000000 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 200000000000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 1000000000 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 21, kind 3: the tangents at `p` and `r` -/
def tc21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 204800000000000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 3276800000000 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 1000000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 100000000 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 600) (Nat.shiftLeft sw 1300))) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 21 (gaps 3..6, weight 100000000) -/
def st21 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc21 top bk tD bD pb R w L U acc o) (tb21 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta21 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 3355443200000000 7) 100)) true

/-- term 22, kind 1: the tangent at `p` -/
def ta22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 33509000192 (lo32 (hi32 X))) fun sp =>
  forceR 67018000384000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1072288006144 (Nat.mul 1024 (lo32 X))) (Nat.mul 327236330 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32723633 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 22, kind 2: the constant and the tangent at `p` -/
def tb22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 32723633 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 65447266000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 327236330 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32723633 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 22, kind 3: the tangents at `p` and `r` -/
def tc22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 67018000384000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1072288006144 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 327236330 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 32723633 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 22 (gaps 4..4, weight 32723633) -/
def st22 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc22 top bk tD bD pb R w L U acc o) (tb22 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta22 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 1098022918291456 7) 100)) true

/-- term 23, kind 1: the tangent at `p` -/
def ta23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 3837002752 (lo32 (hi32 X))) fun sp =>
  forceR 7674005504000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 122784088064 (Nat.mul 1024 (lo32 X))) (Nat.mul 37470730 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 3747073 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 23, kind 2: the constant and the tangent at `p` -/
def tb23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 3747073 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 7494146000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 37470730 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 3747073 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 23, kind 3: the tangents at `p` and `r` -/
def tc23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 7674005504000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 122784088064 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 37470730 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 3747073 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 700) (Nat.shiftLeft sw 1400))) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 23 (gaps 4..5, weight 3747073) -/
def st23 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc23 top bk tD bD pb R w L U acc o) (tb23 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta23 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 125730906177536 7) 100)) true

/-- term 25, kind 1: the tangent at `p` -/
def ta25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 32852407296 (lo32 (hi32 X))) fun sp =>
  forceR 65704814592000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 1051277033472 (Nat.mul 1024 (lo32 X))) (Nat.mul 320824290 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32082429 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 25, kind 2: the constant and the tangent at `p` -/
def tb25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 32082429 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 64164858000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 320824290 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 32082429 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 25, kind 3: the tangents at `p` and `r` -/
def tc25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 65704814592000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 1051277033472 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 320824290 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 32082429 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 800) (Nat.shiftLeft sw 1500))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 25 (gaps 5..5, weight 32082429) -/
def st25 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc25 top bk tD bD pb R w L U acc o) (tb25 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta25 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 1076507682275328 7) 100)) true

/-- term 27, kind 1: the tangent at `p` -/
def ta27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 16682481664 (lo32 (hi32 X))) fun sp =>
  forceR 33364963328000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 6) (Nat.shiftLeft (Nat.add (Nat.mul 533839413248 (Nat.mul 1024 (lo32 X))) (Nat.mul 162914860 (Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 16291486 (Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))

/-- term 27, kind 2: the constant and the tangent at `p` -/
def tb27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (pt3 pb p) fun X =>
  forceR (Nat.mul 16291486 (Nat.mul m (lo32 (hi32 X)))) fun sp =>
  forceR (Nat.mul 32582972000000000 m) fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 16) (Nat.shiftLeft (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) 7) (Nat.mul m (lo32 X)))) (Nat.mul 162914860 (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)))) 100)) (Nat.shiftLeft (Nat.mul 16291486 (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L))) 200)) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) (Nat.beq m 0 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p)))

/-- term 27, kind 3: the tangents at `p` and `r` -/
def tc27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc o : ℕ) : ℕ :=
  forceR L fun L => forceR U fun U =>
  forceR (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) fun m =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15)) fun p =>
  forceR (gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15)) fun r =>
  forceR (pt3 pb p) fun X => forceR (pt3 pb r) fun Y =>
  forceR (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 X))) (Nat.mul m (lo32 (hi32 Y))))) fun sp =>
  forceR 33364963328000000000 fun sw =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.add (Nat.add (Nat.add (Nat.add acc 20) (Nat.shiftLeft (Nat.add (Nat.mul 533839413248 (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 X)) (Nat.mul m (lo32 Y)))) (Nat.mul 162914860 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub (hi32 (hi32 X)) 2000000000)) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub (hi32 (hi32 Y)) 2000000000)) (Nat.sub r L))))) 100)) (Nat.shiftLeft (Nat.mul 16291486 (Nat.add (Nat.mul (Nat.mul (Nat.sub 1024 m) (Nat.sub 2000000000 (hi32 (hi32 X)))) (Nat.sub p L)) (Nat.mul (Nat.mul m (Nat.sub 2000000000 (hi32 (hi32 Y)))) (Nat.sub r L)))) 200)) (Nat.add (Nat.shiftLeft sp 900) (Nat.shiftLeft sw 1600))) ((Nat.beq m 1024 || (tcheck R L U p X (treadU R tD bD U p) (treadD R tD bD L p))) && (Nat.beq m 0 || (tcheck R L U r Y (treadU R tD bD U r) (treadD R tD bD L r))))

/-- term 27 (gaps 6..6, weight 16291486) -/
def st27 (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w L U acc : ℕ) : ℕ :=
  forceR acc fun acc =>
  forceR (Nat.land acc 4095) fun o =>
  forceR (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (tc27 top bk tD bD pb R w L U acc o) (tb27 top bk tD bD pb R w L U acc o) (Nat.beq k 2))
      (ta27 top bk tD bD pb R w L U acc o) (Nat.beq k 1))
    (Nat.add (Nat.add acc 2) (Nat.shiftLeft (Nat.mul 546651559165952 7) 100)) true

/-- the minorant leaf as a chain of term steps: the payload length when it passes, else `0` -/
def mleafC (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 : ℕ) : ℕ :=
  forceR (st27 top bk tD bD pb R w l6 u6 (st25 top bk tD bD pb R w l5 u5 (st23 top bk tD bD pb R w (Nat.add l4 l5) (Nat.add u4 u5) (st22 top bk tD bD pb R w l4 u4 (st21 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add l3 l4) l5) l6) (Nat.add (Nat.add (Nat.add u3 u4) u5) u6) (st20 top bk tD bD pb R w (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (st19 top bk tD bD pb R w (Nat.add l3 l4) (Nat.add u3 u4) (st18 top bk tD bD pb R w l3 u3 (st17 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) u6) (st15 top bk tD bD pb R w (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (st14 top bk tD bD pb R w (Nat.add l2 l3) (Nat.add u2 u3) (st13 top bk tD bD pb R w l2 u2 (st12 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) u6) (st11 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (st9 top bk tD bD pb R w (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (st8 top bk tD bD pb R w (Nat.add l1 l2) (Nat.add u1 u2) (st7 top bk tD bD pb R w l1 u1 (st6 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) l6) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) u6) (st5 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (st4 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (st3 top bk tD bD pb R w (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (st0 top bk tD bD pb R w l0 u0 (Nat.shiftLeft 1 1700))))))))))))))))))))))) fun acc =>
  Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight acc 0) 1267650600228229401496703205375) (Nat.ble 56362808934785782620655415167470525914030964411108314940402423418609289689068355355971379591897745173403010078263747529856646401949852539644969848434700186501722593132609102394906926373262117075563330306831364144677433787178189964179613588058505555939250641616528896329618001580624087604790707070002646363767810376024580461947390375276158858357529962546338406854636102805723631292609311399696875316557143945391102311532165688506692261634047197324706752950818927815472385992693228752306187618995383028460736741376 acc && Nat.ble (Nat.add 187231046205440000000000 (Nat.mul 10 (Nat.add (Nat.land (Nat.shiftRight acc 200) 1267650600228229401496703205375) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub u0 l0) (Nat.sub (Nat.land (Nat.shiftRight acc 1000) 1267650600228229401496703205375) (Nat.add 32596992000000000 (Nat.land (Nat.shiftRight acc 300) 1267650600228229401496703205375))))) (Nat.mul (Nat.sub u1 l1) (Nat.sub (Nat.land (Nat.shiftRight acc 1100) 1267650600228229401496703205375) (Nat.add 60342272000000000 (Nat.land (Nat.shiftRight acc 400) 1267650600228229401496703205375))))) (Nat.mul (Nat.sub u2 l2) (Nat.sub (Nat.land (Nat.shiftRight acc 1200) 1267650600228229401496703205375) (Nat.add 71417856000000000 (Nat.land (Nat.shiftRight acc 500) 1267650600228229401496703205375))))) (Nat.mul (Nat.sub u3 l3) (Nat.sub (Nat.land (Nat.shiftRight acc 1300) 1267650600228229401496703205375) (Nat.add 85339136000000000 (Nat.land (Nat.shiftRight acc 600) 1267650600228229401496703205375))))) (Nat.mul (Nat.sub u4 l4) (Nat.sub (Nat.land (Nat.shiftRight acc 1400) 1267650600228229401496703205375) (Nat.add 71417856000000000 (Nat.land (Nat.shiftRight acc 700) 1267650600228229401496703205375))))) (Nat.mul (Nat.sub u5 l5) (Nat.sub (Nat.land (Nat.shiftRight acc 1500) 1267650600228229401496703205375) (Nat.add 60342272000000000 (Nat.land (Nat.shiftRight acc 800) 1267650600228229401496703205375))))) (Nat.mul (Nat.sub u6 l6) (Nat.sub (Nat.land (Nat.shiftRight acc 1600) 1267650600228229401496703205375) (Nat.add 32596992000000000 (Nat.land (Nat.shiftRight acc 900) 1267650600228229401496703205375)))))))) (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 31833 l0)) (Nat.mul 58928 l1)) (Nat.mul 69744 l2)) (Nat.mul 83339 l3)) (Nat.mul 69744 l4)) (Nat.mul 58928 l5)) (Nat.mul 31833 l6))) (Nat.land (Nat.shiftRight acc 100) 1267650600228229401496703205375)))

end AMW.Cert.AMT8MO
