#!/usr/bin/env python3
"""(bridge-port) The minorant leaf of an eight-point instance (AMT8 layout) as a chain of per-term steps over an
accumulator structure, in the exact form of the instance's `mscheck`: the accumulated fields are mscheck's sums
(Σ a·mval, Σ a·mcp, Σ a·mcn, per gap Σ a·(mw1 + mw2) and const + Σ a·msl, in term order) and the side condition of each
term is mscheck's (`m ≤ 1024 && mok …`), so `mleafS ≠ 0` gives `mscheck … = true` for the decoded fields and the
instance's `mscheck_sound` applies.  Each step reads only what its kind needs: a zero-order term (κ = 0) one pyramid
read, a tangent term no pyramid read when its constant weight is 0 and no second point when its weight is 0.
Same leaf word as `mleafN`.  Emits ROOT/AMW/{NAME}S.lean.  Usage: bp_mleafs2.py ROOT NAME [--noproof]"""
import sys, os
ROOT, NAME = sys.argv[1], sys.argv[2]
PROOF = "--noproof" not in sys.argv
HERE = os.path.dirname(os.path.abspath(__file__))
P = os.path.join(HERE, "..", ROOT, "AMW")
toks = open(os.path.join(HERE, f"{NAME}_params.txt")).read().split()
Q = int(toks[0]); aN = [int(x) for x in toks[2].split(",")]; bN = [int(x) for x in toks[3].split(",")]; cN = int(toks[4])
PAIRS = [(i, j) for i in range(Q) for j in range(i + 1, Q + 1)]
DT = [t for t in range(len(PAIRS)) if aN[t] != 0]
SC, U, U1 = 32768, 10**10, 10**9
WS = [f"W{r}" for r in range(Q)]; SS = [f"S{r}" for r in range(Q)]
F = ["o", "Am", "Ap", "B"] + WS + SS
HDR = "(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ))"
ARGS = "top bk tD bD pb R"
NS = f"AMW.Cert.{NAME}S"
box = " ".join(f"l{r} u{r}" for r in range(Q))


def ns(kind, i, j):
    e = f"{kind}{i}"
    for r in range(i + 1, j): e = f"(Nat.add {e} {kind}{r})"
    return e


def mk(ok, upd):
    return "⟨" + ok + ", " + ", ".join(upd.get(f, f"acc.{f}") for f in F) + "⟩"


# generic per-term expressions (those of mscheck), in the step's local names
MG = "(Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add o 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add o 6)) 1023) (Nat.beq k 2))"
PG = "(gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 15))"
RG = "(gptG L U (Nat.land (Nat.shiftRight w (Nat.add o 6)) 15))"
f_ = "(pt3 pb)"
COND = lambda m, p, r: f"(Nat.ble {m} 1024 && mok R tD bD {f_} L U (mw1 k {m}) (mw2 k {m}) {p} {r})"
V = lambda X: f"(lo32 {X})"; PP = lambda X: f"(lo32 (hi32 {X}))"; MM = lambda X: f"(hi32 (hi32 {X}))"

out = [f"import AMW.{NAME}Inst", "", "set_option maxRecDepth 100000", "", "noncomputable section", "",
       f"namespace {NS}", "", f"open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.{NAME}", "",
       "/-- the accumulator of a minorant leaf: side conditions so far, offset, and mscheck's sums so far -/",
       "structure MA where\n  (ok : Bool) (" + " ".join(F) + " : ℕ)", "",
       "/-- evaluate a natural before continuing with an accumulator (the kernel is call-by-name) -/",
       "def forceM (a : ℕ) (k : ℕ → MA) : MA := Nat.rec (motive := fun _ => MA) (k 0) (fun n _ => k (Nat.succ n)) a", "",
       "theorem forceM_eq (a : ℕ) (k : ℕ → MA) : forceM a k = k a := by cases a <;> rfl", ""]

for t in DT:
    i, j = PAIRS[t]; a = aN[t]; gaps = list(range(i, j))

    def upd(val, cp, cn, wt, sl):
        u = {"o": "(Nat.add o (mlen k))", "Am": f"(Nat.add acc.Am (Nat.mul {a} {val}))",
             "Ap": f"(Nat.add acc.Ap (Nat.mul {a} {cp}))", "B": f"(Nat.add acc.B (Nat.mul {a} {cn}))"}
        for r in gaps:
            u[f"W{r}"] = f"(Nat.add acc.W{r} (Nat.mul {a} {wt}))"; u[f"S{r}"] = f"(Nat.add acc.S{r} (Nat.mul {a} {sl}))"
        return u
    cp1 = lambda l, X, p: f"(Nat.mul (Nat.mul {l} (Nat.sub {MM(X)} 2000000000)) (Nat.sub {p} L))"
    cn1 = lambda l, X, p: f"(Nat.mul (Nat.mul {l} (Nat.sub 2000000000 {MM(X)})) (Nat.sub {p} L))"
    u1 = upd(f"(Nat.mul 1024 {V('X')})", cp1("1024", "X", "p"), cn1("1024", "X", "p"), "1024", f"(Nat.mul 1024 {PP('X')})")
    u2 = upd(f"(Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m {V('X')}))", cp1("m", "X", "p"), cn1("m", "X", "p"),
             "m", f"(Nat.mul m {PP('X')})")
    u3 = upd(f"(Nat.add (Nat.mul (Nat.sub 1024 m) {V('X')}) (Nat.mul m {V('Y')}))",
             f"(Nat.add {cp1('(Nat.sub 1024 m)', 'X', 'p')} {cp1('m', 'Y', 'r')})",
             f"(Nat.add {cn1('(Nat.sub 1024 m)', 'X', 'p')} {cn1('m', 'Y', 'r')})",
             "(Nat.add (Nat.sub 1024 m) m)", f"(Nat.add (Nat.mul (Nat.sub 1024 m) {PP('X')}) (Nat.mul m {PP('Y')}))")
    uz = {"o": "(Nat.add o (mlen k))", "Am": f"(Nat.add acc.Am (Nat.mul {a} (Nat.mul 1024 (lb top bk L U))))"}
    out.append(f"""/-- term {t} (gaps {i}..{j - 1}, weight {a}), kinds 1–3: tangents at grid points -/
def tg{t} {HDR} (w L U o k : ℕ) (acc : MA) : MA :=
  forceM L fun L => forceM U fun U =>
  forceM {MG} fun m =>
  forceM {PG} fun p =>
  forceM ({f_} p) fun X =>
  Bool.rec (motive := fun _ => MA)
    (Bool.rec (motive := fun _ => MA)
      (forceM {RG} fun r => forceM ({f_} r) fun Y => {mk(f"(acc.ok && {COND('m', 'p', 'r')})", u3)})
      {mk(f"(acc.ok && {COND('m', 'p', RG)})", u2)} (Nat.beq k 2))
    {mk(f"(acc.ok && {COND('m', 'p', RG)})", u1)} (Nat.beq k 1)

/-- term {t}: zero order (kind 0, one pyramid read), else `tg{t}` -/
def st{t} {HDR} (w L U : ℕ) (acc : MA) : MA :=
  forceM acc.o fun o =>
  forceM (Nat.land (Nat.shiftRight w o) 3) fun k =>
  Bool.rec (motive := fun _ => MA) (tg{t} {ARGS} w L U o k acc) {mk("acc.ok", uz)} (Nat.beq k 0)
""")

chain = "⟨true, " + ", ".join(("0" if f[0] != "S" else str(1024 * U1 * bN[int(f[1:])])) for f in F) + "⟩"
for t in DT:
    i, j = PAIRS[t]
    chain = f"(st{t} {ARGS} w {ns('l', i, j)} {ns('u', i, j)} {chain})"
boxc = " && ".join(f"Nat.ble l{r} u{r}" for r in range(Q))
linb = f"(Nat.mul {bN[0]} l0)"
for r in range(1, Q): linb = f"(Nat.add {linb} (Nat.mul {bN[r]} l{r}))"
gp = lambda r: f"(Nat.mul (Nat.sub u{r} l{r}) (Nat.sub (Nat.mul 2000000000 acc.W{r}) acc.S{r}))"
gs = gp(0)
for r in range(1, Q): gs = f"(Nat.add {gs} {gp(r)})"
main = (f"Nat.ble (Nat.add {1024 * cN * SC * U} (Nat.mul 10 (Nat.add acc.B {gs}))) "
        f"(Nat.add (Nat.add (Nat.mul {1024 * U} {linb}) (Nat.mul 32768 acc.Am)) (Nat.mul 10 acc.Ap))")
out.append(f"""/-- the minorant leaf: the payload length when the box conditions, every term's side condition and the minorant
inequality hold, else `0` -/
def mleafS {HDR} (w {box} : ℕ) : ℕ :=
  let acc := {chain}
  Bool.rec (motive := fun _ => ℕ) 0 acc.o ((({boxc}) && acc.ok) && {main})
""")
if PROOF:
    IMPL = "{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}"
    out.append("""/-! ### soundness: every step is mscheck's term update; the leaf gives `mscheck` for the decoded fields -/

theorem nadd0 (x : ℕ) : Nat.add 0 x = x := Nat.zero_add x

theorem land_ble (x : ℕ) : Nat.ble (Nat.land x 1023) 1024 = true := by
  rw [Nat.ble_eq]; exact le_trans Nat.and_le_right (by norm_num)

theorem land3_lt (x : ℕ) : Nat.land x 3 < 4 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem and1023_le (x : ℕ) : x &&& 1023 ≤ 1024 := le_trans Nat.and_le_right (by norm_num)

theorem brf {α : Sort _} (x y : α) : Bool.rec (motive := fun _ => α) x y false = x := rfl
theorem brt {α : Sort _} (x y : α) : Bool.rec (motive := fun _ => α) x y true = y := rfl
""" + "\n".join(f"theorem nb{a}{b} : Nat.beq {a} {b} = {'true' if a == b else 'false'} := rfl" for a in range(4) for b in range(4)) + "\n")
    # generic decoded values of a step at accumulator `acc`
    Ko = "(Nat.land (Nat.shiftRight w acc.o) 3)"
    Mo = f"(Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add acc.o 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add acc.o 6)) 1023) (Nat.beq {Ko} 2))"
    Po = "(gptG L U (Nat.land (Nat.shiftRight w (Nat.add acc.o 2)) 15))"
    Ro = "(gptG L U (Nat.land (Nat.shiftRight w (Nat.add acc.o 6)) 15))"
    W1 = f"(mw1 {Ko} {Mo})"; W2 = f"(mw2 {Ko} {Mo})"; WC = f"(mwc {Ko} {Mo})"
    CONDo = f"(Nat.ble {Mo} 1024 && mok R tD bD {f_} L U {W1} {W2} {Po} {Ro})"
    MVAL = f"(mval top bk {f_} L U {WC} {W1} {W2} {Po} {Ro})"
    MCP = f"(mcp {f_} L {W1} {W2} {Po} {Ro})"; MCN = f"(mcn {f_} L {W1} {W2} {Po} {Ro})"
    MSL = f"(msl {f_} {W1} {W2} {Po} {Ro})"; WT = f"(Nat.add {W1} {W2})"
    for t in DT:
        i, j = PAIRS[t]; a = aN[t]; gaps = list(range(i, j))
        u = {"o": f"(Nat.add acc.o (mlen {Ko}))", "Am": f"(Nat.add acc.Am (Nat.mul {a} {MVAL}))",
             "Ap": f"(Nat.add acc.Ap (Nat.mul {a} {MCP}))", "B": f"(Nat.add acc.B (Nat.mul {a} {MCN}))"}
        for r in gaps:
            u[f"W{r}"] = f"(Nat.add acc.W{r} (Nat.mul {a} {WT}))"; u[f"S{r}"] = f"(Nat.add acc.S{r} (Nat.mul {a} {MSL}))"
        out.append(f"""theorem st{t}_eq {IMPL} (w L U : ℕ) (acc : MA) :
    st{t} {ARGS} w L U acc = {mk(f"(acc.ok && {CONDo})", u)} := by
  unfold st{t} tg{t}
  simp only [forceM_eq]
  generalize hk : Nat.land (Nat.shiftRight w acc.o) 3 = k
  have hk4 : k < 4 := hk ▸ land3_lt _
  interval_cases k <;> simp [mval, mcp, mcn, msl, mwc, mw1, mw2, mlen, mok, land_ble, and1023_le, brf, brt, nb00, nb01, nb02, nb03, nb10, nb11, nb12, nb13, nb20, nb21, nb22, nb23, nb30, nb31, nb32, nb33]
""")
    # the leaf theorem
    names = [f"A{t}" for t in DT]
    init = "⟨true, " + ", ".join(("0" if f[0] != "S" else str(1024 * U1 * bN[int(f[1:])])) for f in F) + "⟩"
    gens = []; prev = init; prevname = None
    for idx, t in enumerate(DT):
        i, j = PAIRS[t]
        gens.append(f"  generalize hA{t} : st{t} {ARGS} w {ns('l', i, j)} {ns('u', i, j)} {prev} = A{t} at h")
        prev = f"A{t}"
    lines = []
    lines.append(f"""set_option maxHeartbeats 40000000 in
theorem mleafS_mscheck {IMPL} (w {box} : ℕ) (h : mleafS {ARGS} w {box} ≠ 0) :
    ∃ """ + " ".join(f"k{t} m{t} p{t} r{t}" for t in DT) + f""" : ℕ, mscheck top bk tD bD (pt3 pb) R {box} """ + " ".join(f"k{t} m{t} p{t} r{t}" for t in DT) + """ = true := by
  unfold mleafS at h
  dsimp only at h""")
    lines += gens
    # field equations
    prevA = None
    eqs = []
    for idx, t in enumerate(DT):
        i, j = PAIRS[t]
        lines.append(f"  rw [st{t}_eq] at hA{t}")
        for fname in ["ok", "Am", "Ap", "B"] + WS + SS:
            nm = f"e{fname}{t}"
            lines.append(f"  have {nm} : A{t}.{fname} = _ := (congrArg MA.{fname} hA{t}).symm")
            eqs.append(nm)
    lines.append("  have hb := brec_ne h")
    lines.append("  simp only [Bool.and_eq_true] at hb")
    lines.append("  obtain ⟨⟨hbox, hok⟩, hmain⟩ := hb")
    lines.append(f"  simp only [{', '.join(eqs)}] at hok hmain")
    lines.append("  simp only [nadd0] at hmain")
    # witnesses: the decoded values at each step's input accumulator
    wit = []
    prevacc = init
    for idx, t in enumerate(DT):
        i, j = PAIRS[t]
        o = "(0 : ℕ)" if idx == 0 else f"A{DT[idx - 1]}.o"
        Lx, Ux = ns('l', i, j), ns('u', i, j)
        K = f"(Nat.land (Nat.shiftRight w {o}) 3)"
        wit += [K, f"(Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add {o} 10)) 1023) (Nat.land (Nat.shiftRight w (Nat.add {o} 6)) 1023) (Nat.beq {K} 2))",
                f"(gptG {Lx} {Ux} (Nat.land (Nat.shiftRight w (Nat.add {o} 2)) 15))", f"(gptG {Lx} {Ux} (Nat.land (Nat.shiftRight w (Nat.add {o} 6)) 15))"]
    lines.append("  refine ⟨" + ", ".join(wit) + ", ?_⟩")
    lines.append("  simp only [Bool.and_eq_true] at hbox hok")
    lines.append("  unfold mscheck")
    lines.append("  simp only [Bool.and_eq_true]")
    lines.append("  refine ⟨?_, hmain⟩")
    lines.append("  simp_all")
    out.append("\n".join(lines) + "\n")
    out.append(f"""/-- **the minorant leaf is sound**: a nonzero `mleafS` certifies the box -/
theorem mleafS_sound {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true)
    (w {box} : ℕ) (h : mleafS {ARGS} w {box} ≠ 0) :
    ∀ {' '.join(f'g{r}' for r in range(Q))} : ℝ, {' → '.join(f'(l{r} : ℝ) / SC ≤ g{r} → g{r} ≤ (u{r} : ℝ) / SC' for r in range(Q))} → (cN : ℝ) / SA ≤ G {' '.join(f'g{r}' for r in range(Q))} := by
  obtain ⟨{', '.join(f'k{t}, m{t}, p{t}, r{t}' for t in DT)}, hm⟩ := mleafS_mscheck w {box} h
  exact mscheck_sound (f := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ {' '.join('_ _ _ _' for _ in DT)} hm
""")
out.append(f"end {NS}\n")
open(os.path.join(P, f"{NAME}S.lean"), "w").write("\n".join(out))
print("written", len(DT), "steps", "(with proofs)" if PROOF else "(no proofs)")
