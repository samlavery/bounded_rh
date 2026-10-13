"""The mixed basin test of the seven-point instance (text for gen7.checker): `cscheck` / `ctest`, the slope test in which
each expanded term is either convex (a chain of cells on which w'' >= 0, no charge; bit of `V`) or charged from the
derivative reads; `ctest_sound`, `covered_of_ctest`."""
from gen7 import Q, PAIRS, NP, TS, SC, U, U1, RU, CO, COORDS, QV, V, mem, HV, ssum, nsum, nadd, bit, term_g

def ctest_part(NAME, aN, bN, cN):
    C = cN * SC * U
    XV = " ".join(f"x{t} eu{t} ed{t}" for t in range(NP))
    def vbit(t): return f"(bitOf V {t})"
    CV = " ".join(f"c{t}" for t in range(NP))
    conds = []
    for r in range(Q): conds += [f"Nat.ble l{r} q{r}", f"Nat.ble q{r} u{r}"]
    for t, (i, j) in enumerate(PAIRS):
        conds.append(f"mtok {vbit(t)} {bit(t)} {nsum('l', i, j)} {nsum('u', i, j)} {nsum('q', i, j)} x{t} eu{t} ed{t} c{t}")
    cexpr = conds[0]
    for c in conds[1:]: cexpr = f"({cexpr} && {c})"
    pen = []
    for r in range(Q):
        Kx = nadd([str(U1 * bN[r])] + [f"(Nat.mul {aN[t]} (tK {bit(t)}))" for t in TS[r]])
        Mx = nadd([f"(Nat.mul {aN[t]} (tM {bit(t)} x{t}))" for t in TS[r]])
        Kn = nadd([f"(Nat.mul {aN[t]} (tK {bit(t)}))" for t in TS[r]])
        Px = nadd([str(U1 * bN[r])] + [f"(Nat.mul {aN[t]} (tP {bit(t)} x{t}))" for t in TS[r]])
        pen.append(f"(Nat.mul (Nat.sub q{r} l{r}) (Nat.sub {Kx} {Mx}))")
        pen.append(f"(Nat.mul (Nat.sub u{r} q{r}) (Nat.sub {Kn} {Px}))")
    chg = [f"(Nat.mul {aN[t]} (mchg {vbit(t)} {bit(t)} {nsum('l', i, j)} {nsum('u', i, j)} {nsum('q', i, j)} x{t} eu{t} ed{t}))" for t, (i, j) in enumerate(PAIRS)]
    rhs = f"(Nat.add {C} (Nat.mul {RU} (Nat.add {nadd(pen)} {nadd(chg)})))"
    linq = nadd([f"(Nat.mul {bN[r]} q{r})" for r in range(Q)])
    vals = nadd([f"(Nat.mul {aN[t]} (tval {bit(t)} x{t}))" for t in range(NP)])
    lhs = f"(Nat.add (Nat.mul {U} {linq}) (Nat.mul {SC} {vals}))"
    CCHECK = f"{cexpr} && Nat.ble {rhs} {lhs}"
    ST = []
    for t, (i, j) in enumerate(PAIRS):
        L, Uu, QS = nsum('l', i, j), nsum('u', i, j), nsum('q', i, j)
        ST.append(f"forceB (selXf {bit(t)} top bk pb {L} {Uu} {QS}) fun x{t} =>")
        ST.append(f"forceB (selUv {vbit(t)} {bit(t)} tD bD {QS} {Uu}) fun eu{t} =>")
        ST.append(f"forceB (selDv {vbit(t)} {bit(t)} tD bD {L} {QS}) fun ed{t} =>")
    CTEST = "\n  ".join(ST) + f"\n  cscheck {COORDS} {QV} T V {XV} {CV}"
    XARGS = " ".join(f"(selXf {bit(t)} top bk pb ({ssum('l', i, j)}) ({ssum('u', i, j)}) ({ssum('q', i, j)})) (selUv {vbit(t)} {bit(t)} tD bD ({ssum('q', i, j)}) ({ssum('u', i, j)})) (selDv {vbit(t)} {bit(t)} tD bD ({ssum('l', i, j)}) ({ssum('q', i, j)}))" for t, (i, j) in enumerate(PAIRS))
    flat = []
    for r in range(Q): flat += [f"hq{r}1", f"hq{r}2"]
    for t in range(NP): flat.append(f"hok{t}")
    pat = flat[0]
    for c in flat[1:]: pat = f"⟨{pat}, {c}⟩"
    pat = f"⟨{pat}, hmain⟩"
    out = f"""
/-- the convex-basin inequality at the point `q` with expansion set `T`, given the per-term reads `x_t` and chains
`c_t`: `cN·SC·U + (U/U1)·Σ_r ((q_r − l_r)·Pos_r + (u_r − q_r)·Neg_r) ≤ U·Σ b_r q_r + SC·Σ a_t·val_t` -/
def cscheck ({COORDS} : ℕ) ({QV} : ℕ) (T V : ℕ) ({XV} : ℕ) ({CV} : List ℕ) : Bool :=
  {CCHECK}

/-- the convex-basin test at the point `q` with expansion set `T` and chains `c_t` -/
def ctest (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) ({COORDS} : ℕ) ({QV} : ℕ) (T V : ℕ) ({CV} : List ℕ) : Bool :=
  {CTEST}

theorem ctest_spec {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} ({COORDS} : ℕ) ({QV} : ℕ) (T V : ℕ) ({CV} : List ℕ)
    (h : ctest top bk tD bD pb {COORDS} {QV} T V {CV} = true) :
    cscheck {COORDS} {QV} T V {XARGS} {CV} = true := by
  unfold ctest at h
  simp only [forceB_eq] at h
  exact h

set_option maxHeartbeats 40000000 in
theorem ctest_sound {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) ({COORDS} : ℕ)
    ({QV} : ℕ) (T V : ℕ) ({CV} : List ℕ) (h : ctest top bk tD bD pb {COORDS} {QV} T V {CV} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {HV}
  have h' := ctest_spec {COORDS} {QV} T V {CV} h
  unfold cscheck at h'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h'
  obtain {pat} := h'
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
"""
    for t, (i, j) in enumerate(PAIRS):
        L_, U_, Q_ = f"({ssum('l', i, j)})", f"({ssum('u', i, j)})", f"({ssum('q', i, j)})"
        hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
        out += (f"  obtain ⟨d{t}, hdl{t}, hdu{t}, hb{t}⟩ := mterm_bound hlb hD hpt {vbit(t)} {bit(t)} {L_} {U_} {Q_} (by omega) (by omega) c{t} hok{t}\n"
                f"    ({term_g(i, j)}) (by push_cast; (try simp only [add_div]); linarith [{hl}]) (by push_cast; (try simp only [add_div]); linarith [{hu}])\n"
                f"  push_cast at hb{t}\n")
    out += f"  rw [hSCe] at {HV}\n"
    for r in range(Q):
        out += (f"  have hl{r} : (l{r} : ℝ) ≤ q{r} := by exact_mod_cast hq{r}1\n"
                f"  have hu{r} : (q{r} : ℝ) ≤ u{r} := by exact_mod_cast hq{r}2\n")
    for r in range(Q):
        Er = f"(({bN[r]} : ℝ) + {' + '.join(f'{aN[t]} * d{t}' for t in TS[r])})"
        Kx = " + ".join([str(U1 * bN[r])] + [f"{aN[t]} * tK {bit(t)}" for t in TS[r]])
        Mx = " + ".join(f"{aN[t]} * tM {bit(t)} (selXf {bit(t)} top bk pb ({ssum('l', *PAIRS[t])}) ({ssum('u', *PAIRS[t])}) ({ssum('q', *PAIRS[t])}))" for t in TS[r])
        Kn = " + ".join(f"{aN[t]} * tK {bit(t)}" for t in TS[r])
        Px = " + ".join([str(U1 * bN[r])] + [f"{aN[t]} * tP {bit(t)} (selXf {bit(t)} top bk pb ({ssum('l', *PAIRS[t])}) ({ssum('u', *PAIRS[t])}) ({ssum('q', *PAIRS[t])}))" for t in TS[r]])
        out += f"""  have hP{r} : (1000000000 : ℝ) * {Er} ≤ ((({Kx}) - ({Mx}) : ℕ) : ℝ) := by
    have := natsub_ge ({Kx}) ({Mx})
    push_cast at this
    linarith [{', '.join(f'hdu{t}' for t in TS[r])}]
  have hN{r} : -((1000000000 : ℝ) * {Er}) ≤ ((({Kn}) - ({Px}) : ℕ) : ℝ) := by
    have := natsub_ge ({Kn}) ({Px})
    push_cast at this
    linarith [{', '.join(f'hdl{t}' for t in TS[r])}]
  have hml{r} : ((q{r} - l{r} : ℕ) : ℝ) = (q{r} : ℝ) - l{r} := Nat.cast_sub hq{r}1
  have hum{r} : ((u{r} - q{r} : ℕ) : ℝ) = (u{r} : ℝ) - q{r} := Nat.cast_sub hq{r}2
  have ht{r} := mterm (e := g{r} - (q{r} : ℝ) / 32768) (E := {Er}) (lo := ((q{r} - l{r} : ℕ) : ℝ) / 32768)
    (hi := ((u{r} - q{r} : ℕ) : ℝ) / 32768) (by rw [hml{r}]; linarith [h{r}1]) (by rw [hum{r}]; linarith [h{r}2])
    (by positivity) (by positivity) hP{r} hN{r} (natsub_nonneg _ _) (natsub_nonneg _ _)
"""
    out += f"""  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  try simp only [{', '.join(f'hml{r}, hum{r}' for r in range(Q))}] at hq
  simp only [{', '.join(f'hml{r}, hum{r}' for r in range(Q))}] at {' '.join(f'ht{r}' for r in range(Q))}
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ({' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
      + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))}) * SA
      = {' + '.join(f'{bN[r]} * {V[r]}' for r in range(Q))} + {' + '.join(f'{aN[t]} * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))} := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = {cN} := by norm_num [cN]
  rw [hcN]
  linarith [hq, {', '.join(f'ht{r}' for r in range(Q))}, {', '.join(f'mul_le_mul_of_nonneg_left hb{t} (by norm_num : (0:ℝ) ≤ {aN[t]})' for t in range(NP))}]

theorem covered_of_ctest {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) ({COORDS} : ℕ)
    ({QV} : ℕ) (T V : ℕ) ({CV} : List ℕ) (h : ctest top bk tD bD pb {COORDS} {QV} T V {CV} = true) : Covered {COORDS} := by
  intro {' '.join(V)} {HV}
  exact Or.inl (ctest_sound hlb hD hpt {COORDS} {QV} T V {CV} h {' '.join(V)} {HV})
"""
    return out
