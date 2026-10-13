#!/usr/bin/env python3
"""Instance checker for a weighted six-point certificate with the two leaf tests (zero-order pyramid test and the
mean-value test): definitions from gen_inst.inst_defs, then the proofs (leaf soundness of both tests, the walk with
the per-leaf flag).  The per-gap cover and `of_check` follow (cover_text).
Usage (module): checker(NAME, SA, aN, bN, cN, ORDER) -> str"""
import gen_inst
from gen_inst import Q, PAIRS, SC, U, U1, KU1, RU, CO, COORDS, V, TS, nsum, nadd

def rsum(xs): return " + ".join(xs)
def term_g(i, j): return rsum(V[i:j])
mem = " → ".join(f"(l{r} : ℝ) / SC ≤ g{r} → g{r} ≤ (u{r} : ℝ) / SC" for r in range(Q))
HV = " ".join(f"h{r}1 h{r}2" for r in range(Q))
TBLB = "{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ}"
HYPS = "(hlb : LBSound top bk) (hD : LBSound2 tD bD) (hpt : PTSound pb)"
HARGS = "hlb hD hpt"
TARGS = "top bk tD bD pb"

def args_with(ax, which, val):
    cs = COORDS.split(); cs[2 * ax + (1 if which == "u" else 0)] = val; return " ".join(cs)

def checker(NAME, SA, aN, bN, cN, ORDER):
    C = cN * SC * U
    AR = [sum(aN[t] for t in TS[r]) for r in range(Q)]
    full_nat = f"{U} * ({rsum([f'{bN[r]} * l{r}' for r in range(Q)])}) + {SC} * ({rsum([f'{aN[t]} * lb top bk ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])})' for t, (i, j) in enumerate(PAIRS)])})"
    out = gen_inst.inst_defs(NAME, SA, aN, bN, cN, ORDER)
    out += f"""
/-- the box `[l_r, u_r] / SC` satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered ({COORDS} : ℕ) : Prop :=
  ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} ∨ g{Q-1} < g0

theorem ee_or {{C s : ℕ}} {{rest : Bool}} (h : ee C s rest = true) : C ≤ s ∨ rest = true := by
  unfold ee at h
  cases hc : Nat.ble C s
  · rw [hc] at h; exact Or.inr h
  · exact Or.inl (by rw [← Nat.ble_eq, hc])

theorem leafOK_le (top : ℕ) (bk : ℕ → ℕ) ({COORDS} : ℕ) (h : leafOK top bk {COORDS} = true) :
    {C} ≤ {full_nat} := by
  unfold leafOK at h
  dsimp only at h
{chr(10).join("  rcases ee_or h with h | h" + chr(10) + "  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega" for _ in range(len(PAIRS)))}
  simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega

set_option maxHeartbeats 4000000 in
theorem leaf_sound {{top : ℕ}} {{bk : ℕ → ℕ}} (hlb : LBSound top bk) ({COORDS} : ℕ) (h : leafOK top bk {COORDS} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {HV}
  have hq0 := leafOK_le top bk {COORDS} h
"""
    for t, (i, j) in enumerate(PAIRS):
        hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
        out += (f"  have w{t} := hlb ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])}) ({term_g(i, j)}) "
                f"(by push_cast; (try simp only [add_div]); linarith [{hl}]) (by push_cast; (try simp only [add_div]); linarith [{hu}])\n")
    out += f"""  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hU : (0:ℝ) < 10000000000 := by norm_num
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := {' + '.join(f'{bN[r]} * ((l{r} : ℝ) / SC)' for r in range(Q))} with hL
  set Wt : ℝ := {' + '.join(f"{aN[t]} * ((lb top bk ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])}) : ℝ) / 10000000000)" for t, (i, j) in enumerate(PAIRS))} with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * ({' + '.join(f'{bN[r]} * (l{r} : ℝ)' for r in range(Q))}) + {SC} * ({' + '.join(f"{aN[t]} * (lb top bk ({rsum([f'l{r}' for r in range(i, j)])}) ({rsum([f'u{r}' for r in range(i, j)])}) : ℝ)" for t, (i, j) in enumerate(PAIRS))}) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = {C} := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ({' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
      + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))}) * SA
      = {' + '.join(f'{bN[r]} * {V[r]}' for r in range(Q))} + {' + '.join(f'{aN[t]} * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))} := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', {', '.join(f'mul_le_mul_of_nonneg_left h{r}1 (by positivity : (0:ℝ) ≤ {bN[r]})' for r in range(Q))}, {', '.join(f'mul_le_mul_of_nonneg_left w{t} (by positivity : (0:ℝ) ≤ {aN[t]})' for t in range(len(PAIRS)))}]
"""
    # ---------------- mean-value leaf ----------------
    flat = []
    for r in range(Q): flat += [f"hm{r}1", f"hm{r}2"]
    for t in range(len(PAIRS)): flat += [f"hp{t}", f"hq{t}"]
    pat = flat[0]
    for c in flat[1:]: pat = f"⟨{pat}, {c}⟩"
    pat = f"⟨{pat}, hmain⟩"
    def lsum(i, j): return " + ".join(f"l{r}" for r in range(i, j))
    def usum(i, j): return " + ".join(f"u{r}" for r in range(i, j))
    def msum(i, j): return " + ".join(f"m{r}" for r in range(i, j))
    def ysum(i, j): return " + ".join(f"(m{r} : ℝ) / 32768" for r in range(i, j))
    LBARGS = " ".join(f"(lo32 (lb2 tD bD ({lsum(i, j)}) ({usum(i, j)}))) (hi32 (lb2 tD bD ({lsum(i, j)}) ({usum(i, j)})))" for (i, j) in PAIRS)
    def PexprR(r): return f"({U1 * bN[r] + KU1 * AR[r]} - ({' + '.join(f'{aN[t]} * hi32 (lb2 tD bD ({lsum(*PAIRS[t])}) ({usum(*PAIRS[t])}))' for t in TS[r])}))"
    def NexprR(r): return f"({KU1 * AR[r]} - ({U1 * bN[r]} + {' + '.join(f'{aN[t]} * lo32 (lb2 tD bD ({lsum(*PAIRS[t])}) ({usum(*PAIRS[t])}))' for t in TS[r])}))"
    LBARGS += " " + " ".join(f"{PexprR(r)} {NexprR(r)}" for r in range(Q))
    out += f"""
theorem mleafOK_spec {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} ({COORDS} : ℕ)
    (h : mleafOK tD bD pb {COORDS} = true) :
    ∃ {' '.join(f'm{r}' for r in range(Q))} : ℕ, mcore pb {COORDS} {' '.join(f'm{r}' for r in range(Q))}
      {LBARGS} = true := by
  unfold mleafOK at h
  simp only [forceB_eq] at h
  exact ⟨{', '.join('_' for _ in range(Q))}, h⟩

set_option maxHeartbeats 16000000 in
theorem mleaf_sound {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} (hD : LBSound2 tD bD) (hpt : PTSound pb) ({COORDS} : ℕ)
    (h : mleafOK tD bD pb {COORDS} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {HV}
  obtain ⟨{', '.join(f'm{r}' for r in range(Q))}, h⟩ := mleafOK_spec {COORDS} h
  unfold mcore at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain {pat} := h
"""
    out += "  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]\n"
    out += f"  rw [hSCe] at {HV}\n"
    for r in range(Q):
        out += (f"  have hl{r} : (l{r} : ℝ) ≤ m{r} := by exact_mod_cast hm{r}1\n"
                f"  have hu{r} : (m{r} : ℝ) ≤ u{r} := by exact_mod_cast hm{r}2\n")
    for t, (i, j) in enumerate(PAIRS):
        def bnd(hs): return f"(by push_cast; rw [hSCe]; (try simp only [add_div]); linarith [{', '.join(hs)}])"
        hy1 = bnd([f'hl{r}' for r in range(i, j)] + [f'hm{r}1' for r in range(0)])
        hy2 = bnd([f'hu{r}' for r in range(i, j)])
        hz1 = bnd([f'h{r}1' for r in range(i, j)])
        hz2 = bnd([f'h{r}2' for r in range(i, j)])
        out += (f"  obtain ⟨d{t}, hd{t}, hdl{t}, hdu{t}⟩ := mvt_pair hD ({lsum(i, j)}) ({usum(i, j)}) hp{t} hq{t}\n"
                f"    ({ysum(i, j)}) ({term_g(i, j)})\n    {hy1}\n    {hy2}\n    {hz1}\n    {hz2}\n")
        out += (f"  have hv{t} := hpt ({msum(i, j)})\n"
                f"  rw [show ((({msum(i, j)} : ℕ) : ℝ) / SC) = {ysum(i, j)} by push_cast; rw [hSCe]; (try ring)] at hv{t}\n")
    for r in range(Q):
        Er = f"(({bN[r]} : ℝ) + {' + '.join(f'{aN[t]} * d{t}' for t in TS[r])})"
        Pnum = U1 * bN[r] + KU1 * AR[r]
        Psub = " + ".join(f"{aN[t]} * hi32 (lb2 tD bD ({lsum(*PAIRS[t])}) ({usum(*PAIRS[t])}))" for t in TS[r])
        Nsub = f"{U1 * bN[r]} + " + " + ".join(f"{aN[t]} * lo32 (lb2 tD bD ({lsum(*PAIRS[t])}) ({usum(*PAIRS[t])}))" for t in TS[r])
        out += f"""  have hP{r} : (1000000000 : ℝ) * {Er} ≤ (({Pnum} - ({Psub}) : ℕ) : ℝ) := by
    have := natsub_ge {Pnum} ({Psub})
    push_cast at this
    linarith [{', '.join(f'hdu{t}' for t in TS[r])}]
  have hN{r} : -((1000000000 : ℝ) * {Er}) ≤ (({KU1 * AR[r]} - ({Nsub}) : ℕ) : ℝ) := by
    have := natsub_ge {KU1 * AR[r]} ({Nsub})
    push_cast at this
    linarith [{', '.join(f'hdl{t}' for t in TS[r])}]
  have hml{r} : ((m{r} - l{r} : ℕ) : ℝ) = (m{r} : ℝ) - l{r} := Nat.cast_sub hm{r}1
  have hum{r} : ((u{r} - m{r} : ℕ) : ℝ) = (u{r} : ℝ) - m{r} := Nat.cast_sub hm{r}2
  have ht{r} := mterm (e := g{r} - (m{r} : ℝ) / 32768) (E := {Er}) (lo := ((m{r} - l{r} : ℕ) : ℝ) / 32768)
    (hi := ((u{r} - m{r} : ℕ) : ℝ) / 32768) (by rw [hml{r}]; linarith [h{r}1]) (by rw [hum{r}]; linarith [h{r}2])
    (by positivity) (by positivity) hP{r} hN{r} (natsub_nonneg _ _) (natsub_nonneg _ _)
"""
    out += f"""  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  try simp only [hml0, hml1, hml2, hml3, hml4, hum0, hum1, hum2, hum3, hum4] at hq
  simp only [hml0, hml1, hml2, hml3, hml4, hum0, hum1, hum2, hum3, hum4] at ht0 ht1 ht2 ht3 ht4
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ({' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
      + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))}) * SA
      = {' + '.join(f'{bN[r]} * {V[r]}' for r in range(Q))} + {' + '.join(f'{aN[t]} * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))} := by
    field_simp; try ring
  rw [eG, {', '.join(f'hd{t}' for t in range(len(PAIRS)))}]
  have hcN : ((cN : ℕ) : ℝ) = {cN} := by norm_num [cN]
  rw [hcN]
  linarith [hq, {', '.join(f'ht{r}' for r in range(Q))}, {', '.join(f'mul_le_mul_of_nonneg_left hv{t} (by norm_num : (0:ℝ) ≤ {aN[t]})' for t in range(len(PAIRS)))}]
"""
    for ax in range(Q):
        out += f"""
/-- a box split on gap {ax} at `q` is covered when both halves are -/
theorem covered_split{ax} {{{COORDS} : ℕ}} (q : ℕ) (hA : Covered {args_with(ax, 'u', 'q')}) (hB : Covered {args_with(ax, 'l', 'q')}) :
    Covered {COORDS} := by
  intro {' '.join(V)} {HV}
  rcases le_total g{ax} ((q : ℝ) / SC) with hq | hq
  · exact hA {' '.join(V)} {' '.join(f'h{r}1 ' + ('hq' if r == ax else f'h{r}2') for r in range(Q))}
  · exact hB {' '.join(V)} {' '.join(('hq ' if r == ax else f'h{r}1 ') + f'h{r}2' for r in range(Q))}
"""
    out += f"""
/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos {COORDS} : ℕ, f pos {COORDS} ≠ 0 → Covered {COORDS}
"""
    for ax in range(Q):
        q = f"(Nat.shiftRight (Nat.add l{ax} u{ax}) 1)"
        out += f"""
theorem split{ax}_sound {{ih : WF}} (hih : WalkOK ih) (pos {COORDS} : ℕ) (h : split{ax} ih pos {COORDS} ≠ 0) :
    Covered {COORDS} := by
  unfold split{ax} at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) {args_with(ax, 'u', q)}) 0
  · have h' : ih (ih (Nat.add pos 4) {args_with(ax, 'u', q)}) {args_with(ax, 'l', q)} ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) {args_with(ax, 'u', q)} (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split{ax} _ hA (hih _ {args_with(ax, 'l', q)} h')
  · exact absurd (by simp only [hp]) h
"""
    out += f"""
theorem splitAx_sound {{ih : WF}} (hih : WalkOK ih) (pos ax {COORDS} : ℕ) (h : splitAx ih pos ax {COORDS} ≠ 0) :
    Covered {COORDS} := by
  unfold splitAx at h
"""
    def ax_proof(ax, ind):
        if ax == Q - 1:
            return [f"{ind}exact split{Q-1}_sound hih pos {COORDS} h"]
        o = [f"{ind}cases ha{ax} : Nat.beq ax {ax}", f"{ind}· rw [ha{ax}] at h"]
        o += ax_proof(ax + 1, ind + "  ")
        o += [f"{ind}· rw [ha{ax}] at h; exact split{ax}_sound hih pos {COORDS} h"]
        return o
    out += "\n".join(ax_proof(0, "  ")) + "\n"
    out += f"""
theorem leafStep_sound {TBLB} {HYPS} (pos fl {COORDS} : ℕ) (h : leafStep {TARGS} pos fl {COORDS} ≠ 0) :
    Covered {COORDS} := by
  unfold leafStep at h
  intro {' '.join(V)} {HV}
  cases hs : Nat.ble (Nat.add u{Q-1} 1) l0
  · rw [hs] at h
    cases hf : Nat.beq fl 1
    · rw [hf] at h
      cases hl : leafOK top bk {COORDS}
      · rw [hl] at h; exact absurd rfl h
      · exact Or.inl (leaf_sound hlb {COORDS} hl {' '.join(V)} {HV})
    · rw [hf] at h
      cases hl : mleafOK tD bD pb {COORDS}
      · rw [hl] at h; exact absurd rfl h
      · exact Or.inl (mleaf_sound hD hpt {COORDS} hl {' '.join(V)} {HV})
  · right
    have hsk : u{Q-1} < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u{Q-1} : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {TBLB} {HYPS} (bits : ℕ) : ∀ fuel, WalkOK (walk {TARGS} bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos {COORDS} h; exact absurd rfl h
  | succ fuel ih =>
    intro pos {COORDS} h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep {TARGS} pos (Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) {COORDS})
        (splitAx (walk {TARGS} bits fuel) pos (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) {COORDS})
        (Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1
    · rw [hb] at h'; exact leafStep_sound {HARGS} pos _ {COORDS} h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ {COORDS} h'

theorem covered_of_walk {TBLB} {HYPS} (bits fuel {COORDS} e : ℕ)
    (h : walk {TARGS} bits fuel 1 {COORDS} = e) (he : e ≠ 0) : Covered {COORDS} :=
  walk_sound {HARGS} bits fuel 1 {COORDS} (h ▸ he)
"""
    return out
