# (AM copy of bench/eight/gen8mz.py, mvt-engine, by port8.py; unchanged)
"""The minorant leaf of the (Q+1)-point instance (text for gen7n.checker): every pair term with a nonzero weight is
bounded on its range by its own certified minorant (the zero-order constant, the tangent at a grid point, or a convex
combination of two of these, weights out of 1024), decoded from the walk word; `mscheck` / `mleafN`, `mleafN_sound`.

Per term t (in pair order, zero-weight terms skipped) the word holds: kind (2 bits; 0 constant, 1 tangent, 2 constant
and tangent, 3 two tangents), then j1 (4 bits) for kinds 1-3, then j2 (4 bits) for kind 3, then the weight (10 bits) for
kinds 2-3; the grid point of j is `gptG L U j` (grid `2^GSH`, env GSH, default 8)."""
import os
GS = int(os.environ.get("GSH", "8")); GM = (1 << GS) - 1
TWOGRID = os.environ.get("TWOGRID") == "1"
# payload field offsets after the 2-bit kind: (j bits, j2 offset, weight offset for kind 2, for kind 3, lengths 1..3)
JB, OJ2, OL2, OL3, ML = (5, 7, 7, 12, (7, 17, 22)) if TWOGRID else (4, 6, 6, 10, (6, 16, 20))
GPT = "gptF" if TWOGRID else "gptG"
from gen7n import Q, PAIRS, NP, TS, SC, U, U1, KU1, RU, COORDS, V, mem, HV, ssum, nsum, nadd, term_g

def rng_lo(i, j):
    e = f"h{i}1"
    for r in range(i + 1, j): e = f"(slo_add {e} h{r}1)"
    return e
def rng_hi(i, j):
    e = f"h{i}2"
    for r in range(i + 1, j): e = f"(shi_add {e} h{r}2)"
    return e

def mparts(NAME, aN, bN, cN):
    C = cN * SC * U
    ACT = [t for t in range(NP) if aN[t] > 0]
    TV = " ".join(f"(k{t} m{t} p{t} r{t} : ℕ)" for t in ACT)
    TA = " ".join(f"k{t} m{t} p{t} r{t}" for t in ACT)
    def LU(t): i, j = PAIRS[t]; return nsum('l', i, j), nsum('u', i, j)
    conds = [f"Nat.ble l{r} u{r}" for r in range(Q)]
    for t in ACT:
        L, Uu = LU(t)
        conds.append(f"Nat.ble m{t} 1024")
        conds.append(f"mok R tD bD f {L} {Uu} (mw1 k{t} m{t}) (mw2 k{t} m{t}) p{t} r{t}")
    cexpr = conds[0]
    for c_ in conds[1:]: cexpr = f"({cexpr} && {c_})"
    def W(t): return f"(mwc k{t} m{t}) (mw1 k{t} m{t}) (mw2 k{t} m{t})"
    vals = nadd([f"(Nat.mul {aN[t]} (mval top bk f {LU(t)[0]} {LU(t)[1]} {W(t)} p{t} r{t}))" for t in ACT])
    cps = nadd([f"(Nat.mul {aN[t]} (mcp f {LU(t)[0]} (mw1 k{t} m{t}) (mw2 k{t} m{t}) p{t} r{t}))" for t in ACT])
    cns = nadd([f"(Nat.mul {aN[t]} (mcn f {LU(t)[0]} (mw1 k{t} m{t}) (mw2 k{t} m{t}) p{t} r{t}))" for t in ACT])
    lin = nadd([f"(Nat.mul {bN[r]} l{r})" for r in range(Q)])
    negs = []
    for r in range(Q):
        tr = [t for t in TS[r] if aN[t] > 0]
        SK = nadd([f"(Nat.mul {aN[t]} (Nat.add (mw1 k{t} m{t}) (mw2 k{t} m{t})))" for t in tr])
        SL = nadd([str(1024 * U1 * bN[r])] + [f"(Nat.mul {aN[t]} (msl f (mw1 k{t} m{t}) (mw2 k{t} m{t}) p{t} r{t}))" for t in tr])
        negs.append(f"(Nat.mul (Nat.sub u{r} l{r}) (Nat.sub (Nat.mul {KU1} {SK}) {SL}))")
    lhs = f"(Nat.add (Nat.add (Nat.mul {1024 * U} {lin}) (Nat.mul {SC} {vals})) (Nat.mul {RU} {cps}))"
    rhs = f"(Nat.add {1024 * C} (Nat.mul {RU} (Nat.add {cns} {nadd(negs)})))"
    MCHECK = f"{cexpr} && Nat.ble {rhs} {lhs}"
    # decoding: offsets o0 = 0, fields per kind
    DEC = []
    for idx, t in enumerate(ACT):
        L, Uu = LU(t); o = f"o{idx}"
        DEC.append(f"forceR (Nat.land (Nat.shiftRight w {o}) 3) fun k{t} =>")
        DEC.append(f"forceR (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w (Nat.add {o} {OL3})) 1023) "
                   f"(Nat.land (Nat.shiftRight w (Nat.add {o} {OL2})) 1023) (Nat.beq k{t} 2)) fun m{t} =>")
        DEC.append(f"forceR ({GPT} {L} {Uu} (Nat.land (Nat.shiftRight w (Nat.add {o} 2)) {(1 << JB) - 1})) fun p{t} =>")
        DEC.append(f"forceR ({GPT} {L} {Uu} (Nat.land (Nat.shiftRight w (Nat.add {o} {OJ2})) {(1 << JB) - 1})) fun r{t} =>")
        DEC.append(f"forceR (Nat.add {o} (mlen k{t})) fun o{idx + 1} =>")
    MLEAF = "forceR 0 fun o0 =>\n  " + "\n  ".join(DEC) + f"\n  Bool.rec (motive := fun _ => ℕ) 0 o{len(ACT)} (mscheck top bk tD bD (pt3 pb) R {COORDS} {TA})"
    flat = [f"hlu{r}" for r in range(Q)]
    for t in ACT: flat += [f"hm{t}", f"hok{t}"]
    pat = flat[0]
    for c_ in flat[1:]: pat = f"⟨{pat}, {c_}⟩"
    pat = f"⟨{pat}, hmain⟩"
    return dict(ACT=ACT, TV=TV, TA=TA, MCHECK=MCHECK, MLEAF=MLEAF, pat=pat, LU=LU, C=C)

def mleaf_defs(NAME, aN, bN, cN):
    p = mparts(NAME, aN, bN, cN)
    return f"""
/-- the grid point `j ∈ [0, 8]` of the range `[L, U]`: `L + (U − L) j / 8` rounded down to a multiple of `2^{GS}`, clamped
to the multiples of `2^{GS}` inside `[L, U]` -/
def gptG (L U j : ℕ) : ℕ :=
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L {GM}) {GS}) {GS}) fun ga =>
  forceR (Nat.shiftLeft (Nat.shiftRight U {GS}) {GS}) fun gb =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) j) 3)) {GS}) {GS}) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga)

/-- the grid point of the 5-bit field `jj`: `gptG` with `j = jj mod 16` on the grid of multiples of `2^{GS}` when bit 4 is
set, else of `2^8` -/
def gptF (L U jj : ℕ) : ℕ :=
  forceR (Bool.rec (motive := fun _ => ℕ) 8 {GS} (Nat.beq (Nat.shiftRight jj 4) 1)) fun s =>
  forceR (Nat.land jj 15) fun j =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.sub (Nat.shiftLeft 1 s) 1)) s) s) fun ga =>
  forceR (Nat.shiftLeft (Nat.shiftRight U s) s) fun gb =>
  forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) j) 3)) s) s) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga)

/-- the minorant inequality of a box, given per term its kind `k`, weight `m` and grid points `p`, `r`:
`1024 cN SC U + RU (Σ a mcn + Σ_r (u − l) N_r) ≤ 1024 U Σ b l + SC Σ a mval + RU Σ a mcp` -/
def mscheck (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) ({COORDS} : ℕ) {p['TV']} : Bool :=
  {p['MCHECK']}

/-- the payload length of a minorant term of kind `k` -/
def mlen (k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 {ML[2]} (Nat.beq k 3)) {ML[1]} (Nat.beq k 2)) {ML[0]} (Nat.beq k 1)

/-- a minorant leaf: the payload length when the check passes, else `0` -/
def mleafN (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) ({COORDS} : ℕ) : ℕ :=
  {p['MLEAF']}

"""

def mleaf_proofs(NAME, aN, bN, cN):
    p = mparts(NAME, aN, bN, cN); ACT = p['ACT']; LU = p['LU']
    KM = 327680000000000 * 1024
    IMPL = "{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}"
    out = f"""
set_option maxHeartbeats 40000000 in
theorem mscheck_sound {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true)
    ({COORDS} : ℕ) {p['TV']} (h : mscheck top bk tD bD f R {COORDS} {p['TA']} = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {HV}
  unfold mscheck at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain {p['pat']} := h
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
"""
    for t in ACT:
        i, j = PAIRS[t]; L_, U_ = f"({ssum('l', i, j)})", f"({ssum('u', i, j)})"
        hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
        out += (f"  obtain ⟨D{t}, hDl{t}, hb{t}⟩ := mterm_ok hlb hD hpt hR {L_} {U_} k{t} m{t} p{t} r{t} hm{t} hok{t}\n"
                f"    ({term_g(i, j)}) {rng_lo(i, j)} {rng_hi(i, j)}\n"
                f"  push_cast at hb{t}\n")
    out += f"  rw [hSCe] at {HV}\n"
    for r in range(Q):
        tr = [t for t in TS[r] if aN[t] > 0]
        Er = f"((1024 * {bN[r]} : ℝ) + {' + '.join(f'{aN[t]} * D{t}' for t in tr)})"
        SK = " + ".join(f"{aN[t]} * (mw1 k{t} m{t} + mw2 k{t} m{t})" for t in tr)
        SL = " + ".join([str(1024 * U1 * bN[r])] + [f"{aN[t]} * msl f (mw1 k{t} m{t}) (mw2 k{t} m{t}) p{t} r{t}" for t in tr])
        out += f"""  have hN{r} : -(((({KU1} * ({SK})) - ({SL}) : ℕ) : ℝ)) ≤ 1000000000 * {Er} := by
    have := natsub_ge ({KU1} * ({SK})) ({SL})
    push_cast at this ⊢
    linear_combination this + {' + '.join(f'{aN[t]} * hDl{t}' for t in tr)}
  have hlu{r}' : ((u{r} - l{r} : ℕ) : ℝ) = (u{r} : ℝ) - l{r} := Nat.cast_sub hlu{r}
  have hg{r} := gap_lo (E := {Er}) (e := g{r} - (l{r} : ℝ) / 32768) (H := ((u{r} - l{r} : ℕ) : ℝ))
    (natsub_nonneg _ _) hN{r} (sub_nonneg.mpr h{r}1) (by rw [hlu{r}', sub_div]; exact sub_le_sub_right h{r}2 _)
"""
    out += f"""  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  simp only [{', '.join(f"hlu{r}'" for r in range(Q))}] at hq {' '.join(f'hg{r}' for r in range(Q))}
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ({' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
      + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS))}) * SA
      = {' + '.join(f'{bN[r]} * {V[r]}' for r in range(Q))} + {' + '.join(f'{aN[t]} * wfun ({term_g(i, j)})' for t, (i, j) in enumerate(PAIRS) if aN[t] > 0)} := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = {cN} := by norm_num [cN]
  rw [hcN]
  linarith [hq, {', '.join(f'hg{r}' for r in range(Q))}, {', '.join(f'mul_le_mul_of_nonneg_left hb{t} (by norm_num : (0:ℝ) ≤ {aN[t]})' for t in ACT)}]

theorem mleafN_sound {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w {COORDS} : ℕ)
    (h : mleafN top bk tD bD pb R w {COORDS} ≠ 0) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  unfold mleafN at h
  simp only [forceR_eq] at h
  exact mscheck_sound (f := pt3 pb) hlb hD hpt hR {' '.join(['_'] * (2 * Q + 4 * len(ACT)))} (brec_ne h)
"""
    return out
