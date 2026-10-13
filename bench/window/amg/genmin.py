#!/usr/bin/env python3
"""(bridge-port) The minorant slope test for a seven-point instance, emitted against the instance's existing `cscheck`
(gen7cnam.py): a generic `cscheck_sound` (the slope inequality from per-term bounds, for any reads), the minorant
test `ctestM` (AMW/MinMode.lean: per expanded term a combination of the constant and extended tangents at grid
points, from a variable-length data stream E), `sleafM` and their soundness.

Leaf word of `sleafM` (the kind field is the walk's, not read here): bits 3..14 the six 2-bit `dec` modes, bit 15 the
all-expanded flag, then the 21-bit expansion set T unless the flag is set, then the data stream E: per expanded term in
order, its kind field c (2 bits; κ = c + 1), j₁ (4 bits), then λ (10 bits) if κ ≥ 2, then j₂ (4 bits) if κ = 3.
Usage: genmin.py PARAMS OUT.lean      (PARAMS: the instance's *_params.txt)"""
import sys
from gen7am import Q, PAIRS, NP, TS, SC, U, U1, COORDS, QV, V, mem, HV, ssum, nsum, bit, term_g


def gen(NAME, SA, aN, bN, cN):
    IMPL = "{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}"
    XV = " ".join(f"x{t} eu{t} ed{t} v{t}" for t in range(NP))
    XT = " ".join(f"{{x{t} eu{t} ed{t} : ℕ}} {{v{t} : Bool}}" for t in range(NP))
    flat = []
    for r in range(Q): flat += [f"hq{r}1", f"hq{r}2"]
    for t in range(NP): flat.append(f"hok{t}")
    pat = flat[0]
    for c in flat[1:]: pat = f"⟨{pat}, {c}⟩"
    pat = f"⟨{pat}, hmain⟩"

    def rng(t):
        i, j = PAIRS[t]
        return f"({ssum('l', i, j)})", f"({ssum('u', i, j)})", f"({ssum('q', i, j)})"

    HYP = []
    for t in range(NP):
        L_, U_, Q_ = rng(t)
        HYP.append(
            f"    (H{t} : rtok v{t} {bit(t)} {L_} {U_} {Q_} x{t} eu{t} ed{t} = true → ∀ s : ℝ, (({L_} : ℕ) : ℝ) / SC ≤ s → "
            f"s ≤ (({U_} : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP {bit(t)} x{t} : ℝ) - (tK {bit(t)} : ℝ) ≤ 1000000000 * d ∧ "
            f"1000000000 * d ≤ (tK {bit(t)} : ℝ) - (tM {bit(t)} x{t} : ℝ) ∧ "
            f"32768 * (tval {bit(t)} x{t} : ℝ) + 327680000000000 * (d * (s - (({Q_} : ℕ) : ℝ) / 32768)) "
            f"- 10 * (mchg v{t} {bit(t)} {L_} {U_} {Q_} x{t} eu{t} ed{t} : ℝ) ≤ 327680000000000 * wfun s)")
    out = f"""import AMW.AMS02Inst
import AMW.MinMode

/-! ###### `{NAME}` with minorant terms: the slope inequality `cscheck` from per-term bounds for any reads
(`cscheck_sound`), and the minorant slope test `ctestM` / leaf `sleafM` (per expanded pair term a convex combination
of the constant and extended tangents at grid points, AMW/MinMode.lean), emitted by genmin.py (bridge-port). ###### -/

noncomputable section

namespace AMW.Cert.{NAME}

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

set_option maxHeartbeats 40000000 in
/-- **the slope inequality from per-term bounds**: any reads whose terms each satisfy the per-term inequality of the
slope test give the certificate inequality on the box -/
theorem cscheck_sound ({COORDS} : ℕ) ({QV} : ℕ) (T : ℕ) {XT}
    (h : cscheck {COORDS} {QV} T {XV} = true)
{chr(10).join(HYP)} :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {HV}
  have h' := h
  unfold cscheck at h'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h'
  obtain {pat} := h'
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
"""
    for t, (i, j) in enumerate(PAIRS):
        hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
        out += (f"  obtain ⟨d{t}, hdl{t}, hdu{t}, hb{t}⟩ := H{t} hok{t}\n"
                f"    ({term_g(i, j)}) (by push_cast; (try simp only [add_div]); linarith [{hl}]) (by push_cast; (try simp only [add_div]); linarith [{hu}])\n"
                f"  push_cast at hb{t}\n")
    out += f"  rw [hSCe] at {HV}\n"
    for r in range(Q):
        out += (f"  have hl{r} : (l{r} : ℝ) ≤ q{r} := by exact_mod_cast hq{r}1\n"
                f"  have hu{r} : (q{r} : ℝ) ≤ u{r} := by exact_mod_cast hq{r}2\n")
    for r in range(Q):
        Er = f"(({bN[r]} : ℝ) + {' + '.join(f'{aN[t]} * d{t}' for t in TS[r])})"
        Kx = " + ".join([str(U1 * bN[r])] + [f"{aN[t]} * tK {bit(t)}" for t in TS[r]])
        Mx = " + ".join(f"{aN[t]} * tM {bit(t)} x{t}" for t in TS[r])
        Kn = " + ".join(f"{aN[t]} * tK {bit(t)}" for t in TS[r])
        Px = " + ".join([str(U1 * bN[r])] + [f"{aN[t]} * tP {bit(t)} x{t}" for t in TS[r]])
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

"""
    ST = ["forceB E fun e0 =>"]
    for t, (i, j) in enumerate(PAIRS):
        L, Uu, QS = nsum('l', i, j), nsum('u', i, j), nsum('q', i, j)
        ST.append(f"bforce {bit(t)} fun v{t} =>")
        ST.append(f"forceB (lmMX v{t} e{t} top bk pb tD bD R {L} {Uu} {QS}) fun x{t} =>")
        if t + 1 < NP:
            ST.append(f"forceB (mNext v{t} e{t}) fun e{t + 1} =>")
    XV0 = " ".join(f"x{t} 0 0 v{t}" for t in range(NP))
    CTEST = "\n  ".join(ST) + f"\n  cscheck {COORDS} {QV} T {XV0}"
    HS = " ".join("(fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2)" for _ in range(NP))
    SLEAF = "\n  ".join(f"forceB (dec (Nat.land (Nat.shiftRight w {3 + 2 * r}) 3) l{r} u{r}) fun q{r} =>" for r in range(Q))
    out += f"""/-- the minorant slope test at the point `q` with expansion set `T` and term data `E` -/
def ctestM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) ({COORDS} : ℕ) ({QV} : ℕ) (T E : ℕ) : Bool :=
  {CTEST}

theorem ctestM_sound {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    ({COORDS} : ℕ) ({QV} : ℕ) (T E : ℕ) (h : ctestM top bk tD bD pb R {COORDS} {QV} T E = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  unfold ctestM at h
  simp only [forceB_eq, bforce_eq] at h
  exact cscheck_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h {HS}

theorem covered_of_ctestM {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    ({COORDS} : ℕ) ({QV} : ℕ) (T E : ℕ) (h : ctestM top bk tD bD pb R {COORDS} {QV} T E = true) : Covered {COORDS} := by
  intro {' '.join(V)} {HV}
  exact Or.inl (ctestM_sound hlb hD hpt hR {COORDS} {QV} T E h {' '.join(V)} {HV})

/-- a minorant leaf: `dec` modes (bits 3..14), the all-expanded flag (bit 15) or the expansion set (bits 16..36),
then the term data `E` (from bit 16 when the flag is set, else from bit 37) -/
def sleafM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) ({COORDS} : ℕ) : Bool :=
  {SLEAF}
  forceB (Nat.land (Nat.shiftRight w 15) 1) fun F =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 16) 2097151) 2097151 (Nat.beq F 1)) fun T =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight w 37) (Nat.shiftRight w 16) (Nat.beq F 1)) fun E =>
  ctestM top bk tD bD (pt3 pb) R {COORDS} {QV} T E

theorem covered_of_sleafM {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true)
    (w {COORDS} : ℕ) (h : sleafM top bk tD bD pb R w {COORDS} = true) : Covered {COORDS} := by
  unfold sleafM at h
  simp only [forceB_eq] at h
  exact covered_of_ctestM (pb := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
""" + walk_part(NAME) + f"""
end AMW.Cert.{NAME}

end
"""
    return out


def walk_part(NAME):
    """the walk with minorant leaves: kind 2 splits on bit 3 into a basin leaf (record length 4) and a minorant leaf
    (bits 4..12 its record length, `sleafM` read from bit 10, so its fields start at bit 13)"""
    UL = f"u{Q - 1}"
    TBLB = "{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ}"
    HYPS = "(hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true)"
    HV2 = " ".join(V) + " " + HV
    K = lambda k: f"(Nat.beq (Nat.land (Nat.shiftRight w 1) 3) {k})"
    return f"""
/-! ### the walk with minorant leaves

A leaf record (bit 0 clear): bits 1..2 the kind.  Kind 0: zero order (length 3).  Kind 1: slope (`sleaf`, length 16 or
37).  Kind 3: centre (`cleaf`, length 12 or 33).  Kind 2: bit 3 clear, a basin (length 4); bit 3 set, a minorant leaf
whose record length is bits 4..12 and whose `sleafM` word is the record shifted by 10 (its `dec` modes at bits 13..24,
flag at bit 25, then `T` unless flagged, then the term data). -/

/-- a leaf of the walk with minorant leaves: the next position, or `0` -/
def leafStepM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (pos w {COORDS} : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) 0
            (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 33) (Nat.add pos 12) (Nat.beq (Nat.land (Nat.shiftRight w 11) 1) 1))
            (cleaf top bk tD bD pb R C w {COORDS}))
          (Bool.rec (motive := fun _ => ℕ)
            (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add pos 4) (inBas bas {COORDS}))
            (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add pos (Nat.land (Nat.shiftRight w 4) 511))
              (sleafM top bk tD bD pb R (Nat.shiftRight w 10) {COORDS}))
            (Nat.beq (Nat.land (Nat.shiftRight w 3) 1) 1))
          {K(2)})
        (Bool.rec (motive := fun _ => ℕ) 0
          (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 37) (Nat.add pos 16) (Nat.beq (Nat.land (Nat.shiftRight w 15) 1) 1))
          (sleaf top bk tD bD pb R C w {COORDS}))
        {K(1)})
      (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add pos 3) (leafOK top bk {COORDS}))
      {K(0)})
    (Nat.add pos 3) (Nat.ble (Nat.add {UL} 1) l0)

/-- the bisection walk with minorant leaves (`Nat.rec` on the fuel): the node word is `bits >>> pos` -/
def walkM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos {COORDS} =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStepM top bk tD bD pb R C bas pos w {COORDS}) (splitAx ih pos (Nat.land (Nat.shiftRight w 1) 7) {COORDS}) (Nat.beq (Nat.land w 1) 1))
    fuel

theorem leafStepM_sound {TBLB} {HYPS} {{bas : List Bx}} (hbas : BasOK bas) (pos w {COORDS} : ℕ)
    (h : leafStepM top bk tD bD pb R C bas pos w {COORDS} ≠ 0) : Covered {COORDS} := by
  unfold leafStepM at h
  cases hs : Nat.ble (Nat.add {UL} 1) l0
  · rw [hs] at h
    cases hk0 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 0
    · rw [hk0] at h
      cases hk1 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 1
      · rw [hk1] at h
        cases hk2 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 2
        · rw [hk2] at h
          cases hl : cleaf top bk tD bD pb R C w {COORDS}
          · rw [hl] at h; exact absurd rfl h
          · intro {HV2}
            exact Or.inl (cleaf_sound hlb hD hpt hR w {COORDS} hl {HV2})
        · rw [hk2] at h
          cases hm : Nat.beq (Nat.land (Nat.shiftRight w 3) 1) 1
          · rw [hm] at h
            cases hl : inBas bas {COORDS}
            · rw [hl] at h; exact absurd rfl h
            · exact inBas_sound hbas {COORDS} hl
          · rw [hm] at h
            cases hl : sleafM top bk tD bD pb R (Nat.shiftRight w 10) {COORDS}
            · rw [hl] at h; exact absurd rfl h
            · exact covered_of_sleafM hlb hD hpt hR _ {COORDS} hl
      · rw [hk1] at h
        cases hl : sleaf top bk tD bD pb R C w {COORDS}
        · rw [hl] at h; exact absurd rfl h
        · intro {HV2}
          exact Or.inl (sleaf_sound hlb hD hpt hR w {COORDS} hl {HV2})
    · rw [hk0] at h
      cases hl : leafOK top bk {COORDS}
      · rw [hl] at h; exact absurd rfl h
      · intro {HV2}
        exact Or.inl (leaf_sound hlb {COORDS} hl {HV2})
  · intro {HV2}
    right
    have hsk : {UL} < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : ({UL} : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walkM_sound {TBLB} {HYPS} {{bas : List Bx}} (hbas : BasOK bas) (bits : ℕ) :
    ∀ fuel, WalkOK (walkM top bk tD bD pb R C bas bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos {COORDS} h; exact absurd rfl h
  | succ fuel ih =>
    intro pos {COORDS} h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStepM top bk tD bD pb R C bas pos (Nat.shiftRight bits pos) {COORDS})
        (splitAx (walkM top bk tD bD pb R C bas bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 7) {COORDS})
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
    · rw [hb] at h'; exact leafStepM_sound hlb hD hpt hR hbas pos _ {COORDS} h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ {COORDS} h'

/-- **a box is covered when the walk with minorant leaves reaches its end** -/
theorem covered_of_walkM {TBLB} {HYPS} {{bas : List Bx}} (hbas : BasOK bas) (bits fuel {COORDS} e : ℕ)
    (h : walkM top bk tD bD pb R C bas bits fuel 1 {COORDS} = e) (he : e ≠ 0) : Covered {COORDS} :=
  walkM_sound hlb hD hpt hR hbas bits fuel 1 {COORDS} (h ▸ he)
"""


if __name__ == "__main__":
    toks = open(sys.argv[1]).read().split()
    Qp, SA = int(toks[0]), int(toks[1])
    assert Qp == Q
    aN = [int(x) for x in toks[2].split(",")]; bN = [int(x) for x in toks[3].split(",")]
    cN = int(toks[4]); NAME = toks[5]
    open(sys.argv[2], "w").write(gen(NAME, SA, aN, bN, cN))
