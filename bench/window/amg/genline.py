#!/usr/bin/env python3
"""(bridge-port) The slope test with per-term modes for a seven-point instance: `ctestL` / `sleafL` and their soundness,
emitted against the instance's existing `cscheck` (gen7cnam.py), so nothing of the instance is regenerated.

Each pair term t reads its mode m_t = mdOf (bitOf T t) E t (AMW/LineMode.lean): 0 when not expanded, else
1 + (2-bit field t of E): 1 tangent at q with charge (convex: no charge), 2 left line, 3 right line, 4 mean value.
E = 0 is the existing slope test.  A line or mean-value term needs no charge and no half-range derivative reads.

Leaf word of `sleafL` (kind field read by the walk, not here): bits 3..14 the six 2-bit `dec` modes, bit 15 the
all-expanded flag, then the 21-bit expansion set T unless the flag is set, then E (42 bits).
Usage: genline.py PARAMS OUT.lean      (PARAMS: the instance's *_params.txt)"""
import sys
from gen7am import Q, PAIRS, NP, TS, SC, U, U1, COORDS, QV, V, mem, HV, ssum, nsum, bit, term_g


def md(t): return f"(mdOf {bit(t)} E {t})"


def gen(NAME, SA, aN, bN, cN):
    IMPL = "{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}"
    XV = " ".join(f"x{t} eu{t} ed{t} v{t}" for t in range(NP))
    ST = []
    for t, (i, j) in enumerate(PAIRS):
        L, Uu, QS = nsum('l', i, j), nsum('u', i, j), nsum('q', i, j)
        ST.append(f"forceB {md(t)} fun m{t} =>")
        ST.append(f"bforce (lmCv m{t} (inRg R {L} {Uu})) fun v{t} =>")
        ST.append(f"forceB (lmX m{t} top bk pb tD bD {L} {Uu} {QS}) fun x{t} =>")
        ST.append(f"forceB (selUv v{t} {bit(t)} tD bD {QS} {Uu}) fun eu{t} =>")
        ST.append(f"forceB (selDv v{t} {bit(t)} tD bD {L} {QS}) fun ed{t} =>")
    CTEST = "\n  ".join(ST) + f"\n  cscheck {COORDS} {QV} T {XV}"

    def cv(t):
        i, j = PAIRS[t]
        return f"(lmCv {md(t)} (inRg R ({ssum('l', i, j)}) ({ssum('u', i, j)})))"

    def xr(t):
        i, j = PAIRS[t]
        return f"(lmX {md(t)} top bk pb tD bD ({ssum('l', i, j)}) ({ssum('u', i, j)}) ({ssum('q', i, j)}))"
    XARGS = " ".join(f"{xr(t)} (selUv {cv(t)} {bit(t)} tD bD ({ssum('q', i, j)}) ({ssum('u', i, j)})) "
                     f"(selDv {cv(t)} {bit(t)} tD bD ({ssum('l', i, j)}) ({ssum('q', i, j)})) {cv(t)}"
                     for t, (i, j) in enumerate(PAIRS))
    flat = []
    for r in range(Q): flat += [f"hq{r}1", f"hq{r}2"]
    for t in range(NP): flat.append(f"hok{t}")
    pat = flat[0]
    for c in flat[1:]: pat = f"⟨{pat}, {c}⟩"
    pat = f"⟨{pat}, hmain⟩"

    out = f"""import AMW.AMS02Inst
import AMW.LineMode

/-! ###### `{NAME}` with per-term modes: the slope test `ctestL` (tangent / left line / right line / mean value per
expanded pair term, from the 2-bit fields of `E`; `E = 0` is `ctest`) and the slope leaf `sleafL`, emitted against
the instance's `cscheck` (genline.py, bridge-port). ###### -/

noncomputable section

namespace AMW.Cert.{NAME}

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the slope test at the point `q` with expansion set `T` and term modes `E` -/
def ctestL (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) ({COORDS} : ℕ) ({QV} : ℕ) (T E : ℕ) : Bool :=
  {CTEST}

theorem ctestL_spec {IMPL} ({COORDS} : ℕ) ({QV} : ℕ) (T E : ℕ)
    (h : ctestL top bk tD bD pb R {COORDS} {QV} T E = true) :
    cscheck {COORDS} {QV} T {XARGS} = true := by
  unfold ctestL at h
  simp only [forceB_eq, bforce_eq] at h
  exact h

set_option maxHeartbeats 40000000 in
theorem ctestL_sound {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    ({COORDS} : ℕ) ({QV} : ℕ) (T E : ℕ) (h : ctestL top bk tD bD pb R {COORDS} {QV} T E = true) :
    ∀ {' '.join(V)} : ℝ, {mem} → (cN : ℝ) / SA ≤ G {' '.join(V)} := by
  intro {' '.join(V)} {HV}
  have h' := ctestL_spec {COORDS} {QV} T E h
  unfold cscheck at h'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h'
  obtain {pat} := h'
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
"""
    for t, (i, j) in enumerate(PAIRS):
        L_, U_, Q_ = f"({ssum('l', i, j)})", f"({ssum('u', i, j)})", f"({ssum('q', i, j)})"
        hl = ", ".join(f"h{r}1" for r in range(i, j)); hu = ", ".join(f"h{r}2" for r in range(i, j))
        out += (f"  obtain ⟨d{t}, hdl{t}, hdu{t}, hb{t}⟩ := lterm_bound hlb hD hpt hR {md(t)} {bit(t)} (lmBit_md _ _ _) {L_} {U_} {Q_} (by omega) (by omega) hok{t}\n"
                f"    ({term_g(i, j)}) (by push_cast; (try simp only [add_div]); linarith [{hl}]) (by push_cast; (try simp only [add_div]); linarith [{hu}])\n"
                f"  push_cast at hb{t}\n")
    out += f"  rw [hSCe] at {HV}\n"
    for r in range(Q):
        out += (f"  have hl{r} : (l{r} : ℝ) ≤ q{r} := by exact_mod_cast hq{r}1\n"
                f"  have hu{r} : (q{r} : ℝ) ≤ u{r} := by exact_mod_cast hq{r}2\n")
    for r in range(Q):
        Er = f"(({bN[r]} : ℝ) + {' + '.join(f'{aN[t]} * d{t}' for t in TS[r])})"
        Kx = " + ".join([str(U1 * bN[r])] + [f"{aN[t]} * tK {bit(t)}" for t in TS[r]])
        Mx = " + ".join(f"{aN[t]} * tM {bit(t)} {xr(t)}" for t in TS[r])
        Kn = " + ".join(f"{aN[t]} * tK {bit(t)}" for t in TS[r])
        Px = " + ".join([str(U1 * bN[r])] + [f"{aN[t]} * tP {bit(t)} {xr(t)}" for t in TS[r]])
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

theorem covered_of_ctestL {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    ({COORDS} : ℕ) ({QV} : ℕ) (T E : ℕ) (h : ctestL top bk tD bD pb R {COORDS} {QV} T E = true) : Covered {COORDS} := by
  intro {' '.join(V)} {HV}
  exact Or.inl (ctestL_sound hlb hD hpt hR {COORDS} {QV} T E h {' '.join(V)} {HV})

"""
    SLEAF = "\n  ".join(f"forceB (dec (Nat.land (Nat.shiftRight w {3 + 2 * r}) 3) l{r} u{r}) fun q{r} =>" for r in range(Q))
    out += f"""/-- a slope leaf with term modes: `dec` modes (bits 3..14), the all-expanded flag (bit 15) or the expansion set
(bits 16..36), then the term modes `E` (from bit 16 when the flag is set, else from bit 37) -/
def sleafL (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) ({COORDS} : ℕ) : Bool :=
  {SLEAF}
  forceB (Nat.land (Nat.shiftRight w 15) 1) fun F =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 16) 2097151) 2097151 (Nat.beq F 1)) fun T =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight w 37) (Nat.shiftRight w 16) (Nat.beq F 1)) fun E =>
  ctestL top bk tD bD (pt3 pb) R {COORDS} {QV} T E

theorem covered_of_sleafL {IMPL} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true)
    (w {COORDS} : ℕ) (h : sleafL top bk tD bD pb R w {COORDS} = true) : Covered {COORDS} := by
  unfold sleafL at h
  simp only [forceB_eq] at h
  exact covered_of_ctestL (pb := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

end AMW.Cert.{NAME}

end
"""
    return out


if __name__ == "__main__":
    toks = open(sys.argv[1]).read().split()
    Qp, SA = int(toks[0]), int(toks[1])
    assert Qp == Q
    aN = [int(x) for x in toks[2].split(",")]; bN = [int(x) for x in toks[3].split(",")]
    cN = int(toks[4]); NAME = toks[5]
    open(sys.argv[2], "w").write(gen(NAME, SA, aN, bN, cN))
