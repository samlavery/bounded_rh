# Bridge scope: Theorem D + weighted n-point assembly for the AMTOPA window (2026-10-02, rev. 2)

**Target:** κ ≥ 0.67340 at n = 7 with the AMTOPA window and B = 93/23000. The LP ceiling is 0.6734131 (§5).
The certificate (w_AM enclosures plus the 6-D walk) is mvt-engine's job. This document scopes the BRIDGE: everything
from the pinned Zeta23 up to
`n_point_bound_w'` with `H_AM`, and then `candidate_critical_line_bound(_cumulative)`.

**Files in this directory:**
- `ww.py`, `window_facts.py`, `adm_check.py`
- `TVPosVar.lean` (compiled; standard axioms only)
- `ProbeGeneric.lean`
- logs: `am_runs.log`, `trunc_runs.log`

Zeta23 paths are relative to `zeta23/Zeta23/` (clone at 3635e74).

## 1. What the bridge consumes from the window

The window enters κ only through `cRatio λ a b J = λa²/(b+λ²J)` (`ThmD/AssemblyD.lean:28`).
Here a = L⁻¹∫φ², b = L⁻¹∫φ⁴ and J = (2/L³)∫₀ᴸ(φ²⋆φ²)(y)y dy (`ThmD/Concrete.lean:36-51`).
The pair kernel enters through `kernel_limit` (gram entries → kfun).

**AMTOPA's window.** v(s) = Σ_j c_j cos(ω_j s), with ω₀ = √2, ω_j = 2πj and c from `candidate.json` (c₀ = 1).
It replaces cos(√2 s) as the profile of φ², so φ = √(v/M)·taper.
- **H closed form** (exact; matches AMTOPA's 40 digits): H_AM = H_MT − Σ_{j≥1} c_j²(½ − 1/(4π²j²)) / (2 sin²(1/√2)) = 0.6721881581.
  - Why: v* = cos(√2·) optimises the functional, so ∫|s−s′|cos(√2s)ds = β − cos(√2s′).
  - Also ∫|s−s′|cos(2πjs)ds = ((−1)^j − cos(2πjs′))/(2π²j²) (checked numerically).
  - So all cross terms cancel, and the cos(2πj·) block is diagonal.
- **Kernel:** K_AM(x) := ∫_{−½}^{½} v(t)cos(2πxt)dt = Σ_j c_j[sinc((ω_j−2πx)/2) + sinc((ω_j+2πx)/2)]/2.
  K_AM(0) = √2 sin(1/√2), and kfunAM = K_AM/K_AM(0), so it is independent of M.

## 2. Admissibility obligations (`AdmWindow`, `ThmD/WindowCore.lean:31-43`, plus `LocalHypsCore` extras)

Measured by `adm_check.py`:

| obligation | needed for | as given (M = 1) | with v/M, M = 5/4 |
|---|---|---|---|
| `le_one` φ ≤ 1 | WindowCore:37 | **fails**: max φ² = 1.00827 (+0.83%) | φ² ≤ (1+Σ\|c_j\|)/M ≤ 0.852 |
| `l1_deriv` ‖φ′‖₁ ≤ 2 | WindowCore:40 → \|φ̂\|\|r\| ≤ 2, ψ-majorant (PrimeSideA/Basic:57,376) | **fails**: 2.0223 (+1.1%) | 1.809 |
| `l1_deriv_sq` ‖(φ²)′‖₁ ≤ 2 | WindowCore:41 → Phi_le_inv (Basic:405), \|g′\| ≤ 2 in `sumA2g_close` | **fails**: 2.0420 (+2.1%) | 1.634 |
| `b_ge_half` b > ½ | LocalHypsCore (Basic:429) | 0.851 | 0.545 |
| ½ ≤ a ≤ 1 | `ab_range`, zero side | 0.919 | 0.735 |
| `contDiff 2`, `support`, `even`, `nonneg` | WindowCore:35-39 | hold | v ≥ cos(√2 s) − 0.0652 > 0 for \|s\| < 1.06 |
| `l1_deriv2(_sq)` ≤ c/w | WindowCore:42-43 | hold | c is free (error terms only) |

**The fix is exact.** `cRatio` is invariant under φ ↦ φ/√M, and kfun is normalised, so κ is unchanged. **No gain is lost.**
- Admissible M ∈ [1.0225, 1.3046). The lower end comes from TV/le_one; the upper end from b > ½.
- Both TV fields reduce to a positive-variation bound PV(v) := ∫₀^½(v′)₊ ≤ 0.100 at M = 5/4. The true value is 0.00727 (3 rises), so the slack is 14×.
- The reduction uses ‖f·τ‖′₁/2 = f(0) + 2PV and (fτ)′₊ ≤ f′₊ for τ the ramp.
- The two lemmas for this reduction are **written and compiled** in `TVPosVar.lean`: `integral_abs_deriv_le_two_of_posVar` and `max_deriv_mul_le`.
- PV ≤ 0.1 itself needs a small certificate: about 128 cells with Lipschitz slack, using sin values from the file's integer Taylor evaluators.
- The other choice is M = 1 + Σ|c_j| = 1.0652, where le_one follows from the triangle inequality, but the PV budget is only 0.025.

**Truncation.** At n = 7, 13 terms give 0.6734132, equal to 17 terms (0.6734131). So the j ≥ 13 terms are free to drop.
**Recommendation:** make the bridge parametric in the coefficient list, so the 13/17 choice stays with the certificate side.

## 3. Declarations: instantiate / port / generalise

**Reuse unchanged (pinned Zeta23):**
- `AdmWindow` and its facts, `AdmWindow.localHypsCore` (`WindowLocalHyps:24`), `PsiC`.
- `ThmD.sumA2g_close`, `ThmD.autocorr_deriv_facts` (`Window:1703`).
- Traces (`tracesBoundsD_of_factsD`), AssemblyD, Endgame, PrimeSideA/B, `PaperInputs`/`paperInputs_zeta`.
- `ZeroSide.blockInputsAt`, `Tail.TailHyp.tailInputs`, `Gz_eq_Gp`, `cumulative_of_dyadic`.

**Port from XiPrime.** These are generic, but our tree's XiPrime oleans are stale 4.34.0 builds: the
`ProbeGeneric.lean` import fails with "incompatible header" at `XiPrime/Statement.olean`. So copy them; do not import.
- `Params.phiV/atV` (`XiPrime/Defs:201/206`) plus the rfl lemmas (`QuarticWindow/Params`).
- Generic zero side §1 (`QuarticWindow/ZeroSide:36-117`).
- `ModWindow.lean` (27 KB, imports only WindowCore/Taper), with `ModFactor.antitone`:38 replaced by the PV hypothesis.
- `vConv/jWin/cWin`, `tendsto_cRatio_cWin` (`XiPrime/Window:92`), `tendsto_JT_of_autocorr_close` (:122).
- The `edge_estimate` (`Moments:34`) and `autocorr_phiMQsq_close` (`Moments:369`) patterns.

**Port from ThmD with the window swapped:**
- `Concrete.lean` (12.5 KB → `concreteFactsAM`). MT enters it only at `localFunD` and at `gD_deriv_facts`:153/215 (use `autocorr_deriv_facts`) and `phiD_eq_zero`:221.
- `kernel_eq` (`Functional:321`, private) for the cos(√2·) kernel identity.

**New Lean:**
- (a) window facts and PV certificate.
- (b) Fubini/swap: 2∫₀¹ r·vConv(v)(r)dr = ∬|s−s′|v(s)v(s′).
- (c) the cos(2πj·) kernel identity and the H_AM assembly.
- (d) a rational floor for H_AM, built from the file's `HD_one_bounds` and sin(1/√2) bounds.
- (e) `KfunAM` closed form (from the file's `integral_cos_mul_eq_sinc`), K_AM(0) > 0, and |K_AM| ≤ K_AM(0) (needs v ≥ 0).

**Generalise in our bridge (`SolutionSevW10D.lean`, 72 declarations touch MT names):**
- **Root definitions:** `Kfun/kfun/wfun`:252-257 become the AM versions; the 8 helpers at 451-501 only need v ≥ 0 and evenness.
  `mtParams`:377 becomes `(paramsOf stdProfile 1).atV vAM/M`.
- **Rewrite:**
  - Window §:1088-1110.
  - Limit §:1219-1385, using a sharp-AM comparison and a/b closeness.
  - `Kfun_eq_sum`/`Kinf_eq`/`gram_close_of`:1423-1496.
  - `tail_passage`:1889, which takes the AM prime side, the cRatio limit → c_AM, the zero side, and HD 1 ↦ H_AM.
  - `kernel_limit`:1949.
  - `eventually_h7`:2990 (`poissonSqD`/`aD_range_of` become their generic V versions).
- **Restate over a family:** `endgame_defect`:858, whose proof is already generic.
- **Rename HD 1 to H_AM (statements only):** `Phi_n`, `Phi`, `Phi_w`, `Phi_w'`, `solve_linear`, `pre_solve(_w,_w')`, `n_point_bound(_w,_w')`.
- **Unchanged:** `deleted_strips`, `span_retained_le` and S11–S16. They only use L and d, which agree by rfl, or wfun's abstract properties.
- **Delete:** the MT-only corollaries (`Phi_paper`, `seven_point_bound_*`, `eight_point_*`).

**Interface with mvt-engine.** Their `kfunAM` must equal the bridge's normalised integral.

> Proposal: `vAM t := Σ_{j<K} (cAM j : ℝ)·cos(ωAM j·t)` with integer cAM/10⁹;
> `kfunAM x := KfunAM x / KfunAM 0` with KfunAM the integral above;
> the bridge proves the sinc closed form, and the certificate proves `c ≤ Fw W g` for `wfunAM := kfunAM²`.

## 4. Size and time (bridge only)

**Size:**
- Window layer: about 110–130 KB (A 8, B 45, C 15, D 15, E 40; minified ×0.7).
- Bridge edits: about +25 KB net.
- Bridge + window total: about 0.32 MB. That leaves about 1.65 MB of the 2 MB for the certificate.
- Elaboration adds roughly 1–3 min of build time, which the time projection must include.

**Time:** about 6–8 agent-days sequentially.
- B (admissibility + PV certificate): 1.5 days.
- E (J limit, Fubini, H_AM): 2 days.
- F (retarget): 1.5 days.
- A/C/D: 1.5 days.
- Integration: 0.5 day.
- With B, E and F run in parallel by separate agents, about 3–4 days wall.

## 5. LP ceilings under our assembly (Φ = (H − B(m−q)/m)/(1 − ε(m−q)/m), window's own H, strong oracle)

| n | best B | ε* | Φ_w′ (m) | h_m-law control |
|---|---|---|---|---|
| 6 | 0.0036 | .0070822 | .6733167 (146) | .6733183 |
| 7 | 0.0040435 | .0079101 (LP upper .0079127) | **.6734131** (132) | .6734161 |
| 8 | 0.0040435 | .0079669 | **.6734398** (132) | .6734439 (= Hunt #91) |

**For κ ≥ 0.67340 at n = 7**, the certificate margin must be δ ≲ 0.25% of ε*: δ = 0.1% gives 0.6734080 and δ = 0.3% gives 0.6733977.
H_AM must be floored to about 1e-9, which is easy.

## 6. Riskiest single bridge obligation

**The exact J limit:** (2/L³)∫₀ᴸ g_T(y)y dy → J(v_AM), with J(v_AM) identified in closed form so that cRatio → c_AM and
2 − 1/c_AM = H_AM.
- The generic lemma `tendsto_JT_of_autocorr_close` gives the limit in vConv form.
- Converting it needs the swap identity (new measure theory on a triangle; about 150–250 lines) plus the two kernel identities.
- The other obligations are ports of compiling code or small certificates with ≥ 14× slack.
- **Fallback if the swap identity stalls:** closed forms for vConv(cos α·, cos β·) and their r-moments. No Fubini is needed, but
  there are two generic α ≠ β / α = β lemmas and a 13×13 sum to simplify.
- **No obligation fails** once v is divided by M ∈ [1.0225, 1.3046), and that change costs nothing in κ.

## 7. Build status (2026-10-02): stages A and E compiled

Modules live in `root/AMW/`. Every exported theorem uses only the standard axioms; there is no sorry, axiom or native_decide.

| module | bytes | content |
|---|---|---|
| `Window.lean` | 21,950 | coefficients, vAM, MAM = 5/4, phiW, fW (C², \|fW′\| ≤ 2/L, \|fW″\| ≤ 52/L²), localFunW |
| `Moments.lean` | 31,338 | a/b/J closeness; `tendsto_cRatio_W`; `cRatio_W_pos` |
| `Swap.lean` | 9,365 | `swap_identity` (the integral swap), `JInf_eq_energy` |
| `Constant.lean` | 24,826 | kernel identity, Euler–Lagrange cancellation, `HW_eq` |
| `Floor.lean` | 11,111 | `HW_ge : 6721883/10⁷ ≤ HW`; `eventually_aW_range`, `eventually_bW_ge_half` |
| `Kernel.lean` | 5,733 | `KfunAM`, `kfunAM`, `wfunAM`; `KfunAM_eq_sinc`, \|K\| ≤ K(0), evenness, `0 ≤ w ≤ 1` |

The swap identity was the risk named in §6. It closed in about 200 lines using Mathlib's `integral_integral_swap`, so the fallback was not needed.

`Kernel.lean` later grew to 12,779 bytes with the closed forms `KfunAM_closed`, `KfunAM_at_int`, `KfunAM_zero_closed` and `KMT_eq_gamma`.

## 8. Stage H, done early: the measured budget of the layer (2026-10-02)

`assemble_am.py` builds `AMH.lean`:
- the hoisted imports;
- the 17 AMW/Br modules in topological order;
- a stand-in tail. It is the real n = 7 tail (AMTOPA's weights, `n_point_bound_w'` at m = 132, c = 0.0078943, κ = 0.6734 via `HW_ge`), except that the scored theorems take `hCert` as a hypothesis.

It was checked with `pyr/private_check_rec.sh` in `specroot_amh` against record 6731631/10⁷. Result: BUILD EXIT 0, standard axioms.

| bytes | build | module replay | export | nanoda | closure replay | post |
|---|---|---|---|---|---|---|
| 433,027 (minified 387,833) | 96.9 s (2.84 GB) | 17.8 s (989 consts) | 37.7 s | 53.6 s | 82.6 s (71,431 consts) | 173.9 s |

**Layer projection:** 157 + 2·96.9 + 2.46·173.9 = 779 s.

**What is left for the certificate (G):**
- **Conservative limit (2,700 s):** 2·Δbuild + 2.46·Δpost ≤ 1,921 s. That is roughly a SevW10D-sized certificate: module replay ≲ 200 s, build ≲ 420 s locally.
- **Hard limit (f = 2.56, 3,240 s):** ≤ 2,444 s.
- **Bytes:** ≤ 1.56 MB.

**Rerun with the pruned bridge, AMTail, and SevW10D's certificate as a cost stand-in.** The stand-in is the block from `ThreePoint/Base` to the data, with its kernel renamed to `KfunMT/kfunMT/wfunMT/FMT`; its `cert` sits in the scored closure. All three builds have BUILD EXIT 0 and standard axioms.

| file | bytes | build | module replay | export | nanoda | closure replay | post | projection (f = 2.46) |
|---|---|---|---|---|---|---|---|---|
| AMH2 (pruned layer) | 362,606 | 105.9 s | 28.1 s | ≈38 s | 56.4 s | 86.2 s | ≈181 s | 813 s |
| AMHM (layer + SevW10D certificate) | 1,520,281 | 536.3 s (5.11 GB) | 226.1 s | 40.2 s | 245.1 s | 344.7 s | 630.0 s | **2,779 s** |

- **Against the limits:** a SevW10D-sized certificate is 79 s (2.9%) over the conservative 2,700 s. Under f = 2.56 / 3,240 s it projects to 2,842 s, which passes with a 398 s margin.
- **The certificate's budget:** 2·Δbuild + 2.46·Δpost ≤ 1,887 s (conservative), or ≤ 2,409 s (hard). SevW10D's certificate costs 1,966 model-seconds, so G should aim for ≤ ~0.96× it (conservative) or ≤ ~1.2× it (hard).
- **Bytes:** ≤ ~1.63 MB for G plus the tail.

## 9. The AM six-point file (AMX05), assembled and checked (2026-10-03 ~00:40Z)

**Build:** `assemble_am.py AM6.lean --roots AMTail,AMX05Data --final6 AMX05` → `AM6.lean`, 1,311,211 bytes, 35 modules.

**The tail:**
- W6 is parsed from `AMX05.G` (B = 0.0036, c = 707843/10⁸); `Fw_W6` follows by rfl on the kernel.
- `cert_AM` comes from `AMX05_cert_full`.
- m = 146, Φ ≥ 0.6733143769, κ = 6733143/10⁷.

**Private check against 6731663/10⁷:** BUILD EXIT 0, standard axioms.

| build | module replay | export | nanoda | closure replay | post | projection | peak footprint (build) |
|---|---|---|---|---|---|---|---|
| 343.5 s | 133.5 s (4,349 consts) | 39.7 s | 134.9 s | 207.5 s (74,758 consts) | 382.1 s | **1,784 s** (f = 2.56: 1,822 s) | **4.06 GB** (RSS 9.14 GB) |

The footprint is below accepted SevW10D's 4.77 GB.

## 10. Window optimisation for our assembly (2026-10-03)

**Method:** `wopt.py`, `wopt2.py`, `wopt3.py`, `wscan_vec.py`. Every value is an LP ceiling under `n_point_bound_w'` with c(m−q) ≤ 1, using strong-oracle floors.

| window | n = 6 | n = 7 (B = 0.0040) |
|---|---|---|
| cos(√2 s) (MT) | 0.6731234 (B 0.0036) | 0.6731674 |
| cos(1.5 s) (typh) | 0.6731746 (B 0.0040) | 0.6732217 |
| AMTOPA, 13 terms | 0.6733166 (B 0.0036) | 0.6734131 |
| AMTOPA re-optimised jointly with (a, b) | **0.6733687** (B 0.0036) | **0.6734250** |

**Notes on the table:**
- The best single cosine is ω₀ ≈ 1.45–1.5.
- In every joint optimum ω₀ stays ≈ √2 (1.41399 at n = 6, 1.41419 at n = 7).
- The optimum depends on n. The n = 6 window evaluated at n = 7 gives only 0.6734040.

**Optimiser caveats.** These are properties of the instruments used, not limits of the window family:
- At n = 7, three local methods stop at about +1.2e-5: the envelope gradient, the warm-started line search, and the trust-region LP. The trust-region LP's linearised gains at fixed (a, b) are about 1e-6.
- Global or basin-hopping searches were not run.

**Optimal windows found:**
- n = 6: θ = [1.413988936, 0.011417303, −0.012082749, 0.00111932, 0.007768774, −0.002270835, 0.008614841, −0.007848066, 0.001839062, 0.000679183, −0.000378738, 0.000274196, −0.00021119].
- n = 7: θ = [1.414189347, 0.012078945, −0.013283088, 0.003963606, 0.00604252, −0.001347463, 0.006607159, −0.007899775, 0.005702398, −0.005766402, −0.000879305, 0.000543568, −0.000412815].

## 11. The R windows: rational coefficients, LP weights, and the layers in rootR / rootR7 (2026-10-02)

**Method (`rwin.py N B_SA θ OUT`):**
- ω₀ = √2 exactly; the twelve corrections are rounded to integers over 10⁹.
- The LP is re-solved on the exact rounded window, mirror-symmetrised and floored to integers over 10⁸.
- Each span sum is ≤ 2·10⁸; the b_r sum exactly to B and are symmetric.
- ε is the strong float floor of G at the rounded weights: the minimum over 3 seeds with lattice starts.
- H is the exact closed form at 40 digits. The proved floor is checked against the exact-rational floor expression that `floor_numeric` evaluates.

| | R6 (n = 6) | R7 (n = 7) |
|---|---|---|
| cAMn (j = 1..12, over 10⁹) | 11417303, −12082749, 1119320, 7768774, −2270835, 8614841, −7848066, 1839062, 679183, −378738, 274196, −211190 | 12078945, −13283088, 3963606, 6042520, −1347463, 6607159, −7899775, 5702398, −5766402, −879305, 543568, −412815 |
| Σ\|c_j\| (≤ 13/200) | 0.054504 | 0.064527 |
| \|v′\| bound (≤ 7/2) | 2.874 | 3.350 |
| \|v″\| bound (≤ 78) | 50.42 | 77.48 |
| v(0)/M (≤ 81/100) | 0.80714 | 0.80428 |
| PV cell sum (≤ 9/200) | 0.03228 | 0.04259 |
| H (exact) | 0.67221980259 | 0.67218115086 |
| proved `HW_ge` | 6722198/10⁷ | 67218115/10⁸ |
| B (over 10⁸) | 360000 | 400000 |
| strong ε (over 10⁸) | 711347 | 787449 |
| Φ at δ = 0 / 0.05 % / 0.1 % | 0.6733688 / 0.6733664 / 0.6733641 | 0.6734248 / 0.6734227 / 0.6734201 |

- Every existing Lean constant holds for both windows, so only cAMn, `vAM_zero`, `HW_ge` and the AMTail constant changed. The bridge-port modules compile unchanged; `pvCheck (9/200)` is decided by the kernel on the new cAMn.
- For R7 the tightest margin is |v″| at 77.48 against 78.
- Pair weights: `rwin6.json` and `rwin7.json`.

**Layers built:**
- rootR and rootR7: all 18 modules, Window … AMTail, built with `buildR.sh ROOT` (≈ 14–23 s per module) and standard axioms.
- root/ is untouched: AM6x is live.

**Assembler (`assemble_am.py`):**
- `--root` reads the layer from ROOT. The H floor is read from `Floor.HW_ge` and checked against AMTail.
- The window header is written from the coefficients: AMTOPA, or R with the c_j listed.
- `--npts N` generalises the --final6 tail to n points.
- Regression: n = 6 on root reproduces AM6x.lean byte for byte.
- The n = 7 tail was compiled against rootR7 with a STUB certificate (`smokeT7/`, `sorry` in the stub only). Everything else is clean: κ 6734201/10⁷, m 133.

**Measured checks** (private_check_rec against 6733166/10⁷, then stage.sh):

| file | build | replay | export | nanoda | closure | conservative projection | peak |
|---|---|---|---|---|---|---|---|
| AM7m (AMM1, root, κ 6734033) | 520 s | 223 s | 44 s | 219 s | 272 s | 2,512 s | 5.02 GB |
| AR7 (AMR7, rootR7, κ 6734227) | 569 s | 242 s | 42 s | 255 s | 307 s | 2,782 s | 5.26 GB |

Both pass.

## 12. R8 (n = 8) window (2026-10-02)

- **Method:** `wopt8.py`, a constrained line-search ascent.
  - ω₀ is frozen at √2 and K = 12.
  - The layer's constants are hard constraints with margins: S1 ≤ 13/200, |v′| ≤ 7/2, |v″| ≤ 78, PV ≤ 9/200, v(0)/M ≤ 0.81.
  - Steps are projected off near-active constraints. It starts from R7 at B = 0.0040435, the best of the B scan {0.0038, 0.0040435, 0.0042, 0.0044}.
- **Oracle fault found at seven gaps:** `famq.global_min` keeps the 120 lowest samples for descent. Random samples crowded out the lattice basin near (2,1,2,2,1,2,1), so the LP reported ε 0.0080521 for weights whose floor was 0.0080448.
  - Fix: `smin` gives lattice starts their own quota. `evaluate_s` folds the strong minimisers into the LP as cuts until the LP and the strong search agree. `rwin.py` uses both for n ≥ 8.
- **Result:** `rwin8.json`.
  - cAMn = 12310798, −15041681, 3867664, 6489926, −992327, 5580097, −6846472, 3781297, −5670353, 3355089, −450523, −218483.
  - H = 0.67216841056, floor 67216841/10⁸. B = 404350, robust ε = 805165/10⁸.
  - Φ: 0.6734738 (δ = 0), 0.6734712 (0.05 %), 0.6734686 (0.1 %); m 131. The AMTOPA-13 ceiling was 0.6734398.
  - Margins: S1 0.064605, |v′| 3.319, |v″| 77.235, PV 0.04406, v(0)/M 0.80493. S1, |v″| and PV are active.
- **Variants that did not help:**
  - K = 16: 0.6734688 (strong).
  - S1 ≤ 7/100 with ρ = 0.048: weak 0.6734732, against weak 0.6734738 constrained; |v″| binds.
- **rootR8:** sources prepared (Window, Floor, AMTail, PV header); not built yet.
