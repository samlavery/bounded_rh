# D track: the defect-energy inequality D(δ). State at pause (2026-10-08)

The D track is paused per the pre-registered rule of the hybrid study (§4.4).

Two rules apply throughout this document:
- Every "fails" is scoped to the named certificate family. Nothing here is a statement about D(δ) itself.
- No novelty claims are made.

## 1. Target and normalisation

**Pair-sum form.**
- Zeros are taken in normalised ordinates u_ρ (mean spacing 1); off-line zeros have complex u.
- Let f be the window profile on [−½, ½] with ∫f = 1. Then qf = f⋆f, supported on [−1, 1], and K = qf^∨ = F² ≥ 0 with F = f̂.
- The energy is E = Σ_{a,b} m_a m_b K(x_a − x_b) = ∫ qf |S|².
- For a configuration closed under conjugation, an off-line pair {s ± iy} enters S as a site with amplitude 2cosh(2παy).

**One-sided convention.** This is the same convention as the compiled skeleton.
- ℰ_T = (‖Â_T‖²_F/N − qf(0))/2 = (1/N)∫₀¹ qf|Ŝ|². This is `edE` in `rootR8f/AMW/DefectEnergy.lean` (bridge-port; standard axioms; D only as the hypothesis `DefectEnergy`).
- The band datum is e∞ = ∫₀¹ qf(α)·α dα = JInf/(2aInf²) = 0.1597839052 (R8). The skeleton matches it to 2.8e-17.

**D(δ).** δ(N − N_s) ≤ N·ℰ_T + o(N). This gives N_s/N ≥ 1 − e∞/δ.
- δ is the one-sided energy per non-simple zero, δ = Δ₁/2N.
- Δ₁ is the minimal grid energy d = Σ_{0<j<N} qf(j/N)|S_j|² of one double in a simple configuration.
- A double's extra self-energy is 2K(0) = 2 (two-sided), so δ ≤ ½.

## 2. Numerical evidence for D

**Single defect (L1).**
- The minimiser is a lattice dipole: the double sits on a lattice site, with a vacancy 2 sites away. It is not a split double.
- R8: Δ₁/N = 0.990793 / 0.990783 / 0.990777 / 0.990774 at N = 24 / 32 / 48 / 64.
- The relaxation lowers the bare dipole by only 0.88 %.
- Locality (periodic N = 64; the double's position is free):

| | bare dipole | +1 | +3 | +5 |
|---|---|---|---|---|
| R8: E/Δ₁ − 1 | 8.8e-3 | 1.5e-3 | 1.2e-4 (98.6 % of the relaxation) | 7e-5 (99.2 %) |
| best window: E/Δ₁ − 1 | 3.2e-2 | 6.3e-3 | — | 99.0 % of the relaxation |

  Here "+K" means the double plus K nearest neighbours per side relaxed.

**δ_true, which includes L2.**
- It is the minimum over every superlattice period N = 3…48, 56, 64, 80 and 96, over clusters of k = 2–5 doubles at N = 64 and 96, and over triples at N = 48.
- R8: δ_true = 0.495338. The lowest ratio is 0.99990 (superlattice N = 5).
- Best window: δ_true = 0.484424. The lowest ratio is 0.99996 (N = 24).

**Off-line pairs and triples (L3).**
- The marked-law LP was re-solved with off-line pairs (depth ≤ ½ and ≤ 3) and triples. They never enter the optimum: the support stays at depth 0, and the value is unchanged at N = 16, 24 and 32.
- The y-Hessian at every double of every optimum is strictly positive: +195 (N = 16) to +324 (N = 32). At the single-defect optimum it is +14.1·Δ₁ (R8) and +14.4·Δ₁ (best window).

**Gabor-sampled Lean object** (`sampled.py`; λ = 1; taper → 0, the worst case).
- Bulk aliasing is exactly 0. This follows from Poisson summation, supp √f ⊂ [−½, ½] and a unit grid step.
- R8, one relaxed dipole: N·ℰ_T(defect) − N·ℰ_T(lattice) = 0.98274 (W = 100) and 0.98679 (W = 200), tending to 0.990774. The deficit is O(1/distance-to-edge), which is o(N) in total.
- R8, far-apart dipoles at W = 400: 0.98808 (k = 2) and 0.98732 (k = 4).
- Best window: 0.96017 / 0.96455 (one dipole), tending to 0.968893.

**Lower side (all simple zeros), ℰ_T ≥ −o(1).**

| W | 50 | 100 | 200 | 300 | 400 |
|---|---|---|---|---|---|
| lattice, no margin | −0.73 | −0.80 | −0.86 | — | −0.92 |
| adversarial minimum | −3.08 | −3.74 | −4.29 | −5.04 | −4.37 |

- The lattice values are about −0.093·ln W; with lattice margins they are −0.06…−0.20.
- The adversarial minimisers are wall piles: near-coincident simple zeros at the window edge. Each pile is bounded by its s²/4 self-energy.
- Net result: −O(log N)/N.

**Band-1 context.**
- Single-window marked LP: about 0.6777 (R8).
- Full band-1 marked LP: 0.682426 (N = 24, typed pricing). The Zeta23 law (LawN256) gives 0.68183.

## 3. Windows

| window | κ (single defect) | κ (δ_true) | δ_true | ∫₀¹qf·α (∫₀¹qf = ½) | δ needed to beat 0.6735 / reach 0.676 |
|---|---|---|---|---|---|
| R8 | 0.677456 | 0.677424 | 0.495338 | 0.159784 | 98.80 % / 99.56 % |
| best verified (smooth 25-mode fit) | 0.680755 | 0.680742 | 0.484424 | 0.154656 | 97.78 % / 98.54 % |

Checks on the best verified window:
- κ_D,N = 0.681269 / 0.681047 / 0.680883 / 0.680826 at N = 24 / 32 / 48 / 64, with Δ₁/N = 0.96889 at every N.
- The typed LP at N = 24 gives 0.681475.

Aggressive windows (L2 fails for these windows):
- The general single-defect optimum reaches 0.681449 on single defects. But defect superlattices at spacings 13–23 are 0.9916× cheaper per defect, so the verified value is about 0.6787.
- The continuum LP window claimed 0.681378. It verifies at 0.679487, because k = 2 clusters at N = 96 are 0.99578× cheaper.
- Grid-N optimisation is unreliable here: it cannot see periods that do not divide N.

## 4. Proof routes and their measured obstructions

### 4.1 Global two-point certificate (Cohn–Elkies / Cohn–Kumar shape)

**Form.**
- Split K = h + g, with g ≥ 0 pointwise (dropped termwise off the diagonal), ĥ = qf − ĝ ≥ 0, and ĝ(0) ≤ g(0).
- Then E − N·qf(0) ≥ g(0)·Σ m(m−1), so δ′ = g(0)/2.
- With ĝ piecewise linear, g(u) = T(u)/(4π²u²) exactly, where T is a periodic trigonometric polynomial. So g ≥ 0 on ℝ is a finite check (`global_cert3.py`).

**Band-limited (ĝ supported in [−1, 1]): exact closed form.**
- Fejér–Riesz plus Cauchy–Schwarz give g(0) ≤ ĝ(0), with equality only for the Fejér kernel. Hence δ′ = ½·inf_α qf(α)/(1 − α).
- R8: 0.343977 (69.4 % of δ_true). Best window: 55.8 %.
- Jointly over all windows: κ_cert = 2/3 exactly.

**With ĝ < 0 beyond the band** (support [−A, A]):

| | A = 1.25 | 1.5 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| R8: δ′/δ_true | 85.2 % | 97.84 % | 97.83 % | 99.04 % (κ_cert 0.67431) | — |
| best window: δ′/δ_true | 70.8 % | 83.6 % | 94.4 % | 95.3 % | 95.51 % (κ 0.6657) |

- Joint optimum over windows and certificates (with K ≥ 0): κ_cert = 0.67452 (A = 2) and 0.67556 (A = 3). The optimal window is close to R8's shape.

**Obstruction for this certificate family: off-line pairs** (`offline_toll.py`).
- The pair's self-block, 2∫ĝ·cosh(4παy), amplifies the dip.
- R8, A = 3 certificate, in a lattice-dipole environment. The pair's certified charge relative to a double is:

| depth y | 0.01 | 0.03 | 0.1 | 0.2 | 0.3 |
|---|---|---|---|---|---|
| charge / double | 1.0003 | 1.0029 | 0.9968 | −0.55 | −38 |

- This is the house strip barrier ("strip wall", RH_LEDGER 034) in the D frame.
- The A = 1 certificate stays ≥ 1 at every depth in that environment, but its termwise step also fails at complex arguments in general.

### 4.2 Local (fixed-range) certificate

**Form.**
- Density 1 gives N = Σ gaps, so E − N·qf(0) = Σ_a [Σ_b m_a m_b K(x_a − x_b) − qf(0)·gap_a] exactly.
- Truncating at range R is a valid lower bound because K ≥ 0.
- The lattice bias t_R is 1.15e-3 (R = 2), 1.9e-4 (R = 3), about 1.2e-4 (R = 4–8) and 3.7e-5 (R = 20).
- The truncated all-simple lower side is exact.

**Obstruction for this certificate family: vacancy delocalisation.**
- The truncated minimiser spreads the vacancy as a uniform dilation of the lattice.
- The full functional charges this through the in-band Bragg peak, at a cost proportional to the spreading length L. The range-R functional sees only about R³/L.
- Measured, best window, from a dilated start:

| R, N | value of δ_R |
|---|---|
| R = 8, N = 64 / 96 / 128 | 0.4097 / 0.4004 / 0.3957 |
| R = 16, N = 256 | 0.4066 (83.9 %) |
| R = 24, N = 256 | 0.4274 (88.2 %) |

- The pre-registered prediction δ_R < 0.45 held.

### 4.3 Hybrid certificate (option (i): on-line points by the dip certificate, off-line points by a PSD form)

**Form.**
- Write E = ∫[S_on; S_off]* Q [S_on; S_off] with Q = qf·[[1, 1], [1, 1]], and split Q = M + G.
  - M(α) is a 2×2 PSD form; it is cosh-safe and bounded below by its DC.
  - G = [[ĝ_on, ĝ_x], [ĝ_x, ĝ_oo]] is termwise. On-on is at real arguments. On-off and off-off require cosh-safety: ∫ĝ·cosh(·)·cos(2παu) ≥ 0 for every depth on the grid [0, y_max].
- The exact first-order conditions are:
  - δ′ = g_on(0)/2 with g_on(0) ≥ ĝ_on(0);
  - each pair at depth y needs ĝ_on(0) − ĝ_x(0) + ∫ĝ_oo·cosh²(2παy) ≥ g_on(0).
- The LP imposes PSD by linear cuts, so its values are upper bounds for the family.

**Measured obstructions for this certificate family** (`hybrid_cert.py`):
- **PSD-only gives zero charge (exact).** Putting every off-line term in the PSD form forces [[qf − ĝ_on, qf], [qf, qf]] ⪰ 0, so ĝ_on ≤ 0 and g_on(0) ≤ 0.
- **Strict cosh-safety at all distances gives zero charge for any y_max ≥ 0.02.**
  - For compactly supported ĝ with kinks, g(u) ~ T(u)/(4π²u²) with T almost periodic and T(0) = 0.
  - With cosh weights, T_y(0) ∝ −y²∫ĝ < 0, so the kernel is negative at arbitrarily large distances.
- **Tails relaxed (cosh-safety only for |u| ≤ 30; optimistic), A = 3:**

| y_max | 0.005 | 0.02 | 0.05 | 0.1 | 0.2 | 0.5 |
|---|---|---|---|---|---|---|
| R8 κ_cert | 0.674515 | 0.674515 | 0.672109 | 0.654501 | 0.504504 | collapses |
| joint κ_cert | 0.675896 | 0.675886 | 0.675486 | 0.669863 | 0.631227 | infeasible |

  - The certified pair charge is ≥ the double's on the grid and negative beyond it in every case. For example, with cap 0.05 the joint certificate gives 0.906 at y = 0.2.
- **Ablation (R8, y_max = 0.1, tails ≤ 30):**

| constraints kept | κ_cert |
|---|---|
| all | 0.654501 |
| without on-off cosh-safety | 0.654552 |
| without off-off cosh-safety | 0.663652 |
| without both | 0.674515 (still 0.673612 at y_max = 0.5) |

  - The barrier is the cosh-weighted CROSS terms at complex arguments, pair-pair (off-off) hardest and on-off next. It is not the pair's own charge.
- Normalised depth 0.05 means β − ½ ≈ 0.3/log T. No unconditional result in anything we have read excludes zeros that shallow.

### 4.4 Decision

- Hybrid pre-registration: κ_cert ≥ 0.6745 with the pair charge ≥ the double's at every depth is NOT met in this family. The outcome is the "≤ 0.6735 everywhere" branch.
- The D track is paused.

## 5. Candidate forward inputs (none attempted)

1. **Off-line block handled spectrally, coupled to the on-line dip certificate.**
   - Zeta23's Sylvester inertia charges off-line pairs at flat charge 4. Its Lemma 3.2 / Prop. 4.4 gives δ = ½ with the DC debt (qf(0) − 1)/2 per point, which is the termwise value 0.672168 on R8.
   - The task is to couple that matrix bound to the dip certificate on the on-line block.
   - This is the house's August open problem ("a configuration-valid counting inequality on the pencil with pair charge 4p", RH_LEDGER 033, memory `cgdl-transplant-three-walls`), now sharpened. The gap to close is the cosh-weighted on/off and pair-pair cross terms of §4.3.
2. **Three-point / SDP certificates** (Cohn–de Laat–Salmon type), which go beyond the two-point family of §4.1–4.3.
3. **An unconditional near-line depth cap.** About 0.05 in normalised depth, i.e. β − ½ ≲ 0.3/log T for all but o(N) zeros. It is not available in anything we have read; Selberg-type density decays only like e^{−cy}.

## 6. Files (all in `bench/window/band1/`)

- **Marked LP and realisation:**
  - `marked_lp.py`, `marked_lp_window.py`, `marked_N*.log`, `marked_window*.log`
  - `realise.py`, `realise_check.py`, `realise_N*.log`, `realise_deep.log`, `realise_*.json`
- **Window optimisation:**
  - `winopt.py` and helpers (`winopt_smoothfit.py`, `winopt_famopt*.py`, `winopt_robust.py`, `winopt_final.py`, `winopt_l2.py`, `winopt_stab.py`, `winopt_superlat.py`, `winopt_cont.py`, `winopt_verify*.py`), with matching logs and JSON.
  - Verified numbers: `winopt_verify2.log`.
  - Best window: `winopt_smoothfit_single_N24.json`.
  - L2 failures: `winopt_superlat.log`, `winopt_stab_allc1_N24.log`, `winopt_verify.log`.
  - Far field: `winopt_far_R8.log`, `winopt_far_smoothfit.log`.
- **Gabor-sampled object and lower side:** `sampled.py`, `sampled_lower.py`, `sampled_R8.log`, `sampled_best.log`, `sampled_lower_R8.log`.
- **Global certificate:**
  - `global_cert3.py` (the exact LP), `global_cert3_wide.py`, `global_joint.py`
  - logs `global_cert3_*.log`, `global_joint.log`; knot values `global_cert3_*.json`
  - superseded: `global_cert.py` (closed form plus an invalid B-spline LP) and `global_cert2.py` (incomplete far-field positivity)
- **Off-line toll:** `offline_toll.py`, `offline_toll.log`.
- **Local route:** `local_route.py`, `local_route_best.log`, `local_route_probe.log`, `local_route_volume.log`, `local_refute.py`, `local_refute.log`.
- **Hybrid:** `hybrid_cert.py`, `hybrid_cert.log`, `hybrid_cert_notail.log`, `hybrid_cert_diag.log`, `hybrid_*.json`.
- **Source read:** `cgdl_1810.08843.pdf` / `.txt` (Chirre–Gonçalves–de Laat, arXiv 1810.08843v2).
- **Lean skeleton (bridge-port):** `bench/window/rootR8f/AMW/DefectEnergy.lean`.

---

# Update 2026-10-08: D track RESUMED via the projection route (Lemma P)

Lean build state lives in `bench/window/rootR8f/AMW/DE_LEAN_STATE.md` (bridge-port). Every "fails" below is scoped to its certificate
family or method. No novelty claims.

## Construction

- D(Z) replaces each off-line pair s ± iy by an on-line double at s. Exactly, E(Z) = E(D(Z)) + Δ_B, where Δ_B uses only qf ≥ 0
  (the pair amplitude is 2cosh = 2 + B_y).
- The dip certificate applies only to D(Z), at real arguments, so the cosh never meets the dip.
- The certified bound is COUNT-ONLY: F_C(D) = ĥ(0)N + g(0)Σm². So **Lemma P** (E(Z) ≥ F_C(D(Z)) for all Z) is equivalent to D(δ′)
  with pairs counted as defects.
- Canonical certificate: **v1**, `cert_R8_backed.json` (exact rationals over 2⁴⁰; m_C = m_h = 2e-5; σ = ĝ(0) − g(0) = 1.367e-3 > 0,
  charged per point), **κ_cert = 0.6759645**.
  - σ > 0 is forced (proved): Poisson plus ĝ(m) ≤ 0 at m ≥ 1 make ĝ(0) ≤ g(0) force C = 0 at 2πn/32.
  - am-cert has certified v1 in Lean: cR8, certG_R8 (C ≥ 9.73e-6), and ghat0_sub_g0_R8 (σ exact).
  - v2 (`cert_R8_backed_v2.json`, m_h = 5e-5, κ 0.6759520) is an alternate; nothing builds on it.

## Numerical status of Lemma P

- Worst W per defect = +0.00319 × 2δ′, at depth 0 (N = 24/32/48; dense defect counts included).
- Δ_B < 0 occurs only with slack ≥ 2.2 × 2δ′.
- Slack-relative form: the per-pair form W ≥ θΣR_p FAILS (coherent deep clusters, θ → 0.007); the collective form W ≥ θ·R_coll
  holds with θ ≥ 0.45, and R_coll ~ cosh²/y².

## Field form (single pair)

LP(D, y) = s(D) + ∫qf·B_y² + 2Σ_{b∈D} m_b·L_y(x_b − s) ≥ 0, for real D with a double at s.

The curvature–slack framing (V″ ≤ −c₀ at low slack) is FALSE as posed: 17 packed doubles give slack 0.42 with V″ = −0.495.

| step | content | status |
|---|---|---|
| 1 | exact identities; Poisson at any spacing: Σ_n L(na) = (1/a)Σ_m (qf·B)(m/a) ≥ 0 | PROVED |
| 2 | on-lattice core, masses ≤ 2: LP ≥ Ψ(y) = ∫qf·B² − 4Σ_{n≠0} L_y(n)⁺, using no slack. **CORRECTED:** L_y(n) < 0 for every n ≠ 0 only for y < y_s = **1.141924** (not 1.4); beyond y_s, Ψ ≥ 0.9995·∫qf·B². Certificate: series for y ≤ 0.1; about 610 Lipschitz cells on [0.1, 0.8]; magnitude check for y ≥ 0.8 (≥ 9.5×); about 700 cells in total | PROVED modulo the cell check (sized) |
| 3 | cluster bound: g decreasing on [0, 0.9]; g(¼, ½, ¾) = 0.829, 0.439, 0.122 | PROVED, plus a 1D check |
| 4 | nearest-neighbour strain: g″(1) = 2.3757, d* = 1.0227 (the offset is the σ slack) | PROVED, plus a check of g‴ |
| 5 | near-lattice perturbation: ρ(y) = ∫qf·B²·g″(1)/ΣL² ≥ 22.18 for all y | PLAUSIBLE, constants explicit |
| 6 | far field: \|L_y(u)\| ≤ C_L(y)/u² | PROVED |
| 7 | high-cost regime (clusters, deep pairs) | PROVED |
| 8 | arbitrary gap sequences | see below |
| 9 | coherent deep clusters (y > y_s): W/R_coll ≥ 0.9987 for P ≤ 8 at spacing 1.5; ‖S_B‖ saturates in P; the cluster saturation lemma (9e) is with bridge-port | PLAUSIBLE |

Step 8 detail:
- The coarse certified chain DP (h = 1/32, X = 24) is ≥ 0 at y = 0.5, 1.0, 1.4 and negative at y ≤ 0.3 and y = 0.7.
- Those negatives are method artefacts: the exact LP on the binding chains is positive.
  - The DP dropped P_h and the density constraint, which made "doubles on every site" look tight at O(y⁴).
  - Nearest-neighbour costs miss the quadratic cost of clusters.
- y ≳ 0.4 is certifiable once the DP charges clusters quadratically.

## Shallow-depth defect gap (2026-10-08; `defect_gap.py`, `defect_gap2.py`)

- WITH the full slack, LP = s(D) + y²·Q₂(D) + R₄, where:
  - Q₂ = −2V″_D(s) = 4|K″(0)| − 2Σ_env m_b·K″(x_b), with K″(0) = −6.05;
  - R₄/y⁴ ≈ (4/3)K⁽⁴⁾(0) + (1/6)Σ_env m·K⁽⁴⁾ (K⁽⁴⁾(0) = 89.4; on a lattice ≥ 90.3).
- On a lattice Q₂ = 2Σ_{n≠0}(1 − m_n)·K″(n) ≥ 0. A packed-doubles block of radius R has Q₂ ~ 1/R but slack ~ 0.05R, so its LP is
  O(y), not O(y⁴).
- Adversarial results (N = 48, y ∈ [0.03, 0.3]):
  - global min LP/y² = 18.1 (relaxed dipole, y = 0.2);
  - with one environment point pinned off-lattice (c = 0.5, 0.75, 1.25, 1.5, 2.5): min LP/y² = 27.8;
  - no family with LP/y² → 0 was found.
- Q₂ < 0 occurs at moderate slack with several doubles CROWDING s at about ±0.8. That is where K″ peaks: K″(0.79) = 3.53 > K″(1) = 2.15.
  - −Q₂/s ≲ 6.2, so the second order alone covers y ≤ 0.40.
  - The full LP stays positive there: ≥ 0.48 at y = 0.1, and direct minimisation from these configurations gives ≥ 1.15 / 3.48 / 10.9 at y = 0.3 / 0.4 / 0.5.
- Open step: the CROWDING REGIME. Environment points within about 2 of s are displaced by δ ∈ [δ₀, ½] off their sites; the curvature gain
  2m·ΔK″ is paid by 4m·g(x) (pair with the double at s), about 7.9× at u = 0.79.
  - This is a LOCAL, low-dimensional problem (≤ 4 points per side plus masses), reducible to a finite certified branch-and-bound. Not yet run.
  - Small displacements (δ < δ₀) enter only at y⁴ (relaxation penalty ≈ ∫qf·B²/ρ ≈ 4y⁴ ≪ R₄ ≈ 90y⁴).

## New files

- `cert_backed.py`, `cert_R8_backed.json` (v1, canonical), `cert_R8_backed_v2.json`;
- `lemmaP*.py` and logs; `lemmaP_rel.py`; `lemmaP_chain.py`; `curv_slack.py`; `gabor_check.py`;
- `stability_sketch*.py`; `chain_dp.py`, `chain_check.py`; `step9_stepC.py`; `stepC2.py`, `stepC3.py`;
  `defect_gap.py`, `defect_gap2.py`; with logs.

## Step d certified (2026-10-08; `crowd_dp.py`, logs `crowd_dp_X128_NY32.log`, `crowd_check.log`, `crowd_sound.log`, `crowd_dp_deep.log`)

**Bound used.** In the line model, LP(D, y) = P_h + T_g + 2[K(2iy) − K(0)] + Σ_env m_b·φ_y(u_b), with φ_y = 4[Re K(u+iy) − K(u)].
- Drop P_h ≥ 0, the cross-side environment pairs, and the non-consecutive same-side pairs (g ≥ 0, from the certified C ≥ m_C).
- This leaves LP/y² ≥ S0(y) + V_R + V_L.
- V_side is a nearest-neighbour chain: one-body m·ψ_y(u) + 4m·g(u)/y², and bonds 2mm′·g(Δu)/y².

**Method.**
- Exact backward DP (shortest path over ordered position cells, with positive same-cell loops) on (0, 128].
- Cells:
  - 1/256 on [0, 5], 1/128 to 16, 1/64 to 48, 1/32 to 128;
  - 7296 cells per side; masses {1, 2}.
- Cell lower bounds by second-derivative bounds on tabulated functions:
  - ψ via its Taylor coefficients c_j in t = y² (J = 9, remainder bounded);
  - g from its exact trigonometric form, with |g″| ≤ 7.73 taken from the ĝ knots;
  - pair terms take the minimum of g over the full distance range between the two cells.
- 1/y² is taken at y_hi and S0 at y_lo. There are 32 y-intervals of width 0.0125 covering (0, 0.4].
- Tail beyond X = 128: |ψ| ≤ A₂/u² + A₃/u³ (three integrations by parts); a unit bin with ≥ 2 points pays k(k−1)·min_{[0,1]}g/y².
- Crowding flag for the class C(R, δ₀): a point in the window (0, R+½] outside every site window [n−δ₀, n+δ₀], or two points in one site window. Bound: S0 + V_free + V_crowd.

**Results (certified lower bounds of LP/y², y ∈ (0, 0.4]).**

| class | full slack | slack localised to [0, 8] |
|---|---|---|
| ALL real D (no class restriction) | **1.953** (binding y ∈ [0.1625, 0.175]) | **1.379** |
| crowding R=2, δ₀ = 0.1016 / 0.1484 / 0.2031 | 2.874 / 4.333 / 6.137 | 2.379 / 3.900 / 5.720 |
| crowding R=3, δ₀ = 0.1016 / 0.1484 / 0.2031 | 2.820 / 3.682 / 4.518 | 2.371 / 3.257 / 4.091 |
| crowding R=4, δ₀ = 0.1016 / 0.1484 / 0.2031 | 2.500 / 2.805 / 3.252 | 2.026 / 2.362 / 2.835 |

- Runtime: about 2.5 s per y-interval and slack variant; 324 s in total (single thread, nice 10).
- No refinement was needed: every cell bound is positive.

**Checks.**
- Field form vs periodic Δ_B: identical (N = 64).
- slack = P_h + T_g: exact through ĝ; the image sum converges to it.
- ψ and S0 normalisation vs periodic N = 2048: 3.6e-6.
- Quadrature, 600 vs 1000 nodes: 1.6e-12.
- Tail constants vs exact ψ on [X, X+40]: ratio ≤ 0.935.
- Heuristic minima of the same relaxed objective (4.68–16.3 for y ∈ [0.05, 0.4]) stay above the DP bound, so no unsoundness was detected.
- Exact all-pairs objective on the binding chains: 11–20 at y ∈ [0.2, 0.25].

**Status.**
- PROVED, computer-assisted, double precision with explicit allowances (EPS = 1e-8 per tabulated value). It is NOT yet interval arithmetic; the tail constants come from finite differences × 1.05, checked against exact ψ.
- The all-D bound means that for the single-pair statement on (0, 0.4] the near-lattice branch (step c, ρ) and the off-lattice R₄ bound (step e) are no longer needed: LP(D, y) ≥ 1.95·y² for every real D with masses ≤ 2.

**Limits.**
- Line model only; the periodic model needs image control.
- The bound draws on T_g within distance 128 of s, or within 8 for the localised variant. Configurations with many pairs need a slack-sharing argument (step 9 territory).
- Beyond y ≈ 0.475 the nearest-neighbour relaxation's same-cell loops turn negative (clusters), so a cluster-aware DP (second-neighbour state) is required there. Certified values above 0.4: [0.40, 0.425] → 12.5, [0.425, 0.45] → 16.1, [0.45, 0.475] → 20.6.

## Interface with step 9(e) (bridge-port), 2026-10-08 (`crowd_share.py`, `crowd_share.log`)

**Certified range.** Step 8 (single pair, all real D) is certified for y ∈ (0, 0.475]. The step-8 side of y₁ is therefore ≤ 0.475 unless the DP is extended with a cluster-aware state.

**Diagonal consumption.** The single-pair bound consumes up to 0.60 of the pair's own ∫qf·B_y² (y ∈ [0.14, 0.4]); 0.67 when the slack is localised to ±8. With only half the local T_g, the bound is −0.63y² on [0.125, 0.25].
- Consequence: in any configuration with ≥ 2 pairs, each shallow pair needs about 0.6–0.7 of its diagonal from the joint form ∫qf|Σ_p B_p e(α s_p)|². That form also carries the cross terms ≈ 2·y_p²·y_q²·K⁽⁴⁾(d), with K⁽⁴⁾(1) = −12.58.
- This multi-pair item (shallow+shallow and shallow+deep) is covered by neither step 8 nor step 9(e) yet.

**Slack split proposed.**
- Step 8: T_g within ±8 of each shallow pair, plus cluster pairs.
- Step 9(e): all of P_h, plus T_g elsewhere.
- An overlap rule is still needed for when a deep pair sits within 8 of a shallow pair.

All of these numbers come from the nearest-neighbour relaxation, which is about 2× loose against heuristic minima.

## Single-pair Lemma P for ALL y (2026-10-08)

Certificate v1, line model, one off-line pair, any real D with masses ≤ 2. P_h is never used.
Logs: `crowd_dp_X128_NY32.log`, `crowd_dp2_04_10.log`, `deep_cert_06_12.log`, `deep_asym_Y12.log`.

| y range | instrument | certified bound |
|---|---|---|
| (0, 0.4] | nearest-neighbour chain DP (`crowd_dp.py`) | LP ≥ 1.953·y² |
| [0.4, 0.9375] | chain DP with cluster charge (`crowd_dp2.py`): non-consecutive pairs in a half bin pay g(½), state carries prior mass (cap 24) | LP ≥ 13.65·y² |
| [0.6, 12] | half-bin bound, no DP (`deep_cert.py`): LP ≥ self − Σ_bins max(2Φ, a(1+Φ/2a)²); (u, y) grid 1/512 × 0.002 with bilinear-corner error bounds | LP ≥ 0.0527·self(y) |
| [10, ∞) | half-bin bound, analytic (`deep_asym.py`): \|φ\| ≤ min(Λ, E(τ₂/u² + τ₃/u³)), bins split at V = 2.5y, every term of R(y) decreasing | LP ≥ 0.483·self(y) (≥ 0.568·self for y ≥ 12) |

- Here self(y) = 2[K(2iy) − K(0)] = S0(y)·y².
- **Handoff:** y_deep = 0.8, inside the overlap [0.6, 0.9375]. At 0.8 the DP gives LP/y² ≥ 241 and the half-bin bound gives LP ≥ 0.208·self.
- **Status:** single-pair Lemma P is PROVED for every y > 0, computer-assisted, in double precision with allowances. The tail and qf constants come from finite differences × 1.05. It is NOT interval arithmetic.

**Rigour upgrade, sized only (not run).**
- Replace every quadrature with the closed form K = F², with F(z) = (1/A)Σ_i z_i[sin((w_i − 2πz)/2)/(w_i − 2πz) + sin((w_i + 2πz)/2)/(w_i + 2πz)]. Checked: K(0) = F(0)² = 1 in mpmath.iv.
- Measured cost: mpmath.iv takes about 1 ms per real F evaluation, about 3 ms complex.
- Estimates:
  - DP cell bounds (≈ 5.6e5 evaluations): ≈ 1 h;
  - g block minima (1.3e5): ≈ 10 min;
  - analytic constants: seconds;
  - deep half-bin certificate: has to be restructured to coarser cells with second-order bounds (≈ 5e6 evaluations) ≈ 4 h with mpmath.iv, or minutes with python-flint/arb. python-flint is not installed; installing it is an environment change.
  - DP floating-point sums: a written error budget (n·u·Σ|terms| ≤ 1e-9) is enough.
- Coding: about a day.

**Multi-pair shallow (`multipair_dense.py`, `multipair_dense.log`; periodic N = 64; a block of P equal-depth pairs on consecutive sites).**

LP_total per pair / y², relaxed:

| y | P = 1 | P = 2 | P = 4 | P = 8 | P = 16 |
|---|---|---|---|---|---|
| 0.4 | 35.6 | 13.3 | 7.3 | 4.0 | 2.3 |
| 0.2 | 18.6 | 11.3 | 7.0 | 4.5 | 3.0 |

- The block total stays about 5 at y = 0.4: the margin is an edge effect, not a per-pair one.
- Mechanism: inside a block, each pair's field on the doubles lattice cancels (Poisson: Σ_n L_y(n + t) = 0), and the B–B form ∫qf|Σ_p B_p e(α s_p)|² grows only like log P.
- Consequence: per-pair single bounds cannot be summed, and the diagonal that the single-pair bound consumes (60–67%) is not given back inside blocks.
- Sketch:
  - (i) well-separated pairs (gaps ≥ 16): localised single-pair bounds plus explicit |X_pq| ≤ C·y_p²·y_q²/d² tails close it; cluster charges need a disjoint allocation;
  - (ii) bounded clusters of k ≤ 2–3 pairs: a joint B&B over (relative positions, depths) × a DP with the summed field and the exact cluster B–B form;
  - (iii) long blocks: a bulk + edge decomposition, with the bulk given exactly by the Poisson identities (bridge-port's equal-depth identity ‖S_B‖² + 2Re⟨S_pairs, S_B⟩ = ∫qf(B² + 4B)|V|² is the bulk form for equal depths) and only the edges certified.
- A cell-discretised DP over a long block would accumulate errors ∝ P against an O(1) margin, so the bulk has to be analytic.

## Step 8 under the slack convention; multi-pair shallow extremes (2026-10-08)

**Step 8 with slack localised to ±8 of s** (the accepted convention: local T_g to step 8; P_h and all other T_g to 9(e)).
- (0, 0.4]: LP ≥ 1.379·y² (`crowd_dp.py`).
- [0.4, 0.8]: LP ≥ 13.36·y² (`crowd_dp2.py 0.4 0.8 32 24 8`; log `crowd_dp2_04_08_loc8.log`).
- At y₁ = 0.8 (interval [0.7875, 0.8]): LP/y² ≥ 223.3.
- Cluster parts (bonds shorter than ½, and the half-bin charges) are kept anywhere.

**Multi-pair extremes** (`multipair_dense2.py`, `multipair_denseN.py`, `multipair_restart.py`; periodic; certificate v1; all positions relaxed).

Every tested case is POSITIVE per defect. Worst W/defect, in units of 2δ′:
- dense equal-depth block, N = 128, 64 pairs:
  - +0.0404 at y = 0.2;
  - +0.0921 at y = 0.4;
  - 8 restarts give the same minimum.
- N = 64 block of 32 pairs: +0.0565 (y = 0.2), +0.153 (y = 0.4).
- All mass in pairs (spacing 2): ≥ +0.107.
- Mixed shallow/deep (alternating 1.0 / 1.5, or one deep pair in a shallow block): ≥ +5.2. The deep B-diagonal dominates; fields go down to −70 per defect.

**What pays in the dense extreme** (per defect, y = 0.4, contiguous vacancies):

| N (block size) | P_h | T_g | fields | B–B |
|---|---|---|---|---|
| 32 (16) | 0.048 | 0.047 | 0.106 | 0.061 |
| 64 (32) | 0.040 | 0.027 | 0.054 | 0.032 |
| 128 (64) | 0.031 | 0.017 | 0.027 | 0.017 |

- The non-P_h part decays like about 1/P. Its block total stays ≈ 3.4–3.9, an edge effect: inside the block the fields cancel by Poisson and the B–B form grows only like log P.
- P_h gives an extensive density floor of ≈ 0.02–0.03 per defect, from ĥ(0) = qf(0) − ĝ(0) = 0.0165 > 0, the cost of a density-2 block.
- **Correction** to the earlier "per-pair margin → 0 like 1/P": that holds for the non-P_h part only. With P_h, the per-defect margin saturates at the density floor.

**Slack-sharing statement for shallow pairs** (proposed; status: (i) certified, the rest plausible / numerical).
- Cluster the shallow pairs by |s_p − s_q| < 16, with window W_C = [min s − 8, max s + 8].
- (i) Isolated pair: T_g(W_C) + F_p + ∫qf·B_p² ≥ 1.379·y_p² (y ≤ 0.4) and ≥ 13.36·y_p² (0.4 ≤ y ≤ 0.8). CERTIFIED (single-pair).
- (ii) Cluster of ≥ 2 pairs: T_g(W_C) + Σ_{p∈C} F_p + ‖Σ_{p∈C} B_p e_p‖²_qf ≥ m_C > 0, with m_C = O(1) per cluster (an edge effect), NOT per pair. Numerical.
- (iii) Between clusters: |X_pq| ≤ C·y_p²·y_q²/d², with d ≥ 16, absorbed by the cluster margins. Sketch.
- (iv) P_h is not needed for W ≥ 0 in any tested shallow case. It is needed only if per-defect margins are required in dense shallow blocks; that is the one case where the convention would have to be revisited.
- (v) Deep pairs in a cluster: their B-diagonal dominates.
- Untested: unequal shallow depths inside a block; non-lattice block geometries beyond local relaxation.
- What a proof needs: the cluster B&B for k ≤ 2–3 pairs, plus a bulk identity (Poisson; bridge-port's equal-depth (B² + 4B)|V|² form) with only the edges certified for long blocks.

## Multi-pair (shallow) program (2026-10-08)

**Exact decomposition.**
LP_total = P_h + T_g + Σ_p self_p + Σ_p Σ_env m_b·φ_p(x_b − s_p) + Σ_{p≠q} [2φ_p(s_q − s_p) + X_pq]
- self_p = 2[K(2iy_p) − K(0)];
- X_pq = ∫qf·B_p·B_q·cos(2π α (s_p − s_q)).
- The pair part self + Σ[2φ + X] equals ∫qf(|Σ_p A_p e_p|² − |Σ_p 2e_p|²), with A_p = 2cosh(2π α y_p). For equal depths this is ∫qf(B² + 4B)|V|² ≥ 0 (bridge-port).

**(i) Separated pairs, CLOSED for all-shallow configurations** (`crowd_dp3.py`, `crowd_dp3_00_08.log`, `sep_xlemma.py`, `sep_xlemma_D32.log`).
- Setting: centres pairwise ≥ 32 apart; depths ≤ 0.8.
- Slack allocation is a partition of unity. Pair p uses:
  - non-cluster T_g only inside its window (|u| ≤ 8);
  - cluster parts with weight 0.9 inside the window and 0.4(8/u)² outside.
  - These weights sum to ≤ 0.9934 at every point for any 32-separated set (checked).
- Allocated single-pair DP: LP_p ≥ 1.3787·y_p² on (0, 0.8] (binding y ∈ [0.15, 0.1625]).
- The B–B cross terms 2X_pq are charged to the deeper pair: |X_pq| ≤ 2[|r′(1)|/(2πd)² + (|r″(1)| + ∫|r‴|)/(2πd)³], with r = qf·B_p·B_q, and the charge per y_q² is monotone in depth. The charge is ≤ 0.0042 / 0.021 / 0.17 / 9.4 (×y_q²) at y = 0.1 / 0.2 / 0.4 / 0.8, against margins 1.9 / 1.5 / 11.8 / 188.
- min(margin − charge) = +1.37 y² > 0. **Total W ≥ 0 certified on class (i)** (computer-assisted, double precision).
- Mixed separated configurations (shallow next to deep, y > 0.8): the deep half-bin bound needs the same cluster-weight allocation. A deep pair's field reaches out to distance ~y, so "separated" must scale like d₀ ≳ y for deep pairs. That is bridge-port's side.

**Concavity reduction for clusters — this INSTRUMENT does not close.**
- The method: V(Σ_p φ_p) ≥ Σ_p λ_p V(φ_p/λ_p) − (pair-on-double terms), which reduces any cluster to single-pair DPs with an amplified field μ = 1/λ. Exact and geometry-free.
- Result: the amplification loss is too large (`cluster_dp.py`, `cluster_dp_coarse.log`; m(y, μ) = S0 + 2V(μψ)/μ). At y ∈ [0.1, 0.15], μ = 1 / 1.5 / 2 / 3 give +0.27 / −0.62 / −1.35 / −2.49 (coarse y-grid). Beyond y ≈ 0.45, μ ≥ 1.5 turns strongly negative because the cluster response is superlinear.
- This is a property of the concavity bound, which replaces two spatially separated fields by a coherent one. It is not a property of the configurations.

**Small slack windows:** a single-pair DP with slack window 2 (full cluster weights) still gives +1.157y² (fine grid, binding [0.1375, 0.15]). So a partition of unity with d₀ ≈ 4 is plausible for pairs whose nearest neighbour is ≥ 4 away. It needs exact X(d) for d ∈ [4, 64].

**Close clusters / dense blocks** (pairs within ≈ 4 of each other).
- Per-pair bounds cannot work there. Poisson cancels the B-diagonal that the single-pair bound needs (60–67%): for a dense equal-depth block, Σ_q X(p − q) ≈ −∫qf·B² per pair.
- So the route is the joint form ‖S_B‖² + 4Re⟨S_B, V⟩ (bridge-port), evaluated exactly in the bulk, plus a certified edge.
- The dense numerics put the true P_h-free per-defect margin at about 0.019·2δ′ at y = 0.2, N = 128. That is below the typical DP looseness (×2–3), so a P_h (density) lower bound will probably be needed for long blocks.
- Joint DP over cluster geometry boxes (k = 2): d-boxes ≲ 0.003 wide are needed (box looseness ≈ 200 y²·Δd), giving ≳ 10⁶ DPs. Infeasible, and far too large as a board certificate. This is a cost estimate for that instrument.

**(iii) first case: exact-lattice equal-depth blocks** (`block_dp.py`, `block_dp_coarse.log`; y-grid 0.05).
- Pairs at sites 0..P−1. LP_total ≥ Q_pp + T_g + Σ_env m·Φ_P, with:
  - Q_pp = ∫qf(B² + 4B)·sin²(πPα)/sin²(πα), exact and increasing in y after dividing by y²;
  - block field Φ_P = Σ_j φ(· − j);
  - the edge environment by the cluster-charged DP with the block field (cells shifted by integers);
  - interstitials paying 4m[g(t) + g(1 − t)], with a half-gap cluster correction where they are profitable (y ≥ 0.55);
  - block bonds 8g(1)(P − 1).
- Certified lower bounds of LP_total/y² on (0, 0.8]:

| P | 1 | 2 | 4 | 8 | 16 | 32 |
|---|---|---|---|---|---|---|
| LP_total/y² ≥ | 0.16 | 1.74 | 3.28 | 5.52 | 9.17 | 15.18 |

  - P = 1 is the coarse-grid single pair; the fine grid gives 1.95.
  - Per pair this falls to ≈ 0.47 at P = 32, and the total grows. Q_pp/y² grows like c·log₂P: +8.7 per doubling at y = 0.1, +45 at y = 0.4.
- P → ∞: Q_pp(P + 1) − Q_pp(P) = ∫qf(B² + 4B)·D_P (Dirichlet kernel) = −2Σ_{k>P} w_k, and w_k = 2h′(1)/(2πk)² + O(k⁻³) with h′(1) = qf′(1)(B² + 4B)(1) < 0. So the increments are positive for P ≥ P₀ (explicit constant). Then one DP with the half-infinite block field (tail-bounded) covers all P ≥ P₀. Not yet run.
- CAVEAT: this is a slice. Relaxed dense configurations sit far below the exact lattice: N = 64, P = 32, y = 0.4 gives W/defect 0.613 on the lattice against 0.153 relaxed. General block geometry, with displacements and unequal depths, is the open core. A geometry-robust method is needed (pairs as chain points with long-range, Poisson-cancelling couplings).

**Multiplicity convention (bridge-port, 2026-10-09).**
- The Lean ordSq groups zeros by ordinate. lemmaP.py counts each pair as its own double (R convention).
- My certified statements (single pair for all y, step 8, class (i)) hold under ordSq too, for on-line zeros exactly at a pair's ordinate. With D′ = D + m at s: LP_ord(D′) ≥ Obj_R(D) + m·φ_y(0), and φ_y(0) = 4∫qf(cosh(2παy) − 1) > 0. The P_h-free DP bound covers Obj_R(D) over all D.
- Coincident pairs (stacks) are outside my classes. Bridge-port finds LP_ordSq < 0 for deep stacks with m ≥ 12, while the R convention stays positive. He proposes per-zero weights (mult² on the line, 2·mult off the line); that is the lead's decision.
- Caveat (bridge-port): in clusters or blocks, an on-line zero exactly at s_p also feels the other pairs' fields φ_{y_q}(s_p − s_q), which can be negative. So the "only gains" argument does NOT extend to (ii) and (iii) under ordSq. It does hold under the per-zero weights.
- Per-pair split test (bridge-port, `sat9/e18_theta.py`): the split Q_pp ≥ θ·Σself − c·T_g (c ≤ 1) has θ_max ≈ 0.3–0.4 for two pairs at d ≈ 0.7, and θ_max falls like 1/P on compressed chains.
  - The single-pair DP needs θ ≥ 1 − margin/self ≈ 0.93–0.95 at y ≈ 0.17 (full-self normalisation; "60–67%" was the fraction of the B²-diagonal only).
  - So the PER-PAIR route is closed, as an instrument. The failures are compressed (density-excess) configurations, so a joint environment pricing is needed: identity (c) LP = s(D) + ‖S_B‖² + 2Re⟨S_D, S_B⟩, or a joint DP on compressed clusters, plausibly with P_h.
  - Natural-density blocks (spacing 2) have θ_∞ ≥ 0.6 for y ≤ 0.4.

**Joint environment DP at the hardest known shallow geometries** (2026-10-09; `multipair_geoms.py` → `multipair_geoms.json`; `multi_env_dp.py`).
- Bound: LP_total ≥ Q_pp (exact) + T_pp (pair doubles) + V_env (chain DP, one-body = summed field of all pairs + their T_g) + tails. P_h dropped. Line model.
- Sanity checks:
  - single pair: 2.04y² (y = 0.17) and 15.0y² (y = 0.4);
  - exact lattice of 16 pairs: 17.1y² (y = 0.2) and 131y² (y = 0.4), consistent with `block_dp.py`.
- Relaxed periodic minimisers (pair spacings 0.84–0.99, slightly compressed), X = 128 past the cluster, cells 1/256 near pairs; 1/1024 changes < 0.02:

| geometry | P_h-free DP bound | exact periodic LP | P_h in it |
|---|---|---|---|
| block16, Y = 0.2 | −0.265 | +2.32 | 0.86 |
| block16, Y = 0.4 | −0.95 | +7.20 | 1.71 |
| comp8, Y = 0.4 | −0.023 | +1.57 | 0.53 |
| comp8, Y = 0.2 | +0.045 | +0.53 | 0.24 |
| comp4, Y = 0.4 | +0.81 | +2.52 | 0.23 |

- Diagnosis: compressing a block by ~3% moves the spectral peak of V = Σ e(α s_p) from α = 1 to 1/a > 1, outside the support of qf. Q_pp loses its log-P growth (block16, Y = 0.2: 3.10 on the lattice vs 1.75 relaxed) at a T_g cost of only 0.23.
- The line-model environment, which has no density constraint once P_h is dropped, then responds with excess mass. In the true problem P_h pays for that excess (≈ 0.5–1.7 here).
- **Encountered block (this instrument): the P_h-free joint DP does NOT certify compressed dense blocks.** A density ingredient is needed: P_h ≥ ∫ĥ_low|S_D − Nδ_0|² = ‖k * (ρ − 1)‖² with k̂ = √ĥ_low, scale ~16 (ĥ ≈ 0.0165 at 0, ≈ 0 beyond α ≈ 1/8). Making it local and DP-compatible is open: it is mesoscopic and two-body at range ~16, and coarse-graining loses ~c/16 per unit length, against σ ≈ 1.4e-3.

## Density lemma and the joint DP (2026-10-09)

**Density lemma (pencil, exact).** Periodic model, total mass N, P_h(D) = (1/N)Σ_{j≠0} ĥ(j/N)|S_j|² with ĥ ≥ 0.
- Statement: for any real test function v with mean zero and Fourier coefficients c_j supported where ĥ > 0,
  P_h(D) ≥ 2Σ_a m_a v(x_a) − (1/N)Σ_{j≠0} |c_j|²/ĥ(j/N).
- Proof: termwise, ĥ|S|² ≥ 2Re(c̄S) − |c|²/ĥ, since |ĥS − c|² ≥ 0; then (1/N)Σ c̄_j S_j = Σ_a m_a v(x_a). ∎
- It enters the DP as a one-body potential 2v per unit mass plus a constant. No new DP state; the certificate's data are the test-function parameters.

**Instances used.**
- (L) Low band: v = t_L(w − ∫w/N), with w = 1_R * β sinc²(β·) ≥ 0, R = cluster ± XR, β = 1/32.
  - P_h ≥ 2t_L(Σ m w − ∫w) − t_L²·Q_L, with Q_L = ∫|ŵ|²/ĥ.
  - Environment beyond the DP range adds 2t_L·m·w ≥ 0, which is dropped.
- (B) Band beyond α = 1 (where ĥ = −ĝ ≈ 0.0075–0.0086 on [1.03, 1.13]): v = t_B·(ĥ_W·Ŝ_pairs)^∨, with W = 0 for |α| ≤ ½, a ramp to 1 at ¾.
  - P_h ≥ 4t_B·Σ_env m·Σ_p h_W(x − s_p) + 4(2t_B − t_B²)·Σ_{p,q} h_W(s_p − s_q).
  - Where P_h sits in compressed blocks: ≈ 45–65% in |α| ∈ (1, 3] (the compressed Bragg peak moves into ĥ's band beyond 1), 10–60% at |α| ≤ 1/16.

**Pre-registered rerun** (`multi_env_dp.py` with MEDP_T = 0.5 and per-geometry (XR, t_L, XL); logs `multi_env_dp_density_certs.log`, `multi_env_dp_scan5.log`, `multi_env_dp_b64scan.log`).

| geometry | P_h-free | with density lemma | exact LP | exact P_h |
|---|---|---|---|---|
| block16, Y = 0.2 | −0.265 | **+0.143** (XR = 20, t_L = .005) | 2.32 | 0.86 |
| block16, Y = 0.4 | −0.952 | **+0.273** | 7.20 | 1.71 |
| comp8, Y = 0.4 | −0.023 | **+0.424** | 1.57 | 0.53 |
| comp8, Y = 0.2 | +0.045 | **+0.113** (XR = 10) | 0.53 | 0.24 |
| comp4, Y = 0.4 | +0.812 | **+1.227** | 2.52 | 0.23 |
| block32, Y = 0.4 | — | **+0.191** (XR = 10, XL = 512) | 9.68 | 2.52 |
| block64, Y = 0.2 | — | **+0.761** (XR = 20, t_L = .008, XL = 512) | 5.12 | 2.67 |
| block64, Y = 0.4 | — | **+0.172** (same) | 11.67 | 3.93 |

- All five pre-registered geometries, and the three larger blocks, are ≥ 0: **the design works** on the saved geometries.
- Rigour is unchanged: double precision, line model, per-geometry parameters.

**Diagnosis behind it.**
- The P_h-free DP's optimal environment for block16 is doubles at density 2 out to ±60 (reconstructed chain).
- Embedded in a period N = 1024 with a lattice fill, that environment has exact LP +11.2 / +13.2: P_h 8.5–9.9 (5.6 of it at |α| ≤ 1/64), and all-pairs T_g 1.8–3.7 that the nearest-neighbour relaxation misses.
- So the negative P_h-free bounds came from dropping P_h (density) plus the nearest-neighbour relaxation, not from real configurations (`multipair_dpenv_check.py`).

**Class (i) at smaller separation** (Voronoi partition of unity; `crowd_dp4.py`, `xlemma_exact.py`).
- Allocation: non-cluster T_g with weight v(u) = 1 → 0 across [L − ½, L + ½] (so Σ_p v_p ≤ 1 by the Voronoi complement); cluster parts with weight 0.8·v + CW(L/u)² for u ≥ L + ½ (sum checked ≤ 1).
- Exact X(d) on [D0, 64] per annulus (grid plus local-variation allowance), tail by two integrations by parts, charged to the deeper pair.
- Results:

| D0 | closed for depths | min (margin − X charge) |
|---|---|---|
| 32 | ≤ 0.8 | earlier result |
| 16 | ≤ 0.8 (CW = 0.14; `crowd_dp4_D16.log`, `xlemma_exact_D16.log`) | +1.35 |
| 8 | ≤ 0.7375 | +0.98 |
| 4 | ≤ 0.1875 | +0.038 |

  - At D0 = 4 the worst-case X charge grows like y² above 0.19; at D0 = 8 it overtakes the margin at 0.7375.
- Mixed-depth bookkeeping is still to be finalised: radius L(y_p) per pair, separation ≥ L(y_p) + L(y_q), and annuli re-counted accordingly.

**Pairs-in-the-DP-alphabet: design assessment (2026-10-09, estimate only, not built).**
- Measured obstacles:
  - (1) ĥ ≤ 2.2e-3 on 1/16 < |α| < 1 (mostly ≲ 4e-4). That band is where the pair field qf·B_y lives (weight peaked at α ≈ 0.5–1). So the far pair–environment coupling cannot be absorbed on the Fourier side: Cauchy–Schwarz would need a pair weight ~ |qfB|²/ĥ ~ 10⁶y⁴.
  - (2) In real space a crude far bound costs ≈ 4y²A₂/r per pair (A₂ = 2.9–16.5), against certified dense-block margins of 0.0027 (block64, Y = 0.4) to 0.05 per pair. That forces r ~ 10³, while a nearest-neighbour coupling (r ≈ 1) loses ~3y² per pair.
  - (3) An exact in-window coupling needs the DP state to carry (offset, depth bin) of every pair within range: exponential in the window.
- Estimate: infeasible by orders of magnitude.
- Decision test: build the nearest-neighbour-coupling variant (state = cell, type, prior half-bin mass; J = 8 depth bins; ~×5 DP cost) and run it on the saved depth profiles with free pair placement. Predicted: negative by ~y² per pair. Not run.
- Alternatives:
  - (B) A low-dimensional geometry B&B: box looseness ≈ 300·P·y²·Δs, so Δs ≲ 1e-5–1e-4 at block margins. Infeasible without a reduction lemma.
  - (C) A geometry-reduction lemma (uniformly compressed block plus edge profile is the worst case), after which a 2–3-parameter B&B costs ~10⁴ DPs (~4 days single thread). Cheap plausibility test first: compare DP bounds for relaxed (non-uniform) geometries against uniform-spacing geometries of the same mean spacing.
  - (D) A two-body multi-type certificate, which is geometry-free. The earlier hybrid family was infeasible or ≤ 0.6735 (`hybrid_cert.log`), so it costs κ.

**Plausibility test (C) for a geometry-reduction lemma — PRE-REGISTRATION (written before running, 2026-10-09).**
- Comparators for each of the 8 saved relaxed geometries, keeping the same pair count and the same depth sequence:
  - U0: fully uniform spacing, equal to the relaxed mean spacing (same span);
  - U1 ("with the edge profile"): first and last spacings kept, interior spacings replaced by their mean (same span). **The rule applies to U1.** U0 is reported for information.
- DP bound: `multi_env_dp.py` with the density lemma, using the same parameters that certified the relaxed geometry (same XR, t_L, t_B = 0.5, XL).
- DP resolution: 0.02 absolute (cell refinement 1/256 → 1/1024 moved bounds by ≤ 0.011).
- Rule:
  - SUPPORTS if every relaxed bound ≥ its U1 bound − 0.02;
  - REFUTES if any relaxed bound < its U1 bound − 0.02 (report the geometry).
- PREDICTION: REFUTES. The relaxed geometries are local minimisers of the exact LP over positions, and I expect the DP bound to inherit that ordering: relaxed bound below U1 by more than 0.02 in at least the block cases (my guess 0.02–0.1 for U1, 0.1–0.5 for U0). A graded profile smears the compressed Bragg peak, which lowers the density lemma's band term.
- **RESULT (C), `plausibility_C.log`: REFUTES, as predicted.** Relaxed bound vs U1 vs U0:

| geometry | relaxed | U1 | U0 | relaxed − U1 |
|---|---|---|---|---|
| block16, Y = 0.2 | +0.143 | +0.149 | +0.237 | −0.006 (within resolution) |
| block16, Y = 0.4 | +0.273 | +0.545 | +4.33 | **−0.27** |
| comp8, Y = 0.4 | +0.424 | +2.174 | +3.95 | **−1.75** |
| comp8, Y = 0.2 | +0.113 | +0.185 | +0.270 | **−0.07** |
| comp4, Y = 0.4 | +1.227 | +1.227 | +2.04 | 0 (U1 = relaxed) |
| block32, Y = 0.4 | +0.191 | +1.506 | +6.29 | **−1.32** |
| block64, Y = 0.2 | +0.761 | +0.876 | +1.17 | **−0.12** |
| block64, Y = 0.4 | +0.172 | +3.324 | +8.20 | **−3.15** |

  - "Uniform interior plus edge spacing" is not the worst case for the DP bound; the graded relaxed geometries are lower in 6 of 8 cases.
  - U0, with no edge profile, is far higher, so the boundary layer carries the hard part.
- Certified dense-block margins, kept for the interval-arithmetic costing: 0.0027 (block64, Y = 0.4) to 0.05 per pair; block16 0.009–0.017 per pair; comp8 0.014–0.053 per pair.
- Edge-layer diagnostic (follow-up to (C), `plausibility_C_edge.log`): comparators that keep k spacings at each edge, with a uniform interior. Relaxed vs E2 / E3 / E4:

| geometry | relaxed | E2 | E3 | E4 |
|---|---|---|---|---|
| block16, Y = 0.2 | 0.143 | 0.143 | 0.142 | 0.143 |
| block16, Y = 0.4 | 0.273 | 0.386 | 0.283 | 0.272 |
| block32, Y = 0.4 | 0.191 | 0.969 | 0.504 | 0.327 |
| block64, Y = 0.2 | 0.761 | 0.817 | 0.790 | 0.776 |
| block64, Y = 0.4 | 0.172 | 2.548 | 1.704 | 1.222 |

  - comp8 has E3 = relaxed.
  - The boundary layer that a reduction would have to parametrise is ≤ 2–4 spacings for short or shallow blocks, but ≥ 8–16 for long blocks at y = 0.4 (graded 0.842, 0.952, 0.956, 0.969, … → 0.99).
  - A reduction family would need a graded edge profile, e.g. a_∞ − b·e^{−k/ℓ}: 3–4 parameters plus depth.

**Class (i) with MIXED depths: CLOSED** (`mixed_alloc_check.py`, `crowd_dp4_mixA.log` / `mixB.log` / `mixC14.log`, `xlemma_mixA.log` / `mixB.log` / `mixC14.log`).
- Radius by depth:

| class | depths | L | CW | min (margin − X charge) |
|---|---|---|---|---|
| a | y ≤ 0.1875 | 2 | 0.1 | +0.038y² |
| b | 0.1875 < y < 0.625 | 4 | 0.1 | +0.19y² |
| c | 0.625 ≤ y ≤ 0.8 | 14 | 0.05 | +9.6y² |

  - X charges use annuli starting at L_q + 2, width 4; WINC = 0.8.
- Admissible configurations: |s_p − s_q| ≥ L(y_p) + L(y_q) for all pairs.
- Allocation: sup Σ v_p = 1 (the Voronoi complement), and sup Σ c_p = 0.957. The latter comes from 300 random class sequences plus adversarial patterns at minimal separations, so it is a SAMPLED check, not exhaustive.
- Rigour: double precision.

**Shared lemma DV (with bridge-port, 2026-10-09).** Periodic model, total mass N, any weight ρ ≥ 0 on the frequency axis.
- (1/N)Σ_{j≠0} ρ_j|S_j|² ≥ 2Σ_a M_a v(x_a) − (1/N)Σ_{j≠0} |c_j|²/ρ_j, for every real mean-zero test function v (coefficients c_j supported where ρ > 0).
- Fixed-bump form: with v = t(w − ∫w/N), w = 1_R * Fejér_δ ≥ 0, this is ≥ 2t(Σ M w − ∫w) − t²∫_{0<|α|≤δ}|ŵ|²/ρ.
- Instances:
  - ρ = ĥ: the P_h density lemma (shallow blocks; low-band bump plus a band-beyond-1 test function built from the pairs' spectrum);
  - ρ = q·1_{|α|≤δ}: bridge-port's Lemma LL, which is the configuration-adapted (Cauchy–Schwarz-optimal) case with test function V = Σ e(α s_p). LL then uses ⟨S_A, V⟩ ≥ 2‖V‖² under its quarter-turn condition, and |V|² ≥ P²cos(2πδL).
- α-dependent masses: ⟨S_A, ŵ⟩ = Σ_p 2Re w(s_p + iy_p), and 2Re w(s + iy) − 2w(s) = O((2πδy)²)‖w‖. The mass-count form therefore needs δ ≲ 1/(2πy) (density at scale y): harmless for shallow blocks; deep pairs keep the cosh weight explicitly.

## Round 1 of the core push (2026-10-09)

**(2) Cluster-slack allocation: now EXHAUSTIVE** (`mixed_alloc_exhaustive.py`, `mixed_alloc_exhaustive.log`).
- Every weight is non-increasing in distance, so the worst case for fixed class sequences is minimal separation, and the two sides are independent.
- Method: the first 10 neighbours per side are enumerated (3^10 sequences); the rest is bounded classwise (a class's members are ≥ 2L apart); u-grid includes the breakpoints, plus a slope allowance; points in no core or ramp carry tails only (≤ 0.489).
- Result: sup_x Σ_p c_p(x) ≤ 0.9949 ≤ 1. This **replaces the sampled 0.957**.

**(1) Bulk/end lemma for shallow dense blocks — PRE-REGISTRATION (written before running).**
- Bulk density per pair of the certified bound, analytic by Poisson for a uniform pair lattice at spacing a < 1 with no environment inside:
  m_bulk(a) = 4Σ_{k≠0} g(ka) + 4(2t_B − t_B²)(1/a)Σ_m ĥ_W(m/a) + [4t_L − 2t_L·a − t_L²·a/ĥ(0)] + Q_pp/P (→ 0 for a < 1).
- Validation: DP bounds for exact uniform blocks (a = 0.97, 0.985; y = 0.2, 0.4; P = 8, 16, 32, 64). Fit bound = P·slope + 2e_end and compare the slope with m_bulk.
- Relaxed blocks: periodic minimisers with N = 4P, P = 16, 32, 64, at Y = 0.2 and 0.4. Deficit Δ(P) = bound − P·m_bulk(a_c), with a_c = centre spacing (and also the mean spacing). The grading length ℓ is fitted to the spacing profile.
- Rule:
  - SUPPORTS if |Δ| stays of the same order at P = 16, 32, 64 (bounded in P);
  - REFUTES if Δ grows (in magnitude) with P.
- PREDICTION: **REFUTES.** The certified relaxed-block totals do not grow with P (0.27 / 0.19 / 0.17 at Y = 0.4), while m_bulk(a_c) > 0 (T_g at spacing a_c plus the density terms, ≈ 0.02–0.05 per pair). So Δ ≈ −P·m_bulk + O(1). I expect the relaxed blocks to grade over a length that grows with P, so there is no P-independent edge layer in the certified bound.
- **RESULT (1): REFUTES, as predicted** (`bulk_end.py`, `bulk_end_dp.log`, `bulk_end_analyse.py`, `bulk_end_analyse.log`). Best certified bound over 3 parameter sets; XL = 512; coherent far-field tail. D = LB − P·m_bulk(a_c); D_near excludes the DP tails.

| block | P | LB | a_c | m_bulk(a_c) | D | D_near | grading ℓ |
|---|---|---|---|---|---|---|---|
| relaxed, Y = 0.2 | 16 | 0.289 | 0.9896 | 0.049 | −0.50 | −0.40 | 1.1 |
| relaxed, Y = 0.2 | 32 | 0.368 | 0.9949 | 0.031 | −0.63 | −0.44 | 2.4 |
| relaxed, Y = 0.2 | 64 | 0.438 | 0.9974 | 0.023 | −1.00 | −0.64 | 4.6 |
| relaxed, Y = 0.4 | 16 | 0.732 | 0.9729 | 0.105 | −0.95 | −0.78 | 1.0 |
| relaxed, Y = 0.4 | 32 | 0.390 | 0.9861 | 0.061 | −1.56 | −1.24 | 2.3 |
| relaxed, Y = 0.4 | 64 | **−0.164** | 0.9929 | 0.038 | −2.58 | −1.92 | 4.6 |

  - Uniform comparators at a = 0.97 / 0.985:
    - Y = 0.4: D = +1.8 / +3.1 / +1.7 and +7.1 / +4.1 / +4.7, roughly bounded with positive ends;
    - Y = 0.2: D = −1.04 / −0.95 / −1.48 and −0.69 / −1.16 / −1.39, drifting partly through the DP tails.
  - Mechanism: in the periodic minimisers (N = 4P) the centre spacing drifts toward 1 and the grading length grows like ≈ 0.07P. So the edge layer is not P-independent, and the deficit grows. The DP tails (∝ P/XL) account for about ⅓ of the growth.
  - Certificate status for these geometries: rb64 at Y = 0.4 (N = 256) gives a negative DP bound (−0.164) with the three tested parameter sets, while its exact periodic LP is +10.31. That is looseness of the certificate, not a negative configuration. The other five are positive.
- bridge-port's lattice-with-ends results, for reuse (`sat9/e31*.py`, `e31*.log`):
  - T_pp(P) = P·τ(a) − 8Σ_k k·g(ka) + tail, with τ(a) = 8Σ_{k≥1} g(ka) (my 4Σ_{k≠0}).
  - Equal-depth lattice: Q_pp(P) = C_end − ½∫q(B² + 4B)cos(2πPaα)/sin²(πaα), with C_end = ½∫q(B² + 4B)/sin²(πaα), O(y²) for shallow y. The same ½∫ρ(…)/sin² form gives the end term of any band-weighted quadratic, e.g. my ĥ_W density term.
  - For shallow blocks the measured deficit growth is the environment response plus the grading length ℓ ∝ P, not Q_pp.

## Round 2 of the core push (2026-10-09)

**Diagnosis before tightening** (component breakdown, Y = 0.4, P = 16 → 64):
- Changes across the range: Q_pp +0.46, T_pp +0.48, V_env **−2.43**, tails −0.49, density +1.09; net LB 0.73 → −0.16.
- The main loss is the environment response, not the tail.
- The reconstructed DP environment is doubles at density 2 everywhere outside the block (out to ±600). It collects the block's coherent far field: per unit mass −0.0215 at 10–20 from the ends and −0.0073 at 20–50. This far part grows with P (−1.34 → −2.28), because centre spacing → 1 makes Σ_p e(s_p) ~ P coherent.
- A density-2 environment is unpenalised outside the low-band window (R = cluster ± XR) and costs ~0 in nearest-neighbour T_g at near-zero spacing.

**Pre-registration for (2), local-density comparison (written before computing it).**
- Quantity: LB − Σ_p m_bulk(a_p), with a_p = mean of the two spacings adjacent to pair p (one spacing at the ends), for the relaxed blocks P = 16 / 32 / 64 at Y = 0.2 and 0.4, using the tightened LB from (1).
- PREDICTION: **not bounded in P.** It decreases roughly in proportion to ℓ ∝ P. The graded edge region, where m_bulk(a_p) is large (0.1–0.7 per pair at a_p ≈ 0.86–0.97), grows with P, while the certified LB stays O(1).

**RESULT (1): PASS** (`multi_env_dp.py` far-field repair; `round2_scan5.log` Y = 0.4, `round2_scan6_Y02.log` Y = 0.2; double precision, as for all DP results here).
- Repairs to the certificate:
  - φ beyond the c_j table (u > 128): the all-negative bound −(A2/u² + A3/u³)y² is replaced by the signed leading term −(A2/1.05)y²cos(2πu)/u², with remainder |R| ≤ A3y²/u³ (three integrations by parts; p(1) = 0, p′(0) = 0). Checked against the exact tables on [60, 128]: |φ − lead| ≤ 0.17·A3y²/u³ at y = 0.4 and ≤ 0.35 at y = 0.8.
  - DP range XL = 512 → 1024: halves the tail, which is dominated by the incoherent band bound |h_W| ≤ CW/u² (−0.65 → −0.32 at P = 64).
  - h_W table extended to u ≤ 300 (24-node quadrature agrees with a 400-node reference to 6e-11 there; it aliases beyond u ≈ 400, so beyond 300 the bound CW/u² is kept). A first version tabulated to u = 1400 and gave aliasing garbage (rb16 −1.08). That run (`round2_scan4.log`) is discarded; no reported number used it.
- Best certified LB:

| Y | P = 16 | P = 32 | P = 64 | parameters (t_B = 0.5, XR = 20) |
|---|---|---|---|---|
| 0.4 | +1.318 | +1.444 | **+1.628** | XL = 1024; t_L = 0.012 / 0.016 / 0.016 |
| 0.2 | +0.315 | +0.531 | +0.882 | XL = 512; t_L = 0.008 / 0.008 / 0.012 |
| 0.4, before repair | +1.141 | +1.075 | +0.815 | XL = 512 |

  - Both criteria hold at Y = 0.4: rb64 ≥ 0, and LB is increasing in P (it was decreasing before). Y = 0.2 is increasing too.
  - Certified LB per added pair (P = 16 → 64): +0.0065 at Y = 0.4 and +0.0118 at Y = 0.2.
- What is left of the growth (`chain_diag.py`, `round2_chain_diag.log`; Y = 0.4, XL = 1024, t_L = 0.016). From P = 16 to 64, V_env changes by −1.71 (one-body −1.73). By distance of the environment from the nearer block end:

| distance from end | 0–3 | 3–10 | 10–20 | 20–50 | 50–150 | 150+ |
|---|---|---|---|---|---|---|
| change P 16 → 64 | +0.005 | −0.16 | −0.14 | −0.34 | −0.52 | −0.58 |

  - The block's own neighbourhood (0–3; −4.42 at every P) does not grow.
  - The growth is far field: −1.43 of it lies ≥ 20 from the ends and −1.10 lies ≥ 50.
  - The minimising environment is a doubles chain at density 2 over the whole DP range (mass ≈ 4000 on ≈ 2100 units). It is charged only inside the low-band window R = block ± XR.
  - In the periodic model (total mass N, mean density 1), a density-2 stretch of length L is admissible only with compensation elsewhere. Its low-frequency P_h cost is quadratic in the excess mass, of order ĥ(0)·L (estimate, not computed). The line DP has no mass conservation, so it does not charge this stretch outside R.
  - The linear test functions tried so far are a window (XR = 12–64) and the decaying profile DPROF. Every one that charges the far chain also charges the empty environment through −2t∫w, and so far that has cost more than it recovers. Linear test functions have not been optimised beyond these.
  - A forward step could instead carry the mass count as DP state (a quadratic low-frequency penalty). This was not built (round rule).

**RESULT (2): prediction held — LB − Σ_p m_bulk(a_p) is NOT bounded in P** (`local_density.py`, `round2_local_density.log`). a_p is the mean of the adjacent spacings; t_L is matched to each LB.

| Y | P | certified LB | Σ_p m_bulk(a_p) (edge / bulk) | LB − Σ | exact periodic LP | LP − Σ | gradient G = Σ(Δa_p/a_p)² |
|---|---|---|---|---|---|---|---|
| 0.2 | 16 | 0.315 | 1.470 (0.95 / 0.52) | −1.15 | 2.323 | +0.85 | 0.0013 |
| 0.2 | 32 | 0.531 | 1.957 (1.09 / 0.86) | −1.43 | 3.213 | +1.26 | 0.0013 |
| 0.2 | 64 | 0.882 | 2.933 (1.26 / 1.68) | −2.05 | 4.763 | +1.83 | 0.0013 |
| 0.4 | 16 | 1.318 | 4.004 (3.30 / 0.71) | −2.69 | 7.196 | +3.19 | 0.0136 |
| 0.4 | 32 | 1.444 | 4.942 (3.67 / 1.27) | −3.50 | 8.417 | +3.48 | 0.0139 |
| 0.4 | 64 | 1.628 | 6.213 (4.14 / 2.07) | −4.59 | 10.311 | +4.10 | 0.0140 |

- The certified deficit grows by ≈ −0.3 to −0.6 (Y = 0.2) and −0.8 to −1.1 (Y = 0.4) per doubling of P. Σ m_bulk grows by 0.030 / 0.046 per pair, while the certified LB grows by 0.012 / 0.0065 per pair.
- The gradient measure G is constant in P. So LB ≥ Σ m_bulk − C·G would need C ∝ P: the target shape fails for the CERTIFIED bound.
- The EXACT periodic LP satisfies the shape with no gradient term on all six minimisers: LP − Σ m_bulk = +0.85 … +4.10, and increasing in P.
- Where the gap is: the certificate's environment response (above) absorbs the bulk density margin. Per pair, the far-field V_env loss (−0.036 per pair at Y = 0.4) is the same size as m_bulk's bulk growth.

## Round 3 of the core push (2026-10-09) — last before the state goes to Sam

**PRE-REGISTRATION (written before any round-3 run).**
- (1) Far-profile test, rb64, Y = 0.4. Test function family: f = 1 on R = block ± 20 and f = λ·(D/(D + d_out))^κ beyond R (out to XL = 1024), with the same t_L.
  - Grid: λ ∈ {0.3, 0.6, 1.0} × (D, κ) ∈ {(10, 1), (30, 1), (20, 1.5), (40, 2)}, then a refinement around the best.
  - Baseline: the same code with no far profile. The cell lower bound for w is corrected in this round, so the baseline is rerun.
  - Rule (lead's): best gain > 0.3 SUPPORTS linear far charging; otherwise REFUTES it for this family.
  - PREDICTION: **SUPPORTS**, gain ≈ +0.6 (range 0.3–1.0), probability ≈ 60%.
  - Reason. Per unit length, a charge c = r|f| per unit mass against a doubles chain gaining |f| per unit mass is worth −(2 − r)|f| for r ≤ 1 (doubles stay) and −r|f| for r ≥ 1 (the site goes empty and pays the constant). The best is −|f| at r = 1, which equals the density-1 value. From `round2_chain_diag.log`, current r ≈ 0.6 / 0.2 / 0.02 in the bands 20–50 / 50–150 / 150+. That gives an ideal recovery ≈ 0.22 + 0.36 + 0.41 ≈ 1.0. A 3-parameter power law over a 50× range of |f| should capture 50–70% of it. Over-charging is as costly as not charging (r = 2 recovers nothing), so mismatch is the risk.
- (2) Exact P_h of a density-2 stretch. Periodic model with N ≫ L: doubles at 0..L−1, and the remaining N − 2L singletons spread uniformly on [L, N); compare with the density-1 lattice. PREDICTION: ΔP_h(L)/L ∈ [0.012, 0.020], i.e. ≈ ĥ(0) = 0.0165, with an O(L·ĥ near α = 1) Bragg-shift correction.

**RESULT (1): SUPPORTS — prediction held** (`round3_far_rb64.log`, 21 DPs on rb64 at Y = 0.4; XL = 1024, XR = 20, t_L = 0.016, t_B = 0.5; double precision).
- Code change: the cell lower bound for w now takes the larger of two bounds.
  - Bound (a): midpoint − |w′|h/2, with TV(k_β) < 2.4β. Round 2 used 2β, slightly too small; the true value is 2.388β.
  - Bound (b): min of the endpoint values − |w″|h²/8, with max|k″| = (2π)²β³/6.
- Baseline, same code, no far profile: rb64 **1.7288** (round 2: 1.628).
- Best profile: (λ, D, κ) = (0.45, 20, 1.5) gives **2.3592, gain +0.630**. Next best: (0.4, 10, 1) gives 2.341 (+0.612).
  - Seven profiles lie on a plateau of +0.50 to +0.63.
  - Over-charged profiles lose heavily, e.g. (1.0, 30, 1) gives −3.91. This is the r ≥ 1 branch of the per-site analysis.
- Each geometry takes its own best profile: rb16 1.431 (λ = 0.1), rb32 1.792 (λ = 0.2), rb64 2.359 (λ = 0.45).
  - Certified per-pair slope P = 16 → 64 at Y = 0.4: **0.0193** (round 2: 0.0065).
  - The rb64 profile applied to rb16 loses 0.58, as expected from over-charging a weaker far field.
- Residual far chain on rb64 (`round3_chain_diag_far.log`):
  - The 20–50 band is mostly emptied.
  - 50–150 and 150+ are still doubles, but now near balance: r = charge / |field + g + band| per unit mass = 0.90 and 0.75.

**RESULT (2): exact P_h of a density-2 stretch, and a cost estimate for the mass-count DP (not built)** (`stretch_ph.py`, `round3_stretch_ph_N4096*.log`). Periodic model, N = 4096, doubles at 0..L−1, compared with the density-1 lattice (lattice P_h = 0, since ĥ vanishes at integers).

| L | ΔP_h, low band \|α\| < ½ | stretched-lattice compensation | contiguous vacancy block | spread vacancies (cheapest) |
|---|---|---|---|---|
| 16 | 0.0093/L | 0.296/L | 0.0319/L | 0.0255/L |
| 64 | 0.0140/L | 0.288/L (ΔP_h = 18.46) | 0.0327/L (2.09) | **0.0259/L (1.658)** |
| 256 | 0.0166/L (= ĥ(0)) | 0.045/L | 0.0329/L | 0.0260/L |

- ΔT_g: 0.0013/L (spread vacancies), 0.0027/L (contiguous), 0.16–0.33/L (stretched lattice).
- What makes up the total:
  - the low band tends to ĥ(0)·L;
  - a contiguous deficit costs as much again, giving ≈ 2ĥ(0)L;
  - each isolated vacancy costs ≈ h(0) = 1 − g(0) ≈ 0.0096;
  - compensating by stretching the whole lattice moves its Bragg peak to α ≈ 1 − L/N, where ĥ > 0, and costs ≈ 0.28/L.
- PREDICTION [0.012, 0.020]/L: held for the low-band part (0.0140 at L = 64, 0.0166 at L = 256). It did **NOT** hold for the total: the cheapest compensation adds ≈ 0.010/L, and the stretched-lattice compensation adds 0.27/L.
- Cost estimate for the mass count as DP state:
  - CPU: mass state S ≈ 35–50 per 32-unit bin (the excess is capped where ĥ(0)e²/L_b exceeds the far gain), carried on the ≈ 51% of cells outside R. That is ≈ 10–15× the DP, so ≈ 10–17 min per rb64 run at XL = 1024.
  - Missing lemma: a bin-local quadratic minorant of the low band of P_h. The hard-bin form ρ = c·L_b·sinc²(αL_b) ≤ ĥ fails for EVERY c > 0, because ĥ ≡ 0 on [1.25, 1.3125], [1.5, 1.906], [2.4375, 2.469], [2.531, 2.8125], [2.969, 3], where sinc² does not vanish. So it would have to be the band-limited window form, which couples neighbouring bins (a Toeplitz form) and needs a diagonal (symbol-minimum) reduction. That reduction has not been done.
  - Expected recovery:
    - The exact cost per unit excess (≥ ĥ(0) = 0.0165, ≈ 0.026 with the cheapest compensation) exceeds the far gain per unit mass (≤ 0.009 beyond 20). So a mass-count DP would remove all far excess and leave a density-1 environment. That environment's per-site value −|f| equals a perfectly matched linear charge (r = 1).
    - Its gain over the round-3 linear profiles is therefore only the residual mismatch |1 − r|·|f|: ≈ 0.08 / 0.16 / 0.15–0.30 on rb16/32/64, i.e. ≈ 0.002–0.005 per pair.
  - What neither option removes: the density-1 environment collecting the block's coherent far field, ≈ F/2 = −0.42 / −0.83 / −1.41 on rb16/32/64 (round-2 chain, distance ≥ 20). This term grows like ln((20 + P)/20) × coherence, i.e. sublinearly in P.
- Flag on the round-2 exact comparison: LP − Σm_bulk > 0 was measured on N = 4P minimisers, where the environment density is 2/3. A density-1 environment locked to the block (N ≫ P) has not been tested in the exact functional. The cheapest decision test is the exact relaxed LP of the same blocks at N = 16P.

**(3) Record line.**
- Certified per-pair slope over P = 16 → 64:
  - round 2: 0.0065 (Y = 0.4) and 0.0118 (Y = 0.2);
  - round 3 with the far profile: 0.0193 (Y = 0.4; Y = 0.2 not rerun).
- Thinnest available margin: m_bulk(a → 1) = 0.021 per pair.
- For interval-rigour costing: per-pair margins are 0.0065–0.019 against block totals of 1.3–2.4 and a DP resolution of 0.02. The interval cost is in enclosing the cell bounds (c_j tables, h_W, w), not in floating-point precision.
- Note from bridge-port (2026-10-09): bridge-port's lattice-with-ends numbers are all PAIR–PAIR only, i.e. Q_pp + T_g^pp. That covers C_end, τ(a), the end deficit, the deep-profile end term ≈ 15, and the bulk margin = τ(a). No environment and no P_h enter them. So the stretch, compensation and Bragg-shift costs above do not apply there. Both records agree that the P-dependent loss lies in the environment, and that a block's own end term does not depend on P.

## Round 4 (2026-10-09): the N = 16P exact decision test (Sam chose "cost the port first"; this is the only task this round)

**PRE-REGISTRATION (written before any run).**
- Quantity: the exact relaxed periodic LP of the relaxed blocks P = 16 / 32 / 64 at N = 16P (environment density (N − 2P)/(N − P) ≈ 0.93, against 2/3 at N = 4P), at Y = 0.2 and 0.4, minus Σ_p m_bulk(a_p).
  - a_p = the mean of the adjacent spacings of the relaxed pairs.
  - m_bulk uses the same t_L per geometry as the round-2 table (Y = 0.2: 0.008 / 0.008 / 0.012; Y = 0.4: 0.012 / 0.016 / 0.016). A fixed t_L = 0.016 is reported as a sensitivity check.
- Relaxation: L-BFGS on all positions (environment and pair centres; depths fixed at Y), from three starts:
  - (a) contiguous vacancies next to the block, as in round 1;
  - (b) vacancies spread evenly;
  - (c) a uniformly stretched environment.
  The lowest LP is used; all three are reported.
- Rule (the lead's, as I stated it): LP − Σ m_bulk(a_p) increasing in P SUPPORTS the local-density shape; decreasing REFUTES it at large N. Increments within ±0.05 count as flat and are reported as such.
- PREDICTION: **SUPPORTS at both Y**, about 70% confidence, with LP − Σ m_bulk positive and of the same order as at N = 4P (±1).
  - Reason: the exact LP carries the cost of compensating the block's excess mass P, which grows in proportion to P. From round 3, that is ≥ 0.026 per unit excess with spread vacancies and up to ≈ 0.28 per unit length with lattice stretching. Σ m_bulk does not contain it.
  - Against that, a density-1 environment locked to the block gains a coherent far field that grows only like ln P (round-3 estimate ≤ 1.4 at P = 64, Y = 0.4, from the certified DP's field).
  - Risk: the relaxed environment trades compensation cost against locking in ways the estimate does not see. The round-3 field estimate is an upper bound on the gain from locking, not a computed value.

**RESULT: SUPPORTS at both Y — prediction held** (`exact_n16.py`; `round4_n16_Y02.log`, `round4_n16_Y04.log`, `round4_n4_starts.log`; geometries in `bulk_end_n16_Y0{2,4}.json` and `bulk_end_n4_starts.json`; double precision, L-BFGS with ftol 1e-15 / gtol 1e-9, all runs converged).
- Validation: start (a) at N = 4P reproduces the round-1 values exactly (8.4166, 10.3110).
- Start (b), spread vacancies, gives the lowest LP in all 12 cases. Start (a) is higher by 0.36–2.76 and start (c) by 0.08–0.80.

| Y | P | N = 16P: exact LP | Σ m_bulk(a_p) | **LP − Σ** | (t_L = 0.016) | N = 4P, min of 3 starts: LP − Σ | env density within 40 of the ends (16P / 4P) | env locking \|⟨e(x)⟩\| at N = 16P |
|---|---|---|---|---|---|---|---|---|
| 0.2 | 16 | 1.910 | 1.361 | **+0.549** | +0.471 | +0.577 | 0.90 / 0.40* | 0.98 |
| 0.2 | 32 | 2.710 | 1.821 | **+0.889** | +0.740 | +0.800 | 0.90 / 0.65 | 0.96 |
| 0.2 | 64 | 4.135 | 2.770 | **+1.365** | +1.282 | +1.009 | 0.90 / 0.65 | 0.93 |
| 0.4 | 16 | 5.865 | 3.789 | **+2.076** | +2.044 | +2.388 | 0.90 / 0.40* | 0.88 |
| 0.4 | 32 | 6.921 | 4.664 | **+2.257** | +2.257 | +2.489 | 0.90 / 0.65 | 0.75 |
| 0.4 | 64 | 8.620 | 5.875 | **+2.745** | +2.745 | +2.748 | 0.90 / 0.65 | 0.54 |

(*At N = 64 the 80-unit window covers the whole 48-unit environment.)
- Increments in P (N = 16P): Y = 0.2: +0.34, +0.48. Y = 0.4: +0.18, +0.49. Both increase, and both are above the ±0.05 flat band. The t_L = 0.016 sensitivity column also increases.
- The environment does lock to the block at N = 16P: phase 0.00 relative to arg Σ_p e(s_p), and |⟨e(x)⟩| 0.54–0.98 within 3–60 of the ends.
  - Locking lowers the margin at P = 16 (−0.03 at Y = 0.2, −0.31 at Y = 0.4 against N = 4P).
  - At P = 64 the margin is equal (Y = 0.4) or higher (Y = 0.2, +0.36).
  - So the gain from locking does not outgrow the per-pair bulk margin over this range. That is consistent with the round-3 estimate that it grows like ln P.
- **Correction to round 2:** the N = 4P "exact LP" column used start (a) local minima. The minimum over three starts is lower by 0.36 (P = 16, Y = 0.2) up to 1.55 (P = 64, Y = 0.4).
  - Corrected LP − Σ at N = 4P: +0.58 / +0.80 / +1.01 (Y = 0.2) and +2.39 / +2.49 / +2.75 (Y = 0.4). It still increases in P, so the round-2 conclusion stands with smaller margins.
- Scope:
  - These are local minima from three start families; the global minimum over configurations is not certified.
  - Depths are fixed and equal; the environment density at N = 16P is 0.93, not 1.
  - The certified DP bounds (round 3) were computed on the start-(a) pair geometries. The start-(b) pair geometries differ slightly (centre spacing within 0.0005, every spacing within 0.018) and have not been run through the DP.

## Round 5 (2026-10-09): am-cert fit conditions C2 and C3 (Sam: "run the cheap refuting test first")

**PRE-REGISTRATION (written before any run).**
- (C2) Banded-DP lemma. Rerun crowd_dp4 for classes A (L = 2, y ≤ 0.1875), B (L = 4, 0.1875 < y < 0.625) and C14 (L = 14, 0.625 ≤ y ≤ 0.8), with the same parameters and y-intervals as `crowd_dp4_mix{A,B,C14}.log`.
  - Every bond between consecutive chain points whose cell distance satisfies d_min > r is set to 0. This is valid because bond ≥ 0: the bonds are gmin_range × weights, with gblk ≥ 0. The successor search beyond r then becomes a suffix minimum.
  - Tested at r ∈ {1, 2, 4}. Validation: r = ∞ must reproduce the logged values.
  - Class-(i) margin per interval = (banded LP_p/y² bound) − (X charge R from `xlemma_mix*.log`, which does not depend on the DP).
  - PASS (lead's rule): min over each class's intervals stays > 0 at some r ≤ 4, for all three classes.
  - PREDICTION: **PASS at r = 4**, about 65% confidence.
    - Classes B and C14 pass at r = 2 and r = 4: their margins are 0.19y² and 9.6y², and bonds beyond 2 are near zero, since g has near-zeros at 1.988 and 2.087.
    - Class A is the risk. Its margin is only 0.038y², and the bonds enter in units of 1/y², so even small g values matter at small y. I expect A to fail at r = 1 (g has a bump between 1.03 and 1.99) and to pass at r = 4.
- (C3) Cluster monotonicity. From the unbanded crowd_dp4 tables, check whether W[m, p, k] is non-decreasing in the cluster count p, for every m and k and every y-interval. Also report the saturation level p*, beyond which W[m, p, k] = W[m, PCAP, k].
  - PREDICTION: **monotone** (exactly, up to floating point). By backward induction, the charge clk·m₂·p ≥ 0 increases in p and pn = min(p + m, PCAP) increases in p; at the cap the self-cell option is removed, which only raises W.
  - Saturation p* ≤ 2 everywhere, so that ≤ 3 levels need replay, with probability ≈ 60%. The half-bin charge 2·a_half·m₂·p/y² grows fast, but the cluster weight w_hb is as small as CW·(L/u)² far out, which could allow deeper clusters there.

**RESULT (C2): PASS at every r ∈ {1, 2, 4} for all three classes.** The prediction ("PASS at r = 4; A fails at r = 1") held on PASS and was wrong about A at r = 1. Files: `crowd_dp4_banded.py`; `round5_banded_A.log`, `round5_banded_B.log`, `round5_banded_C14.log`. Double precision. Validation: r = ∞ reproduces the logged bounds in every interval.

| class (y-range) | r = ∞ (crowd_dp4) | r = 4 | r = 2 | r = 1 |
|---|---|---|---|---|
| A (L = 2, y ≤ 0.1875) | +0.0378 | +0.0378 | +0.0378 | +0.0205 |
| B (L = 4, 0.1875 < y < 0.625) | +0.1924 | +0.1924 | +0.1924 | +0.1811 |
| C14 (L = 14, 0.625 ≤ y ≤ 0.8) | +9.6174 | +9.6174 | +9.6174 | +9.6124 |

(Entries are min over y-intervals of margin − X charge, in units of y².)
- At r = 2 and r = 4 the banded bound equals the unbanded one to 4 decimals in all 64 intervals: bonds with d_min > 2 never change the DP value.
- At r = 1 the bound drops by at most 0.28 (A), 0.31 (B) and 0.024 (C14) per interval, but every class margin stays positive. The binding intervals are unchanged.
- The cheapest banded form that keeps all three classes closed is therefore r = 1. The lossless form is r = 2.

**RESULT (C3): MONOTONE, exactly; the "≤ 3 levels" condition holds only partly.**
- Monotonicity: W[m, p, k] is non-decreasing in p in every (m, k) entry of every interval of A, B and C14. There are 0 violations, and the maximum decrease is 0.00e+00. Prediction held.
- Saturation level p*, the first p with W[m, q, k] = W[m, PCAP, k] for all q ≥ p:
  - A: p* ≤ 1 everywhere (histogram {0: 215100, 1: 3780}).
  - B: p* ≤ 2 for y < 0.55, and up to 5 for y ≥ 0.55 (histogram {0: 497288, 1: 11878, 2: 780, 3: 534, 4: 220, 5: 20}).
  - C14: p* up to 14 (histogram {0: 193057, 1: 5379, 2: 843, 3–14: 5009}).
- Where the deep levels sit: next to the pair. In B (y = 0.6125) 111 of the 112 cells with p* ≥ 3 lie at u ∈ [0.5, 1); one lies at u ∈ [64, 129) with p* = 3. In C14 (y = 0.7875) 256 of 257 lie at u ∈ [0, 1); one at [1, 2). The cluster weight there is w_hb = WINC = 0.8.
- Prediction "p* ≤ 2 everywhere" did NOT hold: B reaches 5 and C14 reaches 14. I also expected any deep levels in the far region, where the cluster weight is small. They are in fact in the first two half-bins, where the pair's field is strongest and the DP stacks a cluster.
- So, for the certificate: ≤ 3 replay levels suffice for all of class A, and for class B at y < 0.55, except the first two half-bins (u < 1). There p must be replayed up to 15 levels for C14 and 6 for B. That is ≤ 257 of 7296 cells per interval.

## Round 6 (2026-10-09): rerun of the w-bound-affected certificates (lead-approved)
- What: the round-2 code's low-band w cell bound used 2β; the true TV(k_β) is 2.388β. The 8 saved-geometry certificates, plus block64 Y = 0.4 at XR = 40, and the Y = 0.2 graded row are rerun with the corrected code (`multi_env_dp.py` as of round 3) and the original parameters.
- Files: `round6_rerun_A.log`, `round6_rerun_B.log`, `round6_rerun_C.log`.
- Corrected values (earlier values in brackets):
  - block16, Y = 0.2: +0.155 [0.143]
  - block16, Y = 0.4: +0.584 [0.273]
  - comp8, Y = 0.4: +0.462 [0.424]
  - comp8, Y = 0.2: +0.121 [0.113]
  - comp4, Y = 0.4: +1.258 [1.227]
  - block32, Y = 0.4: +0.658 [0.191]
  - block64, Y = 0.2: +0.891 [0.761]
  - block64, Y = 0.4: +1.140 [0.172]; at XR = 40: +1.502 [0.530]
  - rb16/32/64, Y = 0.2: +0.352 / +0.571 / +0.950 [0.315 / 0.531 / 0.882]; slope 0.0125 per pair [0.0118]
- **No sign change; every value rose.** The rise comes from the other round-2/3 bound improvements: the endpoint-curvature w bound, the signed φ far field beyond u = 128, and the h_W table to 300.
- `LEMMAP_NOTE_shallow.md` §4 is updated, and open item 3 is closed.

## Round 7 (2026-10-09): truth check of the mixed shallow/deep leaf (back on the math; no board target)

**PRE-REGISTRATION (written before any run).**
- Object: the FULL exact LP = E(Z) − F_C(D(Z)) in the periodic model with per-zero (pSq) weights: an on-line zero of multiplicity m weighs m², and an off-line pair of multiplicity m weighs 4m (2m for each of its two zeros).
  - LP = 2d/N + ĝ(0)·N − g_N(0)·(Σ_on m_a² + 4Σ_pairs m_i), with d = Σ_{0<j<N} q(j/N)|S_j|² and S_j = Σ_on m_a e(jx_a/N) + Σ_pairs m_i·2cosh(2πjy_i/N)·e(js_i/N).
  - g_N(0) = g(0) exactly for N ∈ {64, 128, 256}, since g(nN) = 0 when N is a multiple of 32.
- Cancellation-free form: d is a sum of non-negative terms. LP = O(1) arises only as 2d/N minus an O(N) constant, so float64 is accurate to ≈ 1e-13·N plus the S_j rounding error (≲ 1e-16·Σ|terms|).
  - Every candidate with float LP < 1 is RE-EVALUATED in mpmath at 50 digits: q from the window's closed form with the exact rational coefficients, and ĝ(0) and g(0) from the exact rational knots.
- Search: N ∈ {64, 128, 256}; L-BFGS-B over ALL on-line positions, pair positions and depths; shallow pairs y ∈ [1e-3, 0.8], deep pairs y ∈ [0.8, 3] (or one common range [1e-3, 3] in the random family). Multi-start families:
  - (a) deep pairs inserted into the rb16/32/64 blocks (N = 4P, start-(b) geometries), at k ∈ {1, 2, 4} positions, starting depth ∈ {0.8, 1, 1.5, 2, 3};
  - (b) shallow blocks flanked by deep pairs;
  - (c) stacks under pSq: m ∈ {2, 3, 4, 6} coincident pairs at depth 0.8–1.2, plus on-line multiplicities 2 and 3, near or inside the blocks;
  - (d) random mixtures (P random, 60% shallow, 40% deep, random positions).
  Seeds are recorded and shared with bridge-port.
- Rule:
  - REFUTES Lemma P configuration-wise if any LP < 0 is confirmed in mpmath; the configuration is saved.
  - SUPPORTS if min LP ≥ 0. The thinnest per-pair margin (LP / #pairs) is reported by regime.
- PREDICTION: **SUPPORTS**, about 85% confidence. The thinnest per-pair margins should be in the all-shallow dense blocks (≈ 0.03–0.06 per pair, from round 4), and adding deep pairs should only raise the per-configuration minimum.
  - Reasons: under pSq a stack's self-energy grows like m²B² while its charge grows like 4m. A deep pair's self-energy ~ e^{4πy} dominates its field on the environment ~ N·e^{2πy} once e^{2πy} ≳ N, and at y ≈ 0.8 (e^{2πy} ≈ 150) the single-pair certificate already covers any environment.
  - Risk: a deep pair at y ≈ 0.8 adjacent to a shallow block, where the block's coherent spectrum near α = 1 couples to the large cosh weight. The ordSq failure (bridge-port, stacks at 0.8) shows that regime is where the functional is thinnest.

**Addendum to the round-7 pre-registration (written after families a–d, before family e).**
- Families a–d are done: 490 runs, no LP < 0, and 132 mp50 re-evaluations agree with float to ≤ 8.5e-13.
- Design flaw found in family d: it used one depth range [1e-3, 3]. The minimiser drove EVERY pair, deep ones included, to y = 1e-3, so the configurations collapsed to real D with LP → s(D) (the certificate's own slack, ≈ Nσ at the lattice). Family d therefore did not test mixed depths.
- Family e (new) fixes this:
  - deep pairs y ∈ [0.8, 3] (1–4 of them); shallow pairs y ∈ [y_lo, 0.8] with y_lo ∈ {0.05, 0.1, 0.2} (0 to N/4 of them);
  - half the seeds place the shallow pairs as a near-lattice block with the deep pairs inside or beside it; the other half are uniform random;
  - N ∈ {64, 128, 256}, 20 seeds per (N, y_lo), two relaxation passes per start.
  - Same rule as before: any LP < 0 confirmed in mp50 refutes.
- PREDICTION for e: no LP < 0. Deep pairs end at y = 0.8 and shallow pairs at y_lo. min LP ≥ 2 whenever a deep pair is present (as in family a: 2.88–3.63). The thinnest LP/Σy² comes from the largest shallow blocks at y_lo = 0.05.

**RESULT (round 7): SUPPORTS — min LP ≥ 0 in all 670 runs; prediction held.** Files: `mixed_search.py`, `round7_analyse.py`; logs `round7_ms_64_128.log`, `round7_ms_ab256.log`, `round7_ms_cd256.log`, `round7_ms_e{64,128,256}.log`; analyses `round7_analyse_abcd.log`, `round7_analyse_e.log`; results `round7_ms_*.json`; lowest configurations `round7_thinnest.json`. Double precision, local minima from the listed starts (L-BFGS-B, ftol 1e-15).
- No LP < 0, in float or in mp50. There are 135 mp50 re-evaluations (all 132 runs with float LP < 1, plus the 3 thinnest configurations with a deep pair); max |mp50 − float| = 8.5e-13.
- Validation: with depths fixed, rb16/rb32 reproduce round 4 (1.9597, mp50 1.95970380); the finite-difference gradient check passes.
- The minimiser always drives deep pairs to the bound y = 0.8, and shallow pairs either to their lower bound or (next to a deep pair) up toward 0.8.

| regime | runs | min LP | thinnest per-pair LP/#pairs | split at the min |
|---|---|---|---|---|
| real limit: every pair driven to y → 1e-3 (family d, and on-line multiplicity 2 in c) | 80 + 120 + 24 | 0.0978 (N = 64), 0.177 (128), 0.359 (256) | 0.0165 (d, N = 128) | LP = s(D) ≈ lattice value Nσ = 0.0875 / 0.175 / 0.350 plus ≤ 0.01; the certificate covers it |
| deep pair inserted into a shallow block (a) | 144 | **2.877** (N = 128, k = 1 centre, mp50 2.8767081389) | 0.049 (N = 256) | s(D) 5.46, Δ_B −2.58 |
| random mixtures, deep held deep (e) | 180 | 3.529 (N = 128) | 0.071 (N = 256) | s(D) 5.53, Δ_B −2.00; min LP/Σy² = 0.375 |
| shallow block flanked by deep pairs (b) | 54 | 18.36 (N = 256) | 0.278 | s(D) 11.8, Δ_B +6.5 |
| stacks under pSq, m ≥ 2 at y ≥ 0.8 (c) | 144 | 61.7 (N = 256) | 0.93 | — |

- Reading:
  - Every configuration with a pair at y ≥ 0.8 has LP ≥ 2.877.
  - The deep pair's Δ_B is negative (it couples to the block and its environment), down to −3.2, but s(D) of the doubled configuration exceeds it by at least 2.88.
  - Without deep pairs, the minimiser collapses the pairs to the real limit, where LP → s(D) ≥ 0 by the certificate itself.
  - Under pSq, stacks are strongly positive.
- Seeds (shared with bridge-port):
  - family d: 1000N + sd, sd = 0..39;
  - family e: 7000000 + 10000N + 100·round(100·y_lo) + sd, sd = 0..19;
  - families a, b, c are deterministic from `bulk_end_n4_starts.json`.
- Scope: local minima only. The global minimum is not certified. Depth ranges are as stated; deep pairs are limited to y ≤ 3 and N ∈ {64, 128, 256}.

## Round 8 (2026-10-09): the relative margin R = −Δ_B / s(D)

**PRE-REGISTRATION (written before any run; no R value computed yet).**
- Definitions (periodic model, pSq weights, the round-7 split):
  - LP = s(D) + Δ_B, with s(D) = E(D) − F_C^pSq(Z) ≥ 0 (D: each pair → an on-line point of mass 2m_i at s_i) and Δ_B = E(Z) − E(D).
  - R(Z) = −Δ_B / s(D). For s > 0, Lemma P ⟺ R ≤ 1. θ* = sup R.
  - Exactly, s(D) = P_h(D) + T_g(D), with T_g(D) = Σ_{a≠b} m_a m_b g_N(x_a − x_b).
  - Pair-local version: R_loc = −Δ_B / T_g^loc, where T_g^loc keeps only the terms of T_g with at least one of the two points within ±8 of a pair position (the step-8 slack convention: local T_g only, no P_h).
- Search:
  - maximise R directly (L-BFGS-B on −R with the analytic gradient (∇Δ_B·s − Δ_B·∇s)/s²);
  - all positions and depths free, y ∈ [1e-3, 3]; P ≤ 64; N ∈ {64, 128, 256}.
  - Starts:
    - (1) shallow rb blocks (round 4) at several starting depths;
    - (2) the round-7 thinnest mixed configurations;
    - (3) bridge-port's deep minimisers (`sat9/e38_best.json`) when available;
    - (4) stacks;
    - (5) random mixtures (block and uniform layouts);
    - (6) single-pair crowding configurations (a few doubles at ±0.8 around a pair; the Q₂ < 0 regime of the defect-gap analysis).
  - mp50 re-check of Δ_B and s(D) for every run with R > 0.9.
- Outcomes (lead's): θ* ≤ 0.8 means the relative target is viable; θ* ∈ (0.8, 1) means thin; R > 1 confirmed in mp50 means a counterexample.
- PREDICTION: **θ* ∈ [0.5, 0.8], central 0.65; P(θ* ≤ 0.8) ≈ 65%.**
  - Where I expect it: the moderate-depth crowding/mixed regime (a pair at y ≈ 0.3–0.8 with compressed shallow pairs or doubles nearby).
  - Where I do not: deep chains or stacks, where Δ_B is dominated by +‖S_B‖² ~ B² and R < 0; and the real limit y → 0, where R → 0.
  - Basis: the round-7 family-a minimum has R = 2.58/5.46 = 0.47, read off the logged split before this pre-registration (not a new computation), and maximising R rather than minimising LP should push past it.
  - R_loc: larger than R, plausibly > 1 in compressed blocks, where P_h carries much of s(D).

**RESULT (round 8): R > 1 CONFIRMED in mp50 — Lemma P (pSq) is REFUTED configuration-wise, by an ON-LINE zero of multiplicity M ≥ 5 flanked by a few off-line pairs.**
- Without on-line multiplicities ≥ 4, sup R by regime (`round8_rs_{64,128,256}.log`; polish `round8_polish_*.log`):

| regime | N = 64 | N = 128 | N = 256 | at the maximiser |
|---|---|---|---|---|
| shallow rb blocks, depths free | 0.440 | 0.530 | 0.596 | an arched sub-chain (≈ 8 pairs, y 0.38–0.63) inside a block whose other pairs collapse to y → 0 |
| mixed (round-7 configurations) | 0.458 | 0.530 | 0.597 | same shape |
| stacks (off-line, m = 3) | 0.485 | 0.577 | 0.640 (polished, not converged) | the stack collapses to y → 0; a deep arched chain (≈ 23 pairs up to y 1.4–1.8) beside it |
| random mixtures | 0.393 | 0.258 | 0.475 | — |
| deep chains (bridge-port's e38 seeds) | 0.378 | 0.324 | 0.336 | — |
| single-pair crowding by on-line doubles | 0.172 | 0.172 | 0.202 | — |

  - R grows with block size in these families (blocks: 0.44 / 0.53 / 0.60 at P = 16 / 32 / 64). R_loc > 1 at N = 256 (blocks 1.05, stacks 1.12): pair-local T_g alone does not cover −Δ_B, and P_h is needed.
- **The stack maximiser points to the counterexample.** At N = 256 the R-maximiser has the off-line stack (m = 3) collapsed to y = 0.001. Under pSq that item weighs 12 while its D-image has mass 6, so it inflates s(D) by 24·g(0) = 23.8. Replacing it by an ON-LINE zero of multiplicity 6 at the same point leaves E(Z) and E(D) unchanged and gives R = 0.9625, LP = +1.66 (`online_mult_probe.py`).
- Re-minimising LP with an on-line multiplicity M (`round8_onmult_{a,b,c}.log`, N = 256, P = 64; all mp50-confirmed):

| M | min LP | R |
|---|---|---|
| 3 | +1.555 | 0.39 |
| 4 | +0.0024 | 0.9996 |
| 5 | −3.198 | 1.38 |
| 6 | −8.1215 | 1.73 |
| 8 | −18.157 | 1.75 |
| 10 | −36.215 | 2.10 |
| 12 | −61.815 | 2.70 |

- Independent recomputation of the M = 6 minimum with bridge-port's `sat9/e15_exact_mult.py` energy() (the multiplicity as 6 coincident simple points): E(Z) = 406.13212436, F_C^pSq = 414.25366277, **LP = −8.12153841**. That equals my float value and the mp50 value to all printed digits.
- Structure of the M = 6 minimum:
  - the multiplicity-6 zero has no other on-line zero within 32.8;
  - pairs sit symmetrically at ±1.19, ±2.07, ±2.95 with depths 0.81 / 0.94 / 0.99 (an arched chain);
  - 38 of the 64 pairs have y > 0.002; the rest are near-line doubles.
- **Small, N-stable counterexamples** (`round8_onmult_small.json`; centred multiplicity M, P pairs symmetric at ±0.88k, then relaxed; all mp50-confirmed):

| N | M = 5, P = 4 | M = 5, P = 8 | M = 6, P = 4 | M = 6, P = 8 | M = 8, P = 8 | M = 4, P = 8 |
|---|---|---|---|---|---|---|
| 64 | −0.288 | −1.344 | −1.516 | −3.870 | −12.541 | −0.0017 |
| 128 | −0.200 | −1.254 | −1.426 | −3.776 | −12.432 | +0.086 |

  - The shift from N = 64 to 128 is ≈ +0.09, the lattice slack Nσ. So the violation is local and stable in N.
  - The pairs are SHALLOW: y ≤ 0.32 (M = 5, P = 4) and y ≤ 0.53 (M = 6, P = 8).
- Mechanism: the defect-gap expansion LP = s(D) + y²Q₂ + O(y⁴), with Q₂ = 4|K″(0)| − 2Σ_env m_b K″(x_b) and K″(0.79) = 3.53. A multiplicity-M neighbour at ≈ 0.8–1.2 from a pair drives Q₂ ≈ 24 − 7M negative for M ≥ 4. Meanwhile s(D) of an isolated multiplicity-M zero is small: its self-slack is (1 − g(0))M² ≈ 0.0096M².
- Scope and corrections:
  - Round 7 seeded on-line multiplicities only up to 3, so its SUPPORTS is scoped to M ≤ 3.
  - The single-pair certificate (§1 of the note) is for masses ≤ 2 and is unaffected.
  - The refutation is configuration-wise in the periodic model, as pre-registered. Under ordSq the same configurations fail too (pSq = ordSq on the line; the pairs here have distinct ordinates).
  - The Lean hypothesis LemmaPObjZ is asymptotic with an εN allowance. A bounded number of such clusters does not violate it; clusters of on-line multiplicity ≥ 5 at positive density would. Whether the actual zero configuration can contain them at positive density is a separate question, not addressed here.

## Round 9 (2026-10-09): validation of the lead's κ-neutral repair, linear weights pLin

**PRE-REGISTRATION (written before any run).**
- The repair:
  - weights w = 1 for a simple on-line zero, 2M for an on-line zero of multiplicity M ≥ 2, and 2m for an off-line zero of multiplicity m;
  - pLin = 2N − N₀ˢ exactly;
  - F_C^lin = ĥ(0)N + g(0)·pLin;
  - LP_lin = LP_pSq + g(0)·Σ_on (M² − w(M)). This differs from pSq only at on-line M ≥ 3.
- Note: for fixed multiplicities the shift is a CONSTANT, so LP_lin and LP_pSq have the same minimisers. The search therefore re-minimises LP over richer structures for each multiplicity pattern and re-scores.
- Families (N ∈ {64, 128, 256}, positions and depths free in [1e-3, 3]):
  - (i) one on-line multiplicity M ∈ {3, 4, 5, 6, 8, 10, 12, 16, 20} with P_near ∈ {2, 4, 8, 16} pairs around it, plus the round-8 configurations;
  - (ii) a multiplicity M ∈ {3, 4, 6, 8, 12} flanked by off-line stacks of m ∈ {2, 3, 4} pairs at ±d (d ∈ {0.5, 0.9, 1.5}), with single pairs around;
  - (iii) 2–4 multiplicities M ∈ {3, 4, 6, 8} at mutual distances 0.8–3, with pairs between and around;
  - (iv) the round-8 maximisers and minimisers re-scored under pLin.
- mp50 re-check of every LP_lin < 1. R_lin = −Δ_B / s_lin(D), with s_lin = s_pSq + g(0)·Σ_on(M² − w(M)), is maximised for families (i)–(iii) and reported alongside the round-8 values.
- Rule (lead's): REFUTES the repair if any LP_lin < 0 is confirmed in mp50. SUPPORTS if none; then report the thinnest margin and its scaling in M.
- PREDICTION: **SUPPORTS**, about 70% confidence.
  - The thinnest LP_lin should be at small M (3–5), ≈ 2–5.
  - The margin should grow in M roughly like (1 − c)M², with c = (−Δ_B)/M² ≈ 0.5–0.7 at the round-8 minimisers. Those already give LP_lin = +4.5 / +7.9 / +11.7 / +15.6 / +29.4 / +43.0 / +57.1 for M = 3 / 4 / 5 / 6 / 8 / 10 / 12.
  - Main risk is family (ii). An off-line stack near a multiplicity can shape S_B to anti-align with the multiplicity's large S_D more efficiently, pushing c toward 1. c rose from 0.54 at M = 6 to 0.68 at M = 12 in round 8. If c(M) → 1 faster than the 2M/M² slack term shrinks, LP_lin turns negative at large M.
  - R_lin prediction: sup ≈ 0.7–0.9, in family (ii) at large M.

**RESULT (round 9): SUPPORTS the pLin repair — no LP_lin < 0, and no LP_lin < 1, in any run; prediction held.** Files: `lin_search.py`; logs `round9_lin_i64.log`, `round9_lin_i256.log`, `round9_lin_rest.log`, `round9_lin_largeM.log`; results `round9_lin_*.json`. Double precision, local minima. No run fell below the mp50 threshold (min LP_lin = 3.12), so no mp50 re-check was triggered.

| family | thinnest LP_lin by M (min over N ∈ {64, 256}) | sup R_lin |
|---|---|---|
| (i) one multiplicity M with 2–16 pairs | M = 3: **+3.12**; 4: +7.67; 5: +12.47; 6: +17.80; 8: +29.85; 10: +43.73; 12: +59.37; 16: +95.89; 20: +139.87 | 0.07 (M = 3) rising to 0.64 (M = 20) |
| (ii) multiplicity flanked by off-line stacks m = 2–4 | M = 3: +19.07; 4: +23.98; 6: +39.73; 8: +61.98; 12: +114.81 | ≤ 0.22 |
| (iii) 2–4 multiplicities at spacing 0.8–3 | M = 3: +6.14; 4: +15.45; 6: +42.50; 8: +79.95 | ≤ 0.24 |
| (iv) round-8 configurations re-scored | M = 3: +4.53; 4: +7.92; 5: +11.66; 6: +15.65; 8: +28.99; 10: +40.07; 12: +54.89 | ≤ 0.65 |

- Scaling in M:
  - min LP_lin / M² = 0.35 (M = 3), 0.48 (4), 0.50 (5), 0.49 (6), 0.47 (8), 0.44 (10), 0.41 (12), 0.37 (16), 0.35 (20).
  - Beyond the spec, at N = 128 with P_near ≤ 32 (`round9_lin_largeM.log`; nit at the 40000 cap): 0.333 (16), 0.301 (24), 0.299 (32), 0.303 (48).
  - So LP_lin ≈ 0.30·M² at large M, with R_lin saturating at ≈ 0.69. The pairs capture ≈ 69% of the multiplicity's M²; the rest is margin.
- Stacks (ii) are not the risk I predicted: they raise the floor, since their own |S_B|² and pSq weight cost more than the extra coupling gains.
- Collateral (pSq, the convention the repair replaces), mp50-confirmed:
  - M = 4 is NOT just borderline. M = 4 with 16 pairs at N = 64 gives LP_pSq = −0.24873003. The round-8 failure threshold is therefore M ≥ 4.
  - M = 3 gives LP_pSq as low as +0.14625179 (2 pairs, N = 64): thin but positive.
- For M ≤ 2, pLin = pSq, so the round-7 results stand. sup R in the non-multiplicity regimes is unchanged (0.44–0.64; round 8).
