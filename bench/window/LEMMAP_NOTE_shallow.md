# Lemma P — state note, shallow regime (window-scope section, 2026-10-09)

The board route is paused, and this note records the state. Every number has a file pointer. Unless a path says otherwise, files are in
`bench/window/band1/`. The running record, with all pre-registrations, is `band1/D_TRACK_STATE.md`.

**Conventions.**
- Certificate v1 (`cert_R8_backed.json`, κ_cert = 0.6759645, σ = ĝ(0) − g(0) = 1.367e-3).
- D(Z) replaces each off-line pair s ± iy by an on-line double at s. Lemma P: LP := E(Z) − F_C(D(Z)) ≥ 0.
- **Line model** = one copy of ℝ; **periodic model** = period N, total mass N.
- Bounds are LP/y² per pair unless marked otherwise.
- **Weight convention (rounds 8–9, §8).**
  - Under the per-zero weights pSq (m² on the line, 2m off it), Lemma P is REFUTED configuration-wise in the periodic model, by an on-line multiplicity M ≥ 4.
  - The repaired weights pLin (1 for a simple on-line zero, 2M for an on-line multiplicity M ≥ 2, 2m off the line; pLin = 2N − N₀ˢ) pass the adversarial search.
  - §§1–5 are unaffected: they use on-line masses ≤ 2, where pLin = pSq.

**Rigour labels.**
- **[DP]**: computer-assisted, double precision, with explicit allowances (EPS = 1e-8 per tabulated value; tail and qf constants from finite differences × 1.05, checked against exact ψ with ratio ≤ 0.935). It is **not interval arithmetic**.
- **[exact-local]**: exact functional, evaluated at **local minima** from the stated starts. The global minimum is not certified.
- **[estimate]**: not computed as a bound.

## 1. Single pair, all y > 0 [DP; line model; P_h not used]

| y range | instrument | certified bound | file |
|---|---|---|---|
| (0, 0.4] | nearest-neighbour chain DP, all real D, masses ≤ 2 | LP ≥ 1.9531·y² (binding [0.1625, 0.175]) | `crowd_dp_X128_NY32.log` (`crowd_dp.py`) |
| [0.4, 0.9375] | chain DP with half-bin cluster charge (cap 24) | LP ≥ 13.648·y² (binding [0.4, 0.4125]) | `crowd_dp2_04_10.log` (`crowd_dp2.py`) |
| [0.6, 12] | half-bin bound, (u, y) grid 1/512 × 0.002, bilinear-corner error bounds | LP ≥ 0.0527·self(y) | `deep_cert_06_12.log` (`deep_cert.py`) |
| [10, ∞) | half-bin bound, analytic | LP ≥ 0.483·self(y); ≥ 0.568·self for y ≥ 12 | `deep_asym_Y12.log` (`deep_asym.py`) |

- self(y) = 2[K(2iy) − K(0)]. Handoff at y = 0.8 (DP 241·y², half-bin 0.208·self).
- Slack localised to ±8 of s, the multi-pair convention:
  - LP ≥ 1.3787·y² on (0, 0.4] (`crowd_dp_X128_NY32.log`, line 83);
  - LP ≥ 13.361·y² on [0.4, 0.8] (`crowd_dp2_04_08_loc8.log`).
- Under the ordSq multiplicity convention: covered for on-line zeros exactly at the pair's ordinate, since φ_y(0) > 0 (D_TRACK_STATE, "Multiplicity convention"). Coincident deep stacks are not covered.
- Interval-arithmetic upgrade: sized, not run (≈ 1 h of DP cell bounds plus ≈ 4 h for the deep half-bin certificate with mpmath.iv; D_TRACK_STATE, "Rigour upgrade").

## 2. Class (i): separated pairs, depths ≤ 0.8 [DP; line model]

- Method:
  - each pair gets an allocated share of the slack (a partition of unity);
  - the allocated single-pair DP bound is computed for each depth;
  - the exact B–B cross terms X_pq are charged per annulus to the deeper pair.
- Closure means min over y-intervals of (margin − X charge) > 0.

| separation rule | depths | min (margin − X charge) | files |
|---|---|---|---|
| ≥ 32 | ≤ 0.8 | +1.37·y² | `crowd_dp3_00_08.log`, `sep_xlemma_D32.log` |
| ≥ 16 | ≤ 0.8 | +1.35·y² | `crowd_dp4_D16.log`, `xlemma_exact_D16.log` |
| ≥ 8 | ≤ 0.7375 | +0.98·y² | `crowd_dp4_D8.log`, `xlemma_exact_D8.log` |
| ≥ 4 | ≤ 0.1875 | +0.038·y² | `crowd_dp4_D4.log`, `xlemma_exact_D4.log` |
| **mixed depths**: \|s_p − s_q\| ≥ L(y_p) + L(y_q), with L = 2 (y ≤ 0.1875), 4 (0.1875 < y < 0.625), 14 (0.625 ≤ y ≤ 0.8) | ≤ 0.8 | +0.038·y² / +0.19·y² / +9.6·y² | `crowd_dp4_mix{A,B,C14}.log`, `xlemma_mix{A,B,C14}.log` |

- For separations 8 and 4, the logs' final "NOT closed" lines cover the whole range y ≤ 0.8. The closures above are the minima over the depth ranges stated: y ≤ 0.7375 gives +0.9844, and y ≤ 0.1875 gives +0.038.
- **Allocation is EXHAUSTIVE**: sup_x Σ_p c_p(x) ≤ 0.9949 over all class sequences (the first 10 neighbours per side enumerated; the rest bounded classwise) (`mixed_alloc_exhaustive.log`). Non-cluster weights sum to 1 by the Voronoi complement. This replaces an earlier sampled 0.957.
- Pairs deeper than 0.8, and mixed shallow/deep separated configurations, are on bridge-port's side.
- am-cert fit conditions (round 5; `crowd_dp4_banded.py`):
  - **C2, banded DP — PASS** at r = 1, 2, 4 for all three mixed classes (`round5_banded_{A,B,C14}.log`).
    - r = 2 and r = 4 equal the unbanded DP to 4 decimals in all 64 intervals.
    - r = 1 gives +0.0205 / +0.1811 / +9.6124.
  - **C3, monotonicity — PASS**: W[m, p, k] is non-decreasing in the cluster count p in every entry (0 violations).
  - **"≤ 3 replay levels" — PARTIAL**:
    - the saturation level p* is ≤ 1 in A, ≤ 5 in B (y ≥ 0.55) and ≤ 14 in C14;
    - every level above 2 sits in the first two half-bins (u < 1), apart from one cell in B at u ∈ [64, 129) with p* = 3;
    - that is ≤ 257 of 7296 cells per interval (same logs).

## 3. The density lemma DV and its two instances [exact pencil]

**DV.** Periodic model, any weight ρ ≥ 0 on the frequency axis. For every real mean-zero test function v whose Fourier coefficients c_j are
supported where ρ > 0:

  (1/N) Σ_{j≠0} ρ_j |S_j|² ≥ 2 Σ_a M_a v(x_a) − (1/N) Σ_{j≠0} |c_j|²/ρ_j.

Proof: |ρS − c|² ≥ 0 termwise. In a DP it enters as a one-body potential plus a constant, with no new state.

**Instances.**
- **ρ = ĥ**: the P_h density lemma, used by every dense-block certificate in §4. It has two test functions:
  - low band: v = t_L(w − ∫w/N), with w = 1_R * β sinc²(β·), β = 1/32;
  - band beyond α = 1: v = t_B(ĥ_W·Ŝ_pairs)^∨.
  Round 3 adds a far profile f = λ(D/(D + d_out))^κ to the low-band w (an instance of the same lemma).
- **ρ = q·1_{|α|≤δ}**: bridge-port's Lemma LL, the configuration-adapted case with v built from V = Σ_p e(α s_p).
- Source: D_TRACK_STATE, "Density lemma" and "Shared lemma DV".

## 4. Certified dense-block bounds [DP; line model; per-geometry parameters]

All are computed by `multi_env_dp.py`: Q_pp exact, plus T_pp, plus a chain-DP environment, plus tails, plus the density-lemma constant.

**Saved hardest geometries** (relaxed periodic minimisers; `multipair_geoms.json`). All are rerun with the corrected code and the original parameters (t_B = 0.5, RES = 256):

| geometry | parameters (XR, t_L, XL) | certified LB (corrected code) | earlier value (round-2 code) | P_h-free LB | exact periodic LP |
|---|---|---|---|---|---|
| block16, Y = 0.2 | 20, 0.005, 128 | **+0.155** | +0.143 | −0.265 | 2.32 |
| block16, Y = 0.4 | 20, 0.005, 128 | **+0.584** | +0.273 | −0.95 | 7.20 |
| comp8, Y = 0.4 | 20, 0.005, 128 | **+0.462** | +0.424 | −0.023 | 1.57 |
| comp8, Y = 0.2 | 10, 0.005, 128 | **+0.121** | +0.113 | +0.045 | 0.53 |
| comp4, Y = 0.4 | 20, 0.005, 128 | **+1.258** | +1.227 | +0.812 | 2.52 |
| block32, Y = 0.4 | 10, 0.005, 512 | **+0.658** | +0.191 | — | 9.68 |
| block64, Y = 0.2 | 20, 0.008, 512 | **+0.891** | +0.761 | — | 5.12 |
| block64, Y = 0.4 | 20, 0.008, 512 | **+1.140** | +0.172 | — | 11.67 |
| block64, Y = 0.4 | 40, 0.008, 512 | **+1.502** | +0.530 | — | 11.67 |

- Files:
  - corrected values: `round6_rerun_A.log` and `round6_rerun_B.log`;
  - earlier values: `multi_env_dp_density_certs.log`, `multi_env_dp_scan5.log` (comp8, Y = 0.2), `multi_env_dp_b64scan.log` (XR = 40);
  - P_h-free column: `multi_env_dp_XL128.log`.
- Per-pair margins (corrected): 0.0097 (block16, Y = 0.2) to 0.31 (comp4). For blocks of ≥ 16 pairs: 0.0097–0.037.

**Graded relaxed family** rb16/32/64 (N = 4P, `bulk_end_relaxed.json`; corrected code):

| Y | P = 16 | P = 32 | P = 64 | slope per pair (16 → 64) | parameters | files |
|---|---|---|---|---|---|---|
| 0.4 (far profile) | +1.431 | +1.792 | +2.359 | **0.0193** | XL = 1024, XR = 20, t_L = 0.016, λ = 0.1 / 0.2 / 0.45 | `round3_far_E_rb16_32.log`, `round3_far_rb64.log` |
| 0.2 | +0.352 | +0.571 | +0.950 | **0.0125** | XL = 512, XR = 20, t_L = 0.008 / 0.008 / 0.012 | `round6_rerun_C.log` |

- The earlier Y = 0.2 row was +0.315 / +0.531 / +0.882 (slope 0.0118) with the round-2 code (`round2_scan6_Y02.log`).
- Thinnest available margin: m_bulk(a → 1⁻) = 0.018–0.022 per pair for t_L = 0.008–0.016 (`bulk_end.py`, Poisson).
- **Allowance correction (closed).** The round-2 code's cell lower bound for the low-band w used |w′| ≤ 2β·max f, but TV(k_β) = 2.388β.
  - The corrected code (`multi_env_dp.py`, round 3 onwards) takes the larger of two bounds: the midpoint bound with 2.4β, and min of the endpoint values − (2π)²β³/6·Σf/8·h²/8.
  - The corrected code also carries the round-2/3 far-field repairs: the signed IBP lead for φ beyond u = 128, and the h_W table to u = 300, with CW/u² beyond.
  - All rows above are now from the corrected code. **No row changed sign; every row increased.** The increase comes from the other bound improvements, not from the 2.4β term, which on its own can only lower a bound.

## 5. Exact local-density results [exact-local; periodic model; depths fixed and equal; double precision]

Quantity: exact relaxed LP − Σ_p m_bulk(a_p), where a_p is the mean of the adjacent spacings and t_L is as in round 2 (`exact_n16.py`).
- Starts: (a) contiguous vacancies; (b) spread vacancies; (c) stretched environment.
- Start (b) is lowest in all 12 cases.
- L-BFGS with ftol 1e-15 and gtol 1e-9; start (a) reproduces the round-1 values exactly.

| Y | P | N = 4P (lowest of 3 starts) | N = 16P (lowest of 3 starts) |
|---|---|---|---|
| 0.2 | 16 / 32 / 64 | +0.577 / +0.800 / +1.009 | +0.549 / +0.889 / +1.365 |
| 0.4 | 16 / 32 / 64 | +2.388 / +2.489 / +2.748 | +2.076 / +2.257 / +2.745 |

- Files: `round4_n4_starts.log`, `round4_n16_Y02.log`, `round4_n16_Y04.log`; geometries in `bulk_end_n4_starts.json` and `bulk_end_n16_Y0{2,4}.json`.
- The pre-registered N = 16P decision test **SUPPORTS** the local-density shape: the quantity increases in P at both Y.
  - The environment density within 40 of the block ends is 0.90 at N = 16P, against 0.65 at N = 4P.
  - The environment locks to the block's phase (|⟨e(x)⟩| 0.54–0.98).
  - Locking lowers the margin at P = 16 (by 0.03 / 0.31) but not at P = 64.
- Correction on record: round 2 reported N = 4P values from start (a) only (+0.85 … +4.10). Those were overstated by 0.36–1.55.
- The CERTIFIED analogue does not have this shape: LB − Σ m_bulk(a_p) = −2.61 / −3.15 / −3.85 at Y = 0.4 with the round-3 bounds (t_L = 0.016), decreasing in P (`round2_local_density.log` for round 2; recomputed with the round-3 LBs in D_TRACK_STATE round 3).

## 6. Refuted instruments and shapes (one line each)

- **Pairs-in-the-DP-alphabet** [estimate, not built]: infeasible by orders of magnitude. ĥ ≤ 2.2e-3 on 1/16 < |α| < 1, where the pair field lives, so a Cauchy–Schwarz pair weight would be ~10⁶y⁴. A real-space far coupling needs range r ~ 10³ against margins of 0.0027–0.05 per pair (D_TRACK_STATE, "Pairs-in-the-DP-alphabet").
- **(C) geometry reduction** ("uniform interior plus edge spacing is worst"): REFUTED, pre-registered. The relaxed bound is below its U1 comparator in 6 of 8 geometries, by up to 3.15 (block64, Y = 0.4) (`plausibility_C.log`). The boundary layer is ≥ 8–16 spacings for long blocks at y = 0.4 (`plausibility_C_edge.log`).
- **Bulk/end lemma** (deficit LB − P·m_bulk(a_c) bounded in P): REFUTED, pre-registered. At Y = 0.4 the deficit is −0.95 / −1.56 / −2.58, with grading length ≈ 0.07P (`bulk_end_analyse.log`, round-2 code).
- Also, each a property of the named instrument:
  - concavity reduction for clusters, field amplification μ = 1.5 → −0.62·y² at y ∈ [0.10, 0.15] (`cluster_dp_coarse.log`);
  - the P_h-free joint DP on compressed blocks, e.g. block16, Y = 0.4 → −0.95 (`multi_env_dp_XL128.log`);
  - the certified local-density shape (§5);
  - a hard-bin quadratic minorant c·L_b·sinc²(αL_b) ≤ ĥ is impossible for every c > 0, because ĥ ≡ 0 on [1.25, 1.3125], [1.5, 1.906], [2.4375, 2.469], [2.531, 2.8125], [2.969, 3] (D_TRACK_STATE round 3, computed from `bulk_end.py`'s ĥ);
  - the mass-count DP is estimated not worth building: ≈ 0.002–0.005 per pair beyond a matched linear charge [estimate] (D_TRACK_STATE round 3).

## 7. Open items

1. **Geometry covering.** Every dense-block certificate (§4) is for one geometry, with parameters tuned to it. No lemma covers all dense-block geometries.
   - The (C) reduction is refuted, and the alphabet DP is estimated infeasible.
   - A box B&B would need a reduction family with a graded edge (≈ 3–4 parameters plus depth; D_TRACK_STATE, "(C)" follow-up).
   - The exact-functional evidence (§5) is local minima from three start families.
   - Not covered by any instrument here: unequal depths inside a block (numerics only), mixed shallow/deep clusters, coincident stacks under ordSq.
2. **Certificate environment relaxation.** In the line-model DP:
   - bonds are nearest-neighbour only;
   - density charges are linear (dual);
   - there is no mass conservation.
   As a result the certified slope (0.0193 per pair at Y = 0.4) is below the bulk margin available to it (Σ m_bulk grows by 0.046 per pair).
   - Where the loss sits (`round2_chain_diag.log`, `round3_chain_diag_far.log`): a density-1 environment phase-locked to the block collects the block's coherent far field. That is ≈ −0.42 / −0.83 / −1.41 beyond distance 20 on rb16/32/64 at Y = 0.4 [estimate from the DP chain], growing roughly like ln P.
   - Exact cost of a density-2 stretch, for reference (N = 4096): low band → ĥ(0)·L; total 0.026 per unit length with spread vacancies, 0.033 contiguous, 0.29 by lattice stretching (`round3_stretch_ph_N4096*.log`).
3. ~~Rerun of the round-2-code certificates with the corrected w bound.~~ **CLOSED** (`round6_rerun_{A,B,C}.log`). All 9 saved-geometry runs and the Y = 0.2 graded row were rerun with the original parameters. No sign change; every value rose (§4).
   - The comparison numbers in §6 for (C) and bulk/end are from the earlier code and were not rerun. Each compares geometries under one code version.
4. **Rigour.**
   - Interval arithmetic: sized, not run (§1).
   - Line model vs periodic model: image control is not written.
   - C3: the deep cluster levels next to the pair (§2) set the replay depth.
5. **Relative margin without multiplicities** (§8). sup R = 0.44–0.64 at P ≤ 64, and still growing with block size. The supremum over all block sizes is not settled.
6. **The pLin hypothesis in Lean** (DEPLin.lean, am-cert) and its numerical status (§8, round 9) are local minima only. The global minimum is not certified.

## 8. Full-functional truth checks and the weight repair (rounds 7–9) [exact-local; periodic model; double precision, with mp50 re-checks as stated]

All quantities are computed on the full exact functional:
- LP = E(Z) − F_C(D(Z)), with d = Σ_{0<j<N} q(j/N)|S_j|² (non-negative terms; no large cancellation);
- the split LP = s(D) + Δ_B, with s(D) = E(D) − F_C ≥ 0 (D: each pair replaced by an on-line point of mass 2m) and Δ_B = E(Z) − E(D);
- g_N(0) = g(0) exactly for N ∈ {64, 128, 256}.
Code: `band1/mixed_search.py` (LP and its mp50 evaluation `lp_mp`), `band1/ratio_search.py` (R), `band1/lin_search.py` (pLin). The full record is in `band1/D_TRACK_STATE.md`, rounds 7–9.

**Round 7 — mixed shallow/deep clusters, pSq: SUPPORTS, scoped to on-line multiplicity M ≤ 3.**
- Scale: 670 runs (N ∈ {64, 128, 256}); no LP < 0. There were 135 mp50 re-evaluations, with max |mp50 − float| = 8.5e-13.
- Logs: `round7_ms_*.log`, `round7_analyse_{abcd,e}.log`. Configurations: `round7_thinnest.json`.
- Every configuration with a pair at y ≥ 0.8 has LP ≥ **2.877** (a y = 0.8 pair inside a 32-pair shallow block at N = 128; mp50 2.8767081389).
  - Its split is s(D) = 5.46, Δ_B = −2.58.
  - Thinnest per pair: 0.049 (N = 256).
  - Flanked blocks ≥ 18.4; off-line stacks (m ≥ 2, y ≥ 0.8) ≥ 61.7.
- Deep pairs always relax to the bound y = 0.8. When depths are free, pairs collapse to y → 0, where LP → s(D) ≈ Nσ (the certificate's own slack).
- Scope: on-line multiplicities were seeded only up to 3.

**Round 8 — relative margin R = −Δ_B/s(D), pSq: R > 1 CONFIRMED, so Lemma P under pSq is REFUTED configuration-wise at on-line multiplicity M ≥ 4.**
- Logs: `round8_rs_{64,128,256}.log`, `round8_polish_*.log`, `round8_onmult_{a,b,c}.log`, `round9_lin_i64.log`. Configurations: `round8_onmult_{a,b,c}.json`, `round8_onmult_small.json`, `round9_lin_i64.json`.
- The configuration: an on-line zero of multiplicity M flanked by a few off-line pairs (shallow, or an arched chain).
- Minimum LP_pSq, all mp50-confirmed:

| M | N = 64 (small configurations) | N = 256, 64 pairs |
|---|---|---|
| 3 | +0.14625179 (2 pairs) | +1.555 |
| 4 | **−0.24873003** (16 pairs) | +0.0024 |
| 5 | −0.288 (4 pairs, y ≤ 0.32); −1.344 (8 pairs) | −3.198 |
| 6 | −1.516 (4 pairs); −3.870 (8 pairs) | **−8.12153841** |
| 8 | −12.541 (8 pairs) | −18.157 |
| 10 | — | −36.215 |
| 12 | — | −61.815 |

- Independent code: bridge-port's `sat9/e15_exact_mult.py` energy() reproduces the M = 6, N = 256 value to all printed digits (E(Z) = 406.13212436, F_C^pSq = 414.25366277).
- The violation is local: the N = 128 values sit ≈ 0.09 (= Nσ) above the N = 64 values.
- Mechanism (defect-gap expansion): LP = s(D) + y²Q₂ + O(y⁴), with Q₂ = 4|K″(0)| − 2Σ_env m_b K″(x_b) and K″(0.79) = 3.53.
  - A multiplicity-M neighbour at ≈ 0.8–1.2 from a pair gives Q₂ ≈ 24 − 7M < 0 for M ≥ 4.
  - Meanwhile the isolated multiplicity's own slack under pSq is only (1 − g(0))M² ≈ 0.0096M².
- How it was found: the stack-regime R-maximiser had an off-line stack (m = 3) collapsed to y → 0. Under pSq its weight 4m = 12 inflates s(D) by 24·g(0) compared with an on-line multiplicity-6 point; exchanging the two gives R = 0.96.
- Without on-line multiplicities ≥ 4, sup R at N = 64 / 128 / 256 by regime:

| regime | N = 64 | N = 128 | N = 256 |
|---|---|---|---|
| shallow blocks, depths free | 0.44 | 0.53 | 0.60 |
| mixed | 0.46 | 0.53 | 0.60 |
| off-line stacks | 0.49 | 0.58 | 0.64 |
| random | ≤ 0.48 | | |
| deep chains (bridge-port's e38 seeds) | ≤ 0.38 | | |
| crowding by on-line doubles | ≤ 0.20 | | |

  - The maximisers are arched sub-chains inside blocks whose other pairs collapse to y → 0. R grows with block size.
  - R_loc (pair-local T_g within ±8 only) exceeds 1 at N = 256 (1.05–1.12): P_h is needed.
- Scope for the Lean form: the refutation is configuration-wise in the model. The asymptotic Lean hypothesis has an εN allowance, so only a positive density of such clusters would violate it. ordSq fails on the same configurations (pSq = ordSq on the line).

**Round 9 — the repair pLin: SUPPORTS.**
- Weights: 1 for a simple on-line zero, 2M for an on-line multiplicity M ≥ 2, 2m off the line. So pLin = 2N − N₀ˢ and LP_lin = LP_pSq + g(0)·Σ_on(M² − 2M).
- κ is unchanged: the κ chain uses only 2N ≤ p + N₀ˢ.
- Files: `round9_lin_{i64,i256,rest,largeM}.log`, `round9_lin_*.json`.
- No LP_lin < 0 and no LP_lin < 1 in any run, so no mp50 trigger.
- Thinnest margin, by family:

| family | M = 3 | 4 | 5 | 6 | 8 | 10 | 12 | 16 | 20 |
|---|---|---|---|---|---|---|---|---|---|
| one multiplicity with 2–16 pairs | **+3.12** | +7.67 | +12.47 | +17.80 | +29.85 | +43.73 | +59.37 | +95.89 | +139.87 |
| off-line stacks (m = 2–4) flanking | +19.07 | +23.98 | — | +39.73 | +61.98 | — | +114.81 | — | — |
| 2–4 multiplicities at spacing 0.8–3 | +6.14 | +15.45 | — | +42.50 | +79.95 | — | — | — | — |

- Scaling:
  - min LP_lin/M² = 0.48–0.50 at M = 4–6, falling to 0.35 at M = 20.
  - A trend check beyond the spec (N = 128, ≤ 32 pairs, iteration cap reached) gives 0.33 / 0.30 / 0.30 / 0.30 at M = 16 / 24 / 32 / 48, i.e. LP_lin ≈ 0.30·M².
- R_lin: one multiplicity 0.07 (M = 3) rising to ≈ 0.69 (M ≥ 24); stacks ≤ 0.22; multiple multiplicities ≤ 0.24.
