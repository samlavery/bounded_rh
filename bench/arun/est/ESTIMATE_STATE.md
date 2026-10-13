# window-scope — estimate round on R. Arun Chandru's "master-of-puppets" (MOP) chain (2026-10-10)

Workspace: `bench/arun/est/` (new files only). `bench/arun/MOP_Solution.lean` is read-only.

## Their κ chain, as read at source (MOP_Solution.lean)
- `Opeth.AMCounting.defect_to_dyadic` (l. 23488 ff.) with `proposedQ_identity`: (1 − c)·κ = H_lo − B.
  - c = cFloor = 805124/10⁸ (PC8C5BF floor), B = pressureSum = 404350/10⁸, H_lo = 67216841/10⁸ (AMW.HW_ge).
  - κ = 66812491/99194876 = 0.67354780.
- The defect input is `ActualDefectEstimate`: (c − 28δ)·n − B·R − 7c ≤ Dcirc, for the WHOLE retained set (n points, span R ≤ (1+δ)N).
  - Proved by `matching_defect_bound` (l. 23340): a maximal matching at d = 17/20 pinches the Gram matrix into 2-point close-pair blocks, each with defect ≥ 2c − 4δ (wfun ≥ 1/64 at distance ≤ 17/20, c ≤ 1/64), plus ONE separated remainder.
  - The remainder: `remainder_bound` (l. 23095). Spectrum ≤ 2 (separated-set Gram bound normS = 19/10 on 17/20-separated sets, `AMSeparatedSpectrum`) gives offdiag² ≤ defect. The eight-point certificate on consecutive remainder points gives (c − 28δ)m − B·R − 7c.
  - So the endpoint loss is a single 7c in total, and the pressure is charged on the full span.

## PRE-REGISTRATION (written before any computation in this round)
- (a) Edge windows. Prediction: they CANNOT add to their κ, gain 0 at leading order.
  - In their chain the only endpoint loss is one 7c (a single remainder block), absorbed into δN.
  - The pressure is B·R on the whole span, with no per-block (m − 7)/m factor for edge certificates to recover.
  - Edge windows helped us only through the finite block length m = 148 of the √-band chain.
- (b) Sensitivities of κ = (H − B)/(1 − c), analytic: ∂κ/∂c = κ/(1 − c) = 0.679, ∂κ/∂B = −1/(1 − c) = −1.008, ∂κ/∂H = +1.008.
  - normS, d and clipC do not appear in the formula. They enter only as feasibility constraints: normS(d) + O(δ) ≤ clipC = 2 for the cap, and wfun(d) ≥ c for the pair blocks.
  - One indirect route: the remainder certificate is only ever applied to gaps ≥ d. So hCert could be restricted from g ≥ 0 to g ≥ d, which raises the floor c if the unrestricted minimiser of Fw has a gap < d.
- (c) Position: their chain is the m → ∞ limit of the class form κ = (mH − P)/(m − R), so it lies inside Gebendorfer's clipped-Gram class. Caps: R8 dual cap with exact trace 0.6737854 (room ≈ 2.4e-4 above 0.6735478); class cap 0.674034.
- PREDICTION, best single gain: re-certifying W8 on the separated domain g ≥ 17/20.
  - With the SAME weights: < 1e-5 (≈ 60%), because I expect the binding configurations to be the balanced words with gaps ≈ 1–2.
  - With weights re-optimised on that domain: +3e-5 to +1.5e-4 in κ.
  - The next-best is more points (n = 9: ≤ 3e-5 from the round-8 jump map; rank 15 idealised ≈ +1e-4).

## RESULTS (computed after the pre-registration above)
Files: `fw_min.py`, `fw_min.log`, `dscan.py`, `dscan.log` (its restricted minima are LOCAL; superseded by `fw_words.log`), `fw_words.py`, `fw_words.log`, `hw_exact.log`. Double precision for Fw; mpmath for H.
- Validation: the weights are parsed from MOP's aW8/bW8 (B = 0.0040435 ✓, max spanMass = 2 ✓). min Fw over g ≥ 0 = 0.00805165 ≥ cFloor 0.00805124 ✓, so the certificate floor sits 4.1e-7 below the true minimum.
- **(a) Edge windows: gain 0, structural.** Their defect bound has one remainder block with a single 7c endpoint loss (absorbed by δN in `defect_to_dyadic`), and the pressure is B·R on the whole span. There is no (m − 7)/m factor for edge certificates to recover; coverage would enter only that O(1) constant.
- **(b) F and sensitivities.** F: κ = (H − B)/(1 − c), read at source (`proposedQ_identity`).
  - ∂κ/∂c = κ/(1 − c) = +0.6790; ∂κ/∂B = −1/(1 − c) = −1.0081; ∂κ/∂H = +1.0081.
  - ∂κ/∂normS = ∂κ/∂d = ∂κ/∂clipC = 0. They are feasibility constraints only: normS(d) + O(δ) ≤ clipC = 2, and wfun(u) ≥ c on [0, d] for the close-pair blocks.
  - wfun(0.95) = 0.0124, wfun(1.00) = 0.0036, so the pair blocks cap d at ≈ 0.97.
  - Restricting the certificate domain to gaps ≥ d gives EXACTLY 0. W8's binding words have gaps 1.043 / 1.973–1.983 (word-seeded global search over {1.04, 1.97, 2.93}^7). The restricted minimum equals the unrestricted 0.00805165 for every d ≤ 1.03, and only rises at d = 1.05 (0.00806537), where the pair blocks are infeasible.

  | sharpening | Δ of the input | Δκ | cost |
  |---|---|---|---|
  | certified floor → true min of W8 | c +4.1e-7 | +2.8e-7 | re-run the cover at relative margin < 5e-5; leaf count unknown |
  | H bound → exact H_W = 0.672168410564 | H +5.6e-10 | +5.7e-10 | one rational lemma |
  | separation d, normS, clipC | — | 0 | — |
  | domain restriction g ≥ d (feasible d ≤ 0.97) | — | 0 | — |
  | re-optimised (a, b) for the linear objective | — | second order, ≈ 0 (not computed) | — |
  | n = 9 window (round-8 jump map) | — | ≤ +3e-5 | certificate ~10× larger; MOP is 1,858,713 B against the 2,000,000 B cap, and its certificate payload is ≈ 323 KB of long lines |
  | two-level long-range (rank ≥ 8) credit (jump map) | — | ≤ +3.1e-5 | new block-level Lean argument |

  - Why re-optimisation is second order: our PC8C5BF weights maximised Φ at m = 148 on the near-linear branch (dΦ ∝ Φ·dc − dB), the same trade-off as dκ ∝ κ·dc − dB here.
- **(c) Position.** Their chain is the m → ∞ member of the class form κ = (mH − P)/(m − R), so it is inside Gebendorfer's clipped-Gram class.
  - It is 2.38e-4 below the R8 dual cap with exact trace (0.6737854) and 4.86e-4 below the class cap 0.674034.
  - The room is long-range Bragg energy at ranks 8–60 (round-8 jump map: idealised κ(15) − κ(7) ≈ 1.0e-4 and κ(∞) − κ(7) ≈ 1.8e-4 at m = 152). Capturing it needs a block-level certificate or an out-of-class input.
  - Largest CHEAP gain: the certified-floor tightening, +2.8e-7. That is strictly positive, which is all the board's strict-improvement rule requires. Largest realistic gain: ≤ 3e-5 (n = 9 or two-level credit), and neither is cheap.
- Prediction check:
  - (a) = 0 held.
  - "same-weight domain restriction < 1e-5" held (exactly 0).
  - My "re-optimised on that domain +3e-5 to +1.5e-4" is NOT supported. The binding words have every gap ≥ 1.04, above the feasible d ≈ 0.97, so the restriction removes no binding constraint. The expected gain is ≈ 0 (not computed by LP).
  - The best single gain is therefore not the one I predicted.

## Round 2 (lead's redirect): ceilings for re-optimised certificates on κ = (H − B)/(1 − c)

**PRE-REGISTRATION (written before any computation in this round).**
- Dual derivation (mine):
  - For any shift-invariant gap measure μ with mean gap d, averaging the n-point certificate over windows gives c ≤ B·d + Σ_{s ≤ n−1} spanMass(s)·w̄_s(μ) ≤ B·d + E_{n−1}(μ), with E_R = 2Σ_{s=1}^{R} w̄_s (capacity ≤ 2 per rank, WCert.Adm).
  - In the chain the remainder's mean gap is R/n ≈ N/n₀ = 1/κ. Setting d = 1/r, κ ≥ r requires H − B ≥ r(1 − c) ≥ r − B − r·E_{n−1}. B cancels, so κ ≥ r requires H ≥ r(1 − e_{n−1}(1/r)), where e_R(d) is the lower convex envelope over periodic-word mixtures at mean gap d.
  - Ceiling κ_n* = root of H = r(1 − e_{n−1}(1/r)).
  - With all ranks (E_∞ = Ef) this is Gebendorfer's Lemma 5.1, so the n → ∞ value must reproduce the R8 window cap (≈ 0.67379–0.67381).
  - The ceiling ignores the pointwise-vs-ergodic (coboundary) loss, ≈ +0.1% of c ≈ 5e-6 in κ for PC8SF.
- PREDICTIONS:
  - (1) The n = 8 ceiling is NOT 0.6737854 (that is all-rank). It is ≈ 0.67357–0.67362, a gap of +2e-5 to +7e-5 above 0.6735478. PC8C5BF optimised nearly the same trade-off (dΦ ∝ Φ·dc − dB at m = 148), and at m = 152 the idealised rank-7 credit was +4.3e-5 over PC8SF.
  - (2) n = 9 adds +2e-5 to +3e-5 over n = 8; n = 10 adds a further +1e-5 to +2e-5. The long-range energy spreads over ranks 8–60.
  - (3) Window re-optimisation: the all-rank per-window caps range from R8's 0.673816 to the class maximum 0.674039 (+2.2e-4). For n = 8 frames I predict a smaller gain, +2e-5 to +6e-5.

**RESULTS (round 2).** Files: `rank_ceiling.py` with logs `rank_ceiling_r8_789.log`, `rank_ceiling_r8_15inf.log`, `rank_ceiling_famcg.log`, `rank_ceiling_rwin*.log`; `window_grad.py` with `window_grad_R7.log`. Double precision. Periodic words q ≤ 8 on a 0.01 d-grid plus structured [a,b]/[a,a,b] words.
- Upper-bound caveat: each obstruction is a valid upper bound. A richer word set can only LOWER these ceilings, so they are upper bounds that may be loose by a few e-6.
- Consistency: the all-rank (n = ∞) value 0.67381025 matches capscan's R8 cap (0.6738084 tightened) to 2e-6, and every frame ceiling lies above the certificate actually achieved.

| frame | ceiling κ_n* (R8 window) | gap to MOP 0.6735478 | binding words at d = 1/κ* |
|---|---|---|---|
| n = 8 (rank 7) | **0.67356383** | **+1.60e-5** | q=5 at d 1.41 and q=2 at d 1.51 |
| n = 9 | 0.67360469 | +5.69e-5 | same |
| n = 10 | 0.67365060 | +1.03e-4 | q=8 at d 1.38 and q=2 at d 1.51 |
| n = 16 | 0.67373615 | +1.88e-4 | — |
| n = ∞ (class form, all ranks) | 0.67381025 | +2.62e-4 | — |

- (1) The n = 8 ceiling is 0.6735638, not 0.6737854 (that is the all-rank cap, ≈ 0.67381 here). Re-optimising the 8-point (a, b) can gain at most +1.6e-5. Subtracting the pointwise-vs-ergodic (coboundary) loss of ≈ 5e-6 measured for PC8SF leaves a realistic ≈ +1e-5.
- (2) n = 9: +5.7e-5. n = 10: +1.03e-4. The increments per added point are +4.1e-5 and +4.6e-5.
- (3) Window, on the n = 8 ceiling:
  - the all-rank class-optimal window (fam_cg_K24) gives 0.67321839, i.e. −3.3e-4 (H drops to 0.67188);
  - typh7_n8 gives 0.67355060 (−1.3e-5 vs R8);
  - rwin8_try1 and rwin8_B440000 have R8's window (identical);
  - local finite-difference ascent from R8 (4 steps, each re-checked with the full word search) only went DOWN: −0.9e-5 to −2.7e-5. The local two-word model predicted gains, but new binding words appeared, so R8 sits at a multi-word balance.
  - No window gain was found at n = 8 in the tested directions. Windows for n ≥ 9 were not optimised.
- Prediction check:
  - (1) predicted 0.67357–0.67362 (gap 2e-5 to 7e-5); actual 0.6735638 (gap 1.6e-5), just below the range. "Not 0.6737854" held.
  - (2) predicted per-point increments of +1e-5 to +3e-5; actual +4.1e-5 / +4.6e-5. I underestimated.
  - (3) predicted +2e-5 to +6e-5; none found. Not supported.

## Round 3: direct optimisation of (a_ij, b_r) for κ_n = (H − B_n)/(1 − c_n), n = 9 and 10; gap domains; binding words

**PRE-REGISTRATION (written before any computation in this round).**
- Method:
  - cutting-plane LP (HiGHS) over a_ij ≥ 0, b_r ≥ 0 and c, under the reflection symmetry MOP's certificate has (hsym), the capacity Σ_{j−i=s} a_ij ≤ 2, and Fw(g) ≥ c for g in a working set;
  - Dinkelbach outer loop: maximise κ·c − B, then κ ← (H − B)/(1 − c);
  - separation oracle: the global minimum of Fw over gaps in [lo, 40] (word-seeded starts {1.04, 1.97, 2.93}^{n−1}, plus random starts, plus the working set);
  - reported c_n = the TRUE minimum of the final weights (not a certified floor). Validation: n = 8 must land between MOP (0.6735478) and the n = 8 ceiling (0.6735638).
- PREDICTIONS:
  - n = 8 re-optimised: +0.5e-5 to +1.2e-5 over MOP.
  - n = 9: κ_9 − 0.6735478 = +3e-5 to +4.5e-5 (the ceiling +5.7e-5 less a ≈ 1e-5 pointwise/ergodic loss).
  - n = 10: +7e-5 to +9e-5 (ceiling +1.03e-4).
  - Domain g ≥ 17/20 against g ≥ 0: difference < 2e-6, because the binding words have gaps ≥ 1.03.
  - Binding structure: a few dozen active words built from gaps ≈ 1.04 / 1.97 / 2.93. B&B leaves at 8 dimensions ≈ 3–10× PC8C5BF's 4598.

**RESULTS (round 3).** Files: `lp_frame.py` (cutting-plane LP plus Dinkelbach; converged when no violated cut remains and c_LP − c_true < 1e-10), logs and JSONs `lp8_lo0.*`, `lp9_lo0.*`, `lp9_lo085.*`, `lp10_lo0.*`; `basins.py` with `basins_{mop,lp8,lp9,lp10}.log`. Double precision. c is the TRUE minimum from the word-seeded global search over {1.04, 1.97, 2.93}^{n−1} plus the working set plus random starts. The kernel is exact in the final evaluation. κ uses the H floor 0.67216841 (exact H adds 5.7e-10).

| frame | B_n | c_n (true min) | κ_n | gain over 0.6735478 | ceiling (round 2) | basins within 5e-5 / 1e-3 rel | distinct local minima |
|---|---|---|---|---|---|---|---|
| MOP W8 (n = 8) | 0.0040435 | 0.00805165 | 0.67354808 | +2.8e-7 (floor → true min) | 0.6735638 | 17 / 19 | 2,212 |
| n = 8 re-optimised | 0.00406752 | 0.00808760 | 0.67354828 | +4.8e-7 | 0.6735638 | 15 / 19 | 2,213 |
| **n = 9, gaps ≥ 0** | 0.00437542 | 0.00859348 | **0.67358140** | **+3.36e-5** | 0.6736047 | 16 / 24 | 6,581 |
| n = 9, gaps ≥ 17/20 | 0.00437585 | 0.00859414 | 0.67358141 | +3.36e-5 | — | — | — |
| **n = 10, gaps ≥ 0** | 0.00439939 | 0.00866655 | **0.67360686** | **+5.91e-5** | 0.6736506 | 17 / 23 | 19,721 |

- (1) Realistic targets: κ_9 = 0.6735814 (+3.36e-5) and κ_10 = 0.6736069 (+5.91e-5).
  - PC8C5BF is already optimal at n = 8 for this objective, to +2e-7. The n = 8 ceiling gap of 1.6e-5 is entirely pointwise-vs-ergodic loss.
  - Realised share of each frame's ceiling gap: 59% at n = 9, 57% at n = 10.
- (2) Gap domain: certifying on gaps ≥ 17/20 instead of ≥ 0 changes κ_9 by +1e-8. That threading change is not worth making.
- (3) Binding structure for B&B sizing:
  - Every near-binding word is built from gaps ≈ 1.04 / 1.97 / 2.91, with spans ≈ 12.03–12.06 at n = 9.
  - n = 9 has 16 basins within 1e-5..2e-4 relative of the min (2 within 1e-6), against 17 for MOP's W8. The count of near-binding basins is unchanged; one more dimension is added, and the total local-minimum count grows ≈ 3× (2,212 → 6,581).
  - Suggested certificate margin: 2e-4 relative. It costs Δκ = 0.679 × 2e-4 × c ≈ 1.2e-6 and keeps the same 16 basins (1e-3 would cost 5.8e-6 and admit 24).
  - Leaf estimate (ESTIMATE, not B&B): ≈ 3–6× PC8C5BF's 4,598, i.e. ≈ 14k–28k, from one extra dimension with ≈ 3 basins per gap, plus deeper refinement near the 16 basins. n = 10 adds another ≈ 3× (19,721 local minima, 17 near-binding basins).
- Prediction check:
  - n = 8 +0.5e-5 to +1.2e-5: WRONG (actual +4.8e-7; PC8C5BF was already optimal).
  - n = 9 +3e-5 to +4.5e-5: HELD (+3.36e-5).
  - n = 10 +7e-5 to +9e-5: WRONG, below (+5.91e-5).
  - Domain difference < 2e-6: HELD (1e-8).
  - Binding words 1.04 / 1.97 / 2.93: HELD. The leaf multiplier is still an estimate.

## Round 4: concrete optimised certificates for n = 8 and n = 9 (rounded weights, fresh re-check, margin structure)

**PRE-REGISTRATION (written before any computation in this round).**
- Procedure:
  - start from the converged LP solutions (`lp8_lo0.json`, `lp9_lo0.json`);
  - round to integers over 10⁸: a_ij by FLOOR (so the capacity Σ_{j−i=s} a ≤ 2 survives exactly), b_r to nearest; mirror pairs stay equal because the LP enforced symmetry;
  - recompute c_true of the ROUNDED weights by a FRESH global search, different from the LP's oracle: all {1.04, 1.97, 2.93}^{n−1} words, plus 20,000 words from a 10-letter alphabet {0.3, …, 5.0}, plus 5,000 uniform starts in [0, 4]^{n−1}, plus 2,000 in [0, 40]^{n−1}, plus perturbations of the binding basins;
  - κ = (H_lo − B)/(1 − c_true).
  - Margin structure: basin counts within relative δ, Hessian eigenvalues at the near-binding minima, basin half-widths √(2δc/λ) at δ = 2e-4, and the minimal gap in the near-binding words.
- PREDICTIONS:
  - κ_8 = 0.6735483 ± 1e-7, κ_9 = 0.6735814 ± 1e-7.
  - Rounding costs ≤ 2e-7 (likely ≈ 1e-8).
  - The fresh search finds no word undercutting the LP's minimum by more than 1e-9 relative.
  - Near-binding basins at 5e-5 relative: 15 (n = 8), 16 (n = 9).
  - Minimal gap in near-binding words ≈ 1.03.
  - Basin half-widths at δ = 2e-4: 1e-3 to 1e-2 in gap units.

**RESULTS (round 4).** Files: `cert_final.py` with `cert8_final.log`, `cert9_final.log`; certificates (integer weights over 10⁸) in **`cert8_final.json`, `cert9_final.json`**; baseline `cert_mop_basins.log`. Double precision. Fresh global search: all {1.04, 1.97, 2.93} words, plus 20,000 random 10-letter-alphabet words, plus 7,000 uniform starts, plus basin perturbations. It found 16,835 (n = 8) and 26,166 (n = 9) distinct local minima, and NO word below the LP's minimum (the rounded c is higher by 7e-9 / 5e-9 because b was rounded).

| | n = 8 (re-optimised) | n = 9 |
|---|---|---|
| B (integer over 10⁸) | 406753 | 437542 |
| capacities (× 10⁸, ≤ 2·10⁸) | 199999997 … 200000000 | 199999996 … 200000000 |
| nonzero a_ij | 26 of 28 | 34 of 36 |
| c_true (rounded weights) | 0.0080876082 | 0.0085934887 |
| κ (H floor, true min) | **0.673548275** | **0.673581404** |
| rounding cost | −5.2e-9 | +3.8e-10 |
| gain over 0.6735478 | +4.7e-7 | **+3.360e-5** |
| below its ceiling | 1.55e-5 (ceiling 0.6735638) | 2.33e-5 (ceiling 0.6736047) |
| certified κ at margin δ = 5e-5 / 2e-4 (Δκ = −0.679·δ·c) | 0.6735480 / 0.6735472 (BELOW MOP at 2e-4) | 0.6735811 / 0.6735802 (+3.24e-5) |
| near-binding basins at 1e-6 / 1e-5 / 2e-4 / 1e-3 | 7 / 15 / 15 / 19 | 2 / 16 / 16 / 26 |
| minimal gap in near-binding words | 1.0345 | 1.0315 |
| Hessian eigenvalues at those minima | 0.090 … 1.95 | 0.086 … 1.92 |
| basin half-widths √(2δc/λ) at δ = 2e-4 | 1.3e-3 … 6.0e-3 | 1.3e-3 … 6.3e-3 |

- Baseline, MOP W8 at its own certified margin of 5.09e-5: 17 basins, minimal gap 1.0346, eigenvalues 0.089 … 1.96, half-widths 6.5e-4 … 3.0e-3. At 2e-4: 1.3e-3 … 6.0e-3.
- So n = 9 has the same curvature range, one basin fewer, and one more dimension.
- n = 8 is not a retake route: its re-optimised gain (+4.7e-7) is consumed by any certification margin above ≈ 1e-4 relative.
- Prediction check: κ_8 and κ_9 within ±1e-7 held; rounding ≤ 2e-7 held; no undercut held; basin counts 15 / 16 held; minimal gap ≈ 1.03 held; half-widths 1e-3 … 1e-2 held.

## Round 5: certificate inputs for bridge-port's 9-point sizing (Sam chose n = 9 + dense encoding)

**PRE-REGISTRATION (written before this round's computations).**
- The rounding is the one in `cert9_final.json`: integers over 10⁸ for a and b (PC8C5BF's style), capacities ≤ 2·10⁸ exactly, all b_r > 0. So κ_rounded is already measured: 0.673581404.
- PREDICTIONS:
  - an independent second fresh search (new seed) reproduces c_true(rounded) = 0.0085934887 to ≤ 1e-10;
  - c_cert = ⌊c_true(1 − 2e-4)·10⁸⌋/10⁸ = 859177/10⁸;
  - κ_cert = (67216841 − 437542)/(10⁸ − 859177) ≈ 0.6735802 (+3.24e-5 over 0.6735478);
  - side condition c ≤ 1/64 holds with a wide margin.

**RESULTS (round 5).** `prep9.py`, `prep9.log`, **`cert9_inputs.json`** (weights, c_cert, the exact κ rational, side conditions, the 16 basins with Hessians, the refinement map).
- Independent fresh re-check (new seeds, 30,000 alphabet words, 8,000 uniform starts, all {1.04, 1.97, 2.93} words): 33,367 distinct local minima. c_true(rounded) = 0.0085934887, equal to the round-4 value to 4e-13. Prediction held.
- **c_cert = 859177/10⁸** (margin exactly 2.0e-4 relative). **κ_cert = 66779299/99140823 = 0.6735802365**, i.e. +3.244e-5 over 0.6735478. At c_true, κ = 0.6735814042. Prediction held.
- Side conditions: c_cert ≤ 1/64 ✓ (0.00859 against 0.015625). wfun ≥ 0.0506 on [0, 17/20] ✓ (≥ c). Capacities ≤ 2·10⁸ exactly ✓. a ≥ 0 ✓; all b_r > 0 ✓; reflection symmetry ✓.
- Local minima by relative excess: 16 (≤ 2e-4), 24 (≤ 1e-3), 108 (≤ 1e-2), 3,282 (≤ 1e-1).
- Refinement map: per-coordinate extents of the sublevel sets from the quadratic model at each local minimum, merged. Near-binding (2e-4) bands in every coordinate lie inside [1.028, 1.051] ∪ [1.955, 1.987] ∪ [2.911, 2.924]. At 1e-1 excess the bands sit around gaps 1, 2, 3, 4 (5, 6 at the end coordinates) with widths ≈ 0.1–0.3.
- Suggested box edges: ≤ 2⁻¹⁰ inside the 2e-4 bands (minimum half-width 1.3e-3); 2⁻⁷ inside the 1e-2 bands; 2⁻⁵ inside the 1e-1 bands; 2⁻³ or coarser elsewhere, where Fw − c ≥ 0.1c.

## Round 6: sizer input `bench/arun/cert/rwin9_lp9.json` (rwin8.json format, n = 9)
- Generator `make_rwin9.py`, log `make_rwin9.log`.
- Fields:
  - aN mirror symmetry asserted; bN palindromic and > 0; B_SA = 437542; spans ≤ 2·10⁸;
  - R8 window fields copied from rwin8.json;
  - delta_* entries for the linear chain, with m = null.
- eps_strong = 0.00859348873961842 = the minimum over three independent oracles:
  - famq.Family.global_min with rwin.py's lattice {1.04, 1.97, 2.91, 0.5}^8, seeds 1/2/3, all giving this value;
  - the round-4 fresh search, 2e-14 higher;
  - the round-5 fresh search, also 2e-14 higher.
- Random covers without the lattice reach only 0.0086075 / 0.0086006, so the lattice starts are necessary.
- The 16 near-binding words are included as `root_hints_near_binding`.

## Round 7: n = 9 certificates that trade κ for leaves (lead's experiment)

**PRE-REGISTRATION (written before any computation in this round).**
- Method: a separation LP in (a, b, c, t). Maximise t subject to:
  - Fw(g) ≥ c on the kept basin;
  - Fw(g) ≥ c + t at every other basin's local minimum (basins identified by letter pattern, gaps rounded to 1.04 / 1.97 / 2.92 / …);
  - κ_T·c − B ≥ κ_T − H_lo (linear form of (H_lo − B)/(1 − c) ≥ κ_T), with κ_T = target + 3e-7 so that the certified κ at δ = 5e-5 still meets the target;
  - capacity ≤ 2, mirror symmetry, b_r ≥ 1e-6.
  - Cutting planes with the word-seeded oracle.
- Two choices of kept basin: (A) cert9's minimum, an asymmetric word plus its mirror (2 basins at level c); (B) a palindromic word (1 basin).
- Then: same rounding rules (floor a, capacity exact, mirror, b palindromic and > 0); eps_strong = the true minimum by the lattice oracle (famq + {1.04, 1.97, 2.91, 0.5}^8, 3 seeds); basin counts at 2e-4 / 1e-3 / 1e-2.
- PREDICTIONS:
  - relative excess of the 2nd basin: ≈ 3e-4–1e-3 at 0.673570, ≈ 1e-3–3e-3 at 0.673562, ≈ 2e-3–5e-3 at 0.673555;
  - basin counts at 2e-4 drop from cert9's 16 to 1–2 for all three targets;
  - at 1e-3 (cert9: 24): ≈ 5–10 / 2–4 / 1–2;
  - at 1e-2 (cert9: 108): ≈ 60–90 / 40–70 / 30–60;
  - palindromic keep (B) beats asymmetric keep (A) by one basin at 2e-4, at similar t.

**RESULTS (round 7).** Files: `lp_sep.py` (final formulation, below); logs `sepG{570,562,555}.log` (562 and 555 rerun with a 4e-7 cushion); finalisation `make_rwin9_t.py` with `make_rwin9_t{570,562,555}.log`; sizer files **`bench/arun/cert/rwin9_t{570,562,555}.json`** (rwin9_lp9.json format plus basin counts and up to 60 root hints at ≤ 1e-2 excess).
- Formulation: maximise the absolute gap t between the kept basin and every other basin's local minimum. The kept basin is the palindromic word [1.040 1.976 1.046 1.983 1.983 1.046 1.976 1.040], whose current minimiser is pinned at level c by an equality constraint.
- Superseded attempt: a first version without that pin let the kept basin float above c. Its separations were overstated (sepF*), and it is discarded.
- An asymmetric kept word gives the same t, so the palindromic one is used (1 basin instead of 2).
- Rounding: a floored (capacities exact), mirror symmetry asserted, b palindromic and > 0. eps_strong = the lattice-oracle minimum (3 seeds; the fresh search agrees to ≤ 3e-12).

| certificate | B_SA | eps_strong | κ at c_true | certified κ (δ = 5e-5) | gain over 0.6735478 | 2nd-basin relative excess | basins at 2e-4 / 1e-3 / 1e-2 |
|---|---|---|---|---|---|---|---|
| cert9 (lp9) | 437542 | 0.0085934887 | 0.673581404 | 0.673581106 | +3.33e-5 | 1.5e-10 (mirror), next 1.7e-6 | **16 / 24 / 108** |
| rwin9_t570 | 436674 | 0.0085642495 | 0.673570294 | **0.673570002** | +2.22e-5 | **1.91e-3** | **1 / 1 / 93** |
| rwin9_t562 | 431048 | 0.0084690786 | 0.673562383 | **0.673562092** | +1.43e-5 | **3.24e-3** | **1 / 1 / 70** |
| rwin9_t555 | 428460 | 0.0084203532 | 0.673555384 | **0.673555097** | +0.73e-5 | **4.39e-3** | **1 / 1 / 67** |

- Prediction check:
  - 2nd-basin excess predicted 3e-4–1e-3 / 1e-3–3e-3 / 2e-3–5e-3; actual 1.9e-3 / 3.2e-3 / 4.4e-3. The first two came out ABOVE my ranges; the third held.
  - Counts at 2e-4 predicted 1–2: held (1).
  - Counts at 1e-3 predicted 5–10 / 2–4 / 1–2; actual 1 / 1 / 1. I overpredicted the first two.
  - Counts at 1e-2 predicted 60–90 / 40–70 / 30–60; actual 93 / 70 / 67 — at or above the top of each range.
  - Palindromic beats asymmetric by one basin at equal t: held.

## Round 8: heavier-pressure n = 9 vector (tP570) and the n = 8 fallback sizer file

**PRE-REGISTRATION (written before running).**
- (1) Separation LP as for t570: the palindromic kept basin pinned at c; κ_T c − B ≥ κ_T − H_lo with κ_T = 0.673570 + 4e-7; every other basin ≥ c(1 + 1e-3) (linear: Fw ≥ c + t, t ≥ 1e-3·c); capacity; mirror symmetry. The objective is changed to MAXIMISE min_r b_r (an auxiliary z ≤ b_r); if that is unstable, Σ b_r.
  - Baseline t570: bN = [26814, 50061, 64815, 76647, 76647, 64815, 50061, 26814]·10⁻⁸ (B 436674), so S_r = c/b_r ≈ 31.9 / 17.1 / 13.2 / 11.2.
  - PREDICTION:
    - mostly a REDISTRIBUTION toward the end gaps, with B rising ≤ 2% (to ≈ 0.00440–0.00445). The κ constraint pins B: a uniform pressure increase raises Fw by ε·span, and the shortest binding spans (≈ 8.3 for words of 1.04-gaps) are less than κ·8·1.48 ≈ 11.9.
    - min b_r rises from 0.00027 to ≈ 0.0004–0.0005, so max S_r falls from ≈ 32 to ≈ 18–22.
    - The near-binding separation stays ≈ 1e-3 (the constraint binds).
- (2) rwin8_reopt.json from cert8_final.json: the same format as rwin8.json; eps_strong = lattice-oracle minimum (famq, {1.04, 1.97, 2.91, 0.5}^7, 3 seeds), predicted to equal cert8's 0.0080876082 within 1e-12; delta entries include δ = 3e-5.
- Correction to the baseline line above (typed before reading the file; the predictions are unchanged): t570's actual bN = [27130, 50593, 66037, 74577, 74577, 66037, 50593, 27130], and S_r = c/b_r = 31.57 / 16.93 / 12.97 / 11.48 (mirrored).

**RESULTS (round 8).** Files: `lp_presep.py` (derived from lp_sep.py: objective max min_r b_r or Σ b_r; t ≥ 1e-3·c; kept palindromic basin pinned), logs `sepP570.log` (min-b), `sepPs570.log` (sum); finalisation `make_rwin9_tP570.log`, `make_rwin9_tPs570.log`; sizer files **`cert/rwin9_tP570.json`** (min-b; the named test) and `cert/rwin9_tPs570.json` (Σb alternative); **`cert/rwin8_reopt.json`** (n = 8 fallback; `make_rwin8_reopt.py`, `make_rwin8_reopt.log`).

| certificate | B_SA | bN (end … middle) | S_r = c/b_r (end … middle) | max S | Π S_r | certified κ (5e-5) | basins 2e-4 / 1e-3 / 1e-2 |
|---|---|---|---|---|---|---|---|
| lp9 | 437542 | 27009 … 76098 | 31.8 / 17.3 / 13.0 / 11.3 | 31.8 | 6.55e9 | 0.673581106 | 16 / 24 / 108 |
| t570 | 436674 | 27130 / 50593 / 66037 / 74577 | 31.6 / 16.9 / 13.0 / 11.5 | 31.6 | 6.33e9 | 0.673570002 | 1 / 1 / 93 |
| **tP570 (max min b)** | **431690** | **36167 / 48556 / 60448 / 70674** | **23.5 / 17.5 / 14.1 / 12.0** | **23.5** | **4.80e9** | 0.673570100 | 1 / 15 / 109 |
| tPs570 (max Σ b) | 454192 | 26333 / 56466 / 68264 / 76033 | 33.5 / 15.6 / 12.9 / 11.6 | 33.5 | 6.17e9 | 0.673570093 | 1 / 12 / 96 |

- The min-b objective raises the end-gap pressure by +33% (27130 → 36167), cutting max S_r from 31.6 to 23.5 and the root-box product by 24%.
- But B FALLS by 1.1% (436674 → 431690): it is a redistribution toward the ends. The Σb objective raises B by +4.0% but leaves the end gaps as they were (S_max 33.5).
- In both, the separation constraint binds at 1e-3: the 2nd basin is at 9.97e-4 relative after rounding, and 12–15 basins sit at that level, so they show up in the 1e-3 count.
- n = 8 fallback (`rwin8_reopt.json`):
  - eps_strong = 0.008087608236768, the lattice oracle on 3 seeds (my fresh value is 5e-13 higher).
  - Mirror symmetry asserted; B_SA 406753.
  - Certified κ = 0.6735482690 (δ = 0), 0.6735481060 (δ = 3e-5, cN 808736), 0.6735479974 (5e-5), 0.6735471757 (2e-4, BELOW 0.6735478). Gains over MOP: +4.7e-7 / +3.1e-7 / +2.0e-7 / −6.2e-7.
- Prediction check:
  - "redistribution" held, but "B rises ≤ 2%" did not: B fell 1.1% under min-b and rose 4.0% under Σb.
  - min b predicted 4–5e-4; actual 3.6e-4, below the range.
  - max S predicted 18–22; actual 23.5, above the range.
  - Separation binding at ≈ 1e-3: held.
  - n = 8 eps_strong equal to cert8 within 1e-12: held (5e-13).
- **Lean root-cover constraint (bridge-port, 2026-10-10): b_r ≥ cN/32** (S_r = cN·SC/b_r must be < KB = 2²⁰ = 32·SC).
  - Margins: lp9 +0.6%, t570 +1.4%, t562 +4.5%, t555 +5.2%, tP570 +36.3%, **tPs570 −4.5% (violates; not to be sized)**, rwin8_reopt +16.7%.
  - `lp_sep.py` and `lp_presep.py` now enforce b_r ≥ 1.05·c/32 (env BMIN_FRAC).
- **bridge-port's sizing outcome (2026-10-10):**
  - The narrow b-margins did not bite (lp9 and t570 sized; lp9 compiled with the KB-fixed sizer).
  - **tP570:** the roots 2/5/9 subset gives 3,914 leaves, −1.3% against t570, so ≈ 14.7k in total. Pressure redistribution did not move the bulk count. bridge-port: "the 9-point route is closed for this design" (the budget is ≈ 8–12k).
  - **rwin8_reopt at δ = 3e-5:** 18,731 leaves; the knee is in roots 18 (11,962) and 20 (2,283). δ = 5e-5 is expected near PC8C5BF's size. The decision is with the lead.
  - Lesson: at n = 9 the leaf count is set by the bulk, not by near-binding basin separation or root-box size.

## Round 9 (new campaign, "do the 9 pt, make it fit"): phase 1, the functional's geometry, as input to the engine levers

**PRE-REGISTRATION (written before reading the dumps or computing anything).**
- Data: bridge-port's sizer dump for t570 (`cert/n9/dump_full_t570.pkl`, 14,906 leaves, 16 roots), read-only.
- (a) Plan:
  - per-leaf relative excess ε = min_box F/c − 1 (min over the box's corners, centre and random interior points, F with the exact kernel);
  - the leaf distribution over bands ≤ 1e-3 / 1e-3–1e-2 / 1e-2–1e-1 / > 1e-1;
  - the VOLUME distribution under uniform measure on the union of the root boxes (Monte Carlo).
  - PREDICTION: by volume, > 99% of the root boxes lie at ε > 1e-1. By leaves: ≈ 5% ≤ 1e-3, ≈ 25% in 1e-3–1e-2, ≈ 45% in 1e-2–1e-1, ≈ 25% > 1e-1. So a perfect far-field test removes ≈ 25% of leaves at 1e-1, and ≈ 70% if it worked down to 1e-2.
- (b) Plan: w = (K/K₀)² with w″ and w‴ on the pair-sum range. Per leaf, the box half-widths h_t of its pair sums give a tangent (first-order) error E₁ ≈ Σ a_t sup|w″| h_t²/2 against a second-order error E₂ ≈ Σ a_t sup|w‴| h_t³/6. The admissible enlargement is λ = (E₁/E₂)^{1/3} at fixed error.
  - PREDICTION: λ ≈ 2–4 in the bulk bands (1e-3–1e-1), so a second-order minorant removes ≈ 2–3× leaves there, less near the basins.
- (c) Plan: smoothed R8 windows (corrections damped by e^{−β j²}). For each: the n = 9 ceiling (rank_ceiling, R = 8) and curvature metrics of w on the pair-sum range.
  - PREDICTION: a 20% curvature reduction costs ≈ 2e-5–5e-5 of the n = 9 ceiling and buys ≤ 20% of leaves. Not a good trade.

**RESULTS (round 9, (a) and (b)).** Files: `geom_a.py` (per-leaf minimum by local SLSQP from the best of 400 feasible samples) with `geom_a_t570.log/.json`; `geom_ab.py` with `geom_ab_t570.log`; `geom_b_profile.py` with `geom_b_profile.log` and `w_profile.npz`.
- A first pass that used sampling only (no local minimisation) put 99.9% of leaves above 1e-1. It was wrong: sampling misses each leaf's minimum. Superseded.
- (a) Per-leaf minimum excess, t570 dump (14,906 leaves):
  - ≤ 1e-3: 3 (0.02%); 1e-3–1e-2: 118 (0.8%); 1e-2–1e-1: 2,160 (14.5%); > 1e-1: 12,625 (84.7%).
  - By VOLUME of the root polytopes: 100.0000% lies above 1e-1 (200k samples).
  - Perfect far-field test, i.e. collapsing every subtree whose leaves all have excess > θ:
    - θ = 1e-1: 7,896 leaves (53%);
    - θ = 3e-2: 3,719 (25%);
    - θ = 1e-2: 1,598 (10.7%);
    - θ = 3e-3: 639 (4.3%);
    - θ = 1e-3: 107 (0.7%).
- (b) Derivative profile of w = (K/K₀)²:
  - sup|w″| / sup|w‴| = 0.35 / 0.09 / 0.19 / 0.17 / 0.16 on [0.8, 1.2) / [1.2, 2.5) / [2.5, 5) / [5, 10) / [10, 260];
  - sup|w″| = 3.5 / 0.68 / 0.20 / 0.049 / ≤ 0.015 on the same ranges.
  - Isotropic box enlargement admissible with a second-order (quadratic) minorant against a tangent one, at the leaf's own margin (ε + 5e-5)c: median ×2.13 (> 1e-1 band), ×2.99 (1e-2–1e-1), ×4.6 (1e-3–1e-2), ×6.9 (≤ 1e-3).
  - Crude proxy (a leaf merges 2^saved siblings, saved = Σ over split axes of min(⌊log₂ gain⌋, depth on that axis)): ≈ 4.8k leaves (32%). This is OPTIMISTIC: isotropic growth, and a centre-Taylor error model.
- Anatomy of the far leaves (`geom_far_anatomy.log`): the > 1e-1 leaves have median excess 0.47 (10% / 90%: 0.16 / 1.23), median widest box side 3.97 gap units and median widest gap 5.4; 55% have some gap with lower bound > 2.5 (25% > 3.5). Their true minima are far above c; they exist because affine minorants on wide boxes lose too much.
- (c) Smoothed windows, c_j → c_j·e^{−βj²} (`geom_c_windows.py/.log`, `rank_ceiling_smooth_b*.log`):
  - Curvature barely moves: sup|w″| within ±2% on [0.8, 10) for β ≤ 0.1, and −7% / −12% / −14% on [10, 40) at β = 0.01 / 0.03 / 0.1.
  - H RISES (0.6722428 / 0.6722976 / 0.6723690), but the n = 9 ceiling FALLS: 0.6735660 / 0.6735183 / 0.6734638, against R8's 0.6736047. That is −3.9e-5 / −8.6e-5 / −1.4e-4.
  - So this family buys ≤ 2% bulk curvature (≤ 14% far field) at ≥ 3.9e-5 of κ ceiling: a bad trade, worse than predicted.
  - Why: w's curvature at moderate s is set by the window's support and its main √2 term, not by the corrections. Damping the corrections only removes what R8's optimisation put there.
- Prediction check:
  - (a) volume > 99% above 1e-1: HELD (100%).
  - The leaf distribution was WRONG: I predicted ≈ 25% of leaves above 1e-1; the actual is 84.7%. The far field dominates.
  - A perfect far-field test removes 47% of leaves at 1e-1 (predicted 25%) and 89% at 1e-2 (predicted ≈ 70%).
  - (b) gain ×2–4 in the bulk: HELD (×2.1–3.0). Leaf reduction 2–3× against a proxy of 3.1×, roughly held (optimistic proxy).
  - (c) "not a good trade": HELD, and the curvature lever is even weaker than I assumed.

## Round 10 (phase 2b): real far-field tests on the t570 split tree

**PRE-REGISTRATION (written before running).**
- The tree is `cert/n9/dump_full_t570.pkl` (14,906 leaves). Walking top-down, a node whose box (plus its explicit pair-sum constraints) a test certifies with LB ≥ cN/SA (cN = 856382) becomes a leaf; I count the leaves.
- (T1) interval-min: LB = Σ_t a_t·min_{s∈[lo_t, hi_t]} w(s) + Σ_r b_r lo_r. The pair-sum range is the box sum intersected with the node's constraints. min w comes from a dyadic table at resolution 2⁻ᵏ, k ∈ {6, 8, 10}: outer cover by table cells, each holding the cell minimum (floating point here; certification in Lean is separate).
  - Table size: cells over [0, max pair sum in the tree], plus the pyramid levels for range queries.
- (T2) long-gap decoupling: for a gap r with lo_r ≥ g*, LB = m_L(r) + m_R(r) + b_r·lo_r, where m_L / m_R are the GLOBAL minima of the left / right sub-frame functionals (points 0..r and r+1..8, with the same weights restricted). The cross terms are dropped; they are ≥ 0, so no cross-term bound is needed. g* ∈ {2, 2.5, 3}.
- Combined: T1 or T2.
- PREDICTIONS:
  - T1 removes 10–25% of the leaves (≈ 11–13k remain), with little gain beyond 2⁻⁸. The interval min of w over wide pair-sum ranges is ≈ 0, because K has a zero every ≈ 1 unit.
  - T2 at g* = 2.5 removes 15–35%.
  - T1 + T2 removes 30–45% (≈ 8–10k), against the perfect far test's 7,896.

**RESULTS (round 10).** `far_tests.py`, `far_tests_t570.log/.json`. Baseline 14,906 leaves; the perfect far test at 1e-1 gives 7,896 (−47%).

| test | leaves | removed | nodes certified |
|---|---|---|---|
| T1 interval-min, table 2⁻⁶ | 13,574 | 8.9% | 745 |
| T1, 2⁻⁸ | 13,574 | 8.9% | 812 |
| T1, 2⁻¹⁰ | 13,574 | 8.9% | 819 |
| T2 long-gap, g* = 2.0 / 2.5 | 12,465 | 16.4% | 799 |
| T2, g* = 3.0 | 12,475 | 16.3% | 781 |
| T1 (2⁻⁸ or 2⁻¹⁰) + T2 (g* 2 or 2.5) | 12,283 | 17.6% | 1,109–1,116 |

- T1 does not depend on table resolution. Interval minima of w over the far nodes' wide pair-sum ranges are ≈ 0 (K has a zero roughly every unit), so only the pressure term Σ b_r lo_r works.
- T1 table size over [0, 146.5]:
  - 2⁻⁶: 9,440 cells (36.9 KB base, 452 KB with a full range-min pyramid at 4 B/entry);
  - 2⁻⁸: 147.5 KB base (2.1 MB pyramid);
  - 2⁻¹⁰: 590 KB base (9.6 MB pyramid).
  - Since resolution buys nothing, 2⁻⁶ suffices, and cells whose minimum is 0 need not be stored.
- T2 sub-frame minima (left: points 0..r | right: points r+1..8): r = 0: 0 | 0.00778; 1: 0.00029 | 0.00647; 2: 0.00083 | 0.00492; 3: 0.00178 | 0.00337; and symmetric.
  - So T2 certifies an end gap only from lo ≳ 2.9, and a middle gap only from lo ≳ 4.6; hence the insensitivity to g*.
- The real tests reach 17.6% of the 47% that a perfect far test could remove, i.e. about 37% of the potential.
- Prediction check: T1 10–25% was just BELOW (8.9%); T2 15–35% HELD (16.4%); combined 30–45% WRONG (17.6%).

## Round 11: the ideal box-restricted decoupling (T2*) and its sub-certificate cost (t570 tree)

Lead's context, recorded:
- The κ trade does not buy leaves. Roots 2/5/9 fast sizings: t570 3,966, t562 4,020, t555 4,008. The count comes from the engine, not the margin.
- bridge-port's subset counterfactuals against the LPACCEPT baseline B0 = 3,143: V −5.7%, VC −6.6%, SO −3.8%, SOVC −10.7%; SEP still running.
- B0 against the normal test (3,966) is −21%, so multiplier rounding is a lever on its own.
- Budget ≲ 6–7.5k leaves on the full tree; bytes bind first.

**PRE-REGISTRATION (written before running).**
- (1) T2*: at every node and every gap r, m_L(r, box_L) and m_R(r, box_R) are the TRUE minima of the left (points 0..r) and right (points r+1..8) sub-frame functionals over the node's box.
  - The box is the gaps' ranges plus the node's constraints on pair sums lying entirely within one side. Cross constraints and cross pairs are dropped (a sound relaxation, since cross pairs are ≥ 0).
  - Minima by SLSQP from the best of 200 feasible samples (3 starts).
  - Certify if m_L + m_R + b_r·lo_r ≥ cN/SA (cN = 856382). Collapse top-down.
  - Cheap filters, both sound for skipping: global sub-minima (T2) first; skip r when (F_L + F_R) at the node's best sample point plus b_r·lo_r is already < cN (an upper bound on m_L + m_R).
- (2) Cost: each collapsed node needs certificates for m_L(box_L) ≥ t_L and m_R(box_R) ≥ t_R. The slack m_L + m_R + b_r lo_r − cN is split in proportion to m_L, m_R.
  - Sub-certificate leaves are estimated with a PROXY test (centred second-order bound: F(x_c) − Σ_r |∂_r F| h_r − ½ Σ_t a_t sup|w″|(range_t)(Σ_{r∈t} h_r)², bisecting the widest gap; box only, no pair-sum constraints).
  - The proxy is CALIBRATED on the full 8-gap functional against the dump's actual subtree sizes for ~60 sampled nodes. Sub-certificates are deduplicated by (side, r, box), keeping the largest threshold.
  - Net = remaining top-level leaves + calibrated sub-certificate leaves.
- PREDICTIONS:
  - (1) T2* leaves 8.5k–10k (−33% to −43%, against −47% for the perfect far test; T2 with global minima gave −16.4%), carried mostly by middle gaps r = 2–5.
  - (2) Net 9k–11.5k. The product structure does turn N_L·N_R into ≈ N_L + N_R on far nodes; sub-certificate leaves total ≤ 20% of the top-level leaves removed.
  - Sub-certificate leaves cost ≈ 1/3 of a full leaf's bytes (≤ 10 pair terms against 36, ≤ 4 gaps against 8).

**METHOD AMENDMENTS (made before the counts below; predictions unchanged).**
- The pre-registered minimiser (SLSQP from the best 3 of 200 samples) was tested and FAILED on root 0. At r = 4 it returned m_L = 0.00537, while a feasible point in the root box has F_L = 0.00416. The 7-gap sides also broke mirror symmetry (r = 6 left 0.0065857 against r = 1 right 0.0064842).
  - Debug runs with it, and with an intermediate fix, gave root 0 → 1 and → 30 leaves. Both are discarded.
- Replacement (`t2star.py`, side minimiser):
  - seeds: words over the multi-point basin alphabet {1.04, 1.97, 2.93} and then integers, ≤ 4 values per gap inside the box, plus box ends. The product is ranked on a K table; 3,000 are kept, plus 200 feasible samples.
  - batched projected-gradient descent with a penalty for the pair-sum constraints, then exact SLSQP polish of the 12 best distinct points.
  - inheritance: if the parent's side minimiser lies in the child's side box and constraints, the child's estimate equals the parent's.
  - Validated: hull and free-box side minima are mirror-symmetric to 1e-7 and reproduce round 10's global sub-frame minima (0.0077795, 0.0064692, 0.0049167, 0.0033660, 0.0017846, 0.0008270, 0.0002887). The root-0 r = 0 right side gives 0.0082800, equal to a polish from the full-frame minimiser.
  - Guard: a certified node whose bound exceeds the smallest phase-1 found minimum in its subtree is counted as a violation.
- The global-T2 shortcut is dropped. Round 10's rounded minima were rounded UP in places (0.00029 against 0.0002887), so it was not sound as a shortcut.
- Skip test, still sound: min over feasible samples and inherited points of F_L, plus the same for F_R, plus b_r lo_r, is < cN (separate upper bounds on m_L and m_R).
- Gap classes. "Sub-certificate on ≤ 5 points" holds only for r ∈ {3, 4}, and r = 2 or 5 gives a 6-point side. So every count is reported for three classes of admissible r: all r; r ∈ {2..5}; r ∈ {3, 4}.
- The proxy drops boxes whose pair-sum range misses a constraint interval (empty boxes). Otherwise it is box-only as pre-registered.
- Calibration samples nodes stratified by subtree size (9 strata).
- Added accountings: "best" keeps the original subtree where it is cheaper; "dp" collapses at whatever depth is cheapest below the first certified node.

**Round 11 status at the pause (2026-10-10 23:17), recorded before the remaining counts.**
- (1) T2* ideal, t570 tree, top-down: all r 14,906 → 5,203 (−65.1%); r ∈ {2..5} → 11,660 (−21.8%); r ∈ {3,4} → 12,422 (−16.7%). Per root in `r11/t2star_{a,b,c,d}.log`.
- Pricing (`subcert_net2.py`, files `r11/net2_{r34,r2to5,all}.json`).
  - Proxy: `subcert2.SideHull`, the hull LP. Per pair it uses the VALID convex minorant of w on the effective range, i.e. the lower hull of the cell-minimum step function, with the sizer's SPLIT=err rule.
  - The same proxy prices the full 9-point functional on each collapsed node and the two sides at the slack-split thresholds.
  - The second-order box proxy (`subcert.py`) was abandoned: it could not certify single sizer leaves.
  - Correction to a reading of the files: `r11/calib.{log,json}` calibrates a SUPERSEDED proxy, the LP on a 64-sample hull, which is not a valid minorant on wide ranges. That is where "1 vs 507" comes from. The hull proxy itself has not been calibrated yet.
- Per-node results, same proxy on both sides of the comparison:

| class | collapsed nodes | Σ sizer leaves | Σ full (hull) | Σ sides (hull) | per-node best net |
|---|---|---|---|---|---|
| r 3,4 | 2,885 | 5,322 | 2,993 | 31,812 | 14,906 (0 nodes pay) |
| r 2–5 | 4,438 | 7,608 | 7,194 | 79,071 | 14,868 (8 pay) |
| all r | 4,217 | 13,625 | 47,366 | 129,041 | 14,285 |

- Comparator: the hull LP on the full functional, collapsed top-down, takes 14,906 → 10,778 (−27.7%) in `r11/hull_collapse.json`. bridge-port's QV build engine gives 10,452.
- Byte prices of a sub-frame leaf (`decode_bits.py` on DATA_PC9L, 5,023,670 bits reproduced):
  - a full M leaf is 286 bits: head 2, pair fields 264.8, multipliers 19.2;
  - per-pair fields fall with distance: 14.6 bits at distance 1, 8.1 at 2, 5.8 at 3, 4.3–5.3 beyond;
  - sub-frame leaf (pair fields + head) as a share of a full leaf: 5 points 0.31, 4 points 0.19, 6 points 0.46, 8 points 0.80.

**PRE-REGISTRATION for the remaining counts of round 11 (2026-10-11, written before running).**
- (C1) Calibration of the hull proxy against the real sizer, full functional on stratified sampled nodes of the t570 tree and of the QV tree.
  - Prediction: median sizer/proxy 1.0–1.6. The spread is wide: the 10–90% band of the ratio covers more than a factor 4, because the proxy's split rule is cruder (one LP, no pf look-ahead) and its minorant is stronger.
- (C2) Deduplicated and pooled nets, all classes. Sub-certificates are shared by side key (side, side box, side constraints), at the largest threshold.
  - Prediction: deduplication removes ≤ 35% of the side leaves.
  - Pooled net (Σ sizer × Σ sides_dedup / Σ full) is ≥ 25k for every class.
- (C3) Hybrid against the hull baseline, the DECISIVE number. Start from the hull-collapsed tree (10,778). At every T2*-collapsed node X that the hull walk does not already certify, choose the cheaper of hull_cost(X) and 1 + sides(X). Sides are charged once per distinct side key (OPTIMISTIC sharing: a shared sub-certificate is free after its first use).
  - Prediction: best class ≥ 9,700 (cut ≤ 10%). So box-restricted recursion does NOT reach the 25% cut.
  - What would refute this: a hybrid net ≤ 8,084 (−25% on 10,778).
- (C4) QV tree (10,452), the add-on.
  - Prediction for T1 + T2 (round-10 tests): −8% to −14%, less than the −17.6% on t570.
  - Prediction for T2* ideal all-r top level: 3.5k–4.5k.
  - Prediction for the hybrid net against the hull collapse of the QV tree: no class cuts ≥ 25%.

**ROUND 11 RESULTS (t570 tree; QV add-on partly done, see below).**

(1) T2* ideal, top-down. Per root in `r11/t2star_*.log`.
- All r: 14,906 → **5,203** (−65.1%).
- r ∈ {2..5}: 11,660 (−21.8%).
- r ∈ {3,4} (both sides ≤ 5 points): 12,422 (−16.7%).
- The collapses are carried by the END gaps. In the all-r class, leaves saved by the max-slack gap are r0 3,700, r7 4,305, r3 1,679, other gaps ≤ 13.
- Guard: 2 violations at one far node (R15:…XXY, bound 3.27·cN against a found minimum of 2.97·cN). Neither affects a certification.
- **Prediction CHECK.** Predicted 8.5k–10k, carried by r = 2–5.
  - Count: refuted in both directions. The middle-gap classes give 11.7k / 12.4k; all r gives 5.2k.
  - Attribution: refuted. The end gaps carry the collapses.

(2) Cost, priced by the hull proxy on both sides of each comparison.

(C2) Pooled and deduplicated nets (`r11/net2_*.json`). Deduplication by side key removes only 1.4–4.4% of side leaves (5,293 uses → 5,145 keys for all r). The B_0 × B_R sharing does not appear at the first-certified level.

| class | top | Σ sizer | Σ full | Σ sides | Σ sides dedup | pooled net, dedup | per-node best |
|---|---|---|---|---|---|---|---|
| r 3,4 | 12,422 | 5,322 | 2,993 | 31,812 | 30,397 | 66,487 | 14,906 |
| r 2–5 | 11,660 | 7,608 | 7,194 | 79,071 | 77,180 | 93,314 | 14,868 |
| all r | 5,203 | 13,625 | 47,366 | 129,041 | 127,185 | 42,040 | 14,285 |

- **Prediction CHECK.** Predicted dedup ≤ 35% and pooled ≥ 25k: SUPPORTED. Dedup was 1.4–4.4%; pooled was 42k–93k.

(C1) Calibration of the hull proxy against the real sizer (`r11/calib_hull_t570.log`; 65 stratified nodes, run stopped at the 256–600 stratum, 2 capped).
- When the proxy SPLITS FOR ITSELF, proxy/sizer has median 5.9, pooled 11.7, and a 10–90% band of 0.27–24. By stratum, the median is 1.0 at 1 sizer leaf, 0.5 at 2–3, 5–11 at 4–127, and 57 at 128+.
- The SAME leaf test on the SIZER's splits (`hull_collapse.py`) takes 14,906 → 10,778. bridge-port's QV engine gives 10,452 on its own tree.
- So the hull leaf test is at the sizer's level, and the proxy's own split rule is the weak part. A PFK look-ahead variant was tried and was worse and slower; it was dropped.
- **Prediction CHECK.** Predicted median sizer/proxy 1.0–1.6: REFUTED. Measured 0.17, i.e. proxy/sizer 5.9, with the predicted wide spread.

(C3) DECISIVE hybrid against the hull baseline 10,778 (`hybrid.py`, `hybrid_dp.py`, `r11/hdp_*.json`).
- Setup:
  - At every T2*-collapsed node X not covered by a hull-certified ancestor, take the cheaper of hull(X) and 1 + sides(X).
  - Sharing is OPTIMISTIC: a side key is free after its first use, or amortised.
  - Bytes variant: a sub-frame leaf is priced by its pair fields, a decoupled top leaf at 0.1.
  - Allowance for the proxy's split rule: side costs are divided by HF. Per node, HF = full(X)/hull(X), which is proxy-split against sizer-split on the node itself, same leaf test. Pooled, the measured penalty on candidates is 1.95 / 4.46 / 6.45 for r 3,4 / r 2–5 / all r.
- Candidates not covered by the hull walk: r 3,4 55 nodes (100 hull leaves); r 2–5 295 (694); all r 1,314 (6,904). Middle-gap far cells are already certified by the hull leaf test on the full functional.

| class | HF | first-level, leaves | first-level, bytes | deep DP (120-node sample, extrapolated), leaves | deep DP, bytes |
|---|---|---|---|---|---|
| r 3,4 | per node | 0.0% | −0.0% | — | — |
| r 2–5 | per node | −0.1% | −0.6% | — | — |
| all r | per node | −4.3% | −8.5% | −4.05% | −8.7% |
| all r | 6.45 pooled | −6.1% | −12.3% | −9.1% | −16.9% |

- Sensitivity, first-level, all r, leaves / bytes: HF 1 → −0.0% / −0.2%; HF 3.5 → −1.2% / −3.7%; HF 10 → −13.8% / −22.1%; HF 30 → −34.2% / −44.1%.
- A 25% leaf cut needs HF ≈ 17. That is sub-certificates about 2.6× cheaper, relative to the proxy, than the full certificate on the same nodes.
- **Prediction CHECK.** Predicted best ≥ 9,700 (cut ≤ 10%): SUPPORTED in leaves (best −9.1% → 9,800 under the most generous measured allowance). In bytes the pooled-allowance deep DP reaches −16.9%.
- The refutation threshold (≤ 8,084, −25%) was not reached in any variant with a measured allowance.

**Verdict on box-restricted recursion (t570).**
- The ideal ceiling is large (top level −65%). Almost all of it sits where the hull leaf test on the full functional already certifies, or where the sides cost more than the hull subtree.
- Net against the hull level: −4% to −9% in leaves, −9% to −17% in bytes, with optimistic sharing.
- This instrument does not reach the 25% cut.

(C4) QV tree (10,452 leaves), partial:
- T1 + T2 (`far_tests.py` on the QV dump, `r11/far_tests_qv.log`):
  - T1 at 2⁻⁶ / 2⁻⁸ / 2⁻¹⁰ removes 0 leaves; it certifies only leaves.
  - T2 at g* 2.0 / 2.5 gives 9,901 (−5.3%); at 3.0, 9,907.
  - T1 + T2 gives 9,901 (−5.3%).
  - **Prediction CHECK** (−8% to −14%): REFUTED, it is smaller. The QV engine already absorbs what T1 bought on t570.
- Hull leaf test on the QV splits: 10,452 → 9,983 (−4.5%) (`r11/qv_hull_collapse_nodes.json`).
- T2* ideal and the hybrid on QV are running: `r11/qv_t2star_{a,b,c}`.

**ROUND 11, QV TREE (10,452 leaves, bridge-port's build engine), completed 2026-10-11.**
- T1 + T2: T1 removes 0 leaves; T2 and T1 + T2 give 9,901 (−5.3%). Prediction CHECK (−8 to −14%): REFUTED, smaller.
- Hull leaf test on the QV splits: 9,983 (−4.5%).
- T2* ideal, top level (`r11/qv_t2star_{a,b,c}`):
  - all r 4,726 (−54.8%); r 2–5 9,911 (−5.2%); r 3,4 10,342 (−1.1%).
  - Carried by the end gaps: leaves saved r0 3,084, r7 2,612, r3 20, r4 10.
  - Prediction CHECK (3.5k–4.5k): REFUTED, slightly above.
- Pricing (hull proxy both sides; `r11/qv_net2_*`):

| class | top | Σ sizer | Σ full | Σ sides | Σ sides dedup | pooled net, dedup | per-node best (vs QV) |
|---|---|---|---|---|---|---|---|
| r 3,4 | 10,342 | 2,318 | 2,353 | 25,606 | 24,482 | 34,466 | 10,452 |
| r 2–5 | 9,911 | 4,132 | 6,578 | 65,132 | 63,370 | 49,725 | 10,429 |
| all r | 4,726 | 9,534 | 48,579 | 147,409 | 146,593 | 33,531 | 10,008 (−4.2%) |

- Deduplication saves 0.6% for all r (4,890 uses → 4,751 keys).
- Hybrid against the hull baseline 9,983. Candidates: r 3,4 58 nodes / 100 hull leaves; r 2–5 277 / 630; all r 1,299 / 6,536. Measured allowance HF (pooled): 1.97 / 5.17 / 7.04.
  - Middle-gap classes: ≤ 0.1% leaves, ≤ 0.6% bytes.
  - All r, first level: per-node HF −4.0% leaves / −8.0% bytes; pooled 7.04 −5.3% / −11.6%.
  - All r, deep DP over ALL 1,299 candidates (`r11/qv_hdp_all_*_full_s*.json`):
    - per-node HF: net 9,099 (−8.9% vs hull, −12.9% vs QV); bytes 8,456 (−15.3% vs hull, −19.1% vs QV);
    - pooled HF 7.04: net 8,942 (−10.4% vs hull, −14.4% vs QV); bytes 8,131 (−18.6% vs hull, −22.2% vs QV).
  - The 120-node sample overstated the full deep DP (−11.35% against −8.85%, per-node HF). The t570 deep-DP figures above are 120-node samples.
- Prediction CHECK, C4 hybrid (no class ≥ 25%): SUPPORTED. The best measured is −14.4% in leaves and −22.2% in bytes against QV. Both of those include the hull-level leaf (−4.5%), which the QV engine does not have.

**Verdict on box-restricted recursion (QV tree).**
- Against the hull level, the recursion buys −9 to −10% in leaves and −15 to −19% in bytes.
- All of it comes from END-gap decoupling (an 8-point sub-frame plus one free point), at depth, node by node. Sharing is negligible.
- Middle-gap decoupling buys nothing, because the hull leaf already certifies those cells.
- Under the most generous measured allowance, combined with a hull-level leaf, the total is −14% leaves and −22% bytes against QV. That is below the 25% bar.
- Caveats:
  - The byte shares come from the lp9 layout (DATA_PC9L), not QV's.
  - The deep DP reuses the candidate's T2* minima (conservative) and pays for each sub-certificate separately (no sharing).
  - The HF allowance is measured on the full functional and assumed to transfer to the sides.
- Refuting control, not run: size the side sub-certificates of a sample of the 355 decoupled QV nodes (per-node HF DP) with the real sizer. If Σ(1 + sizer sides) ≤ 0.75 Σ hull(X) over the decoupled set and its uses scale, the bytes bar could be reached. Predicted: it is not reached.

## Round 12: context entropy budget of the walk (bytes bind)

Lead's context, recorded:
- The 9-point file is at ≈ 2.00 MB, after am-cert's byte levers; bridge-port's 32-root re-size gave 10,077 leaves.
- The target is 1.95 MB. A per-position kinds prefix code (≈ −54 KB) should close it; the point-index code is the reserve lever.
- am-cert's order-0 figures on PC9Q:
  - kinds 1.70 bits (1.37 conditional on term position), against a 2-bit field;
  - point index 5.21 bits, against 7 (≈ 21.6 indices per leaf);
  - λ 9.37, against 10.
- The task is the CONTEXT budget that order-0 cannot see. Sizing only.

Input: `cert/n9/DATA_PC9QB4.json` (the 32-root gap-1-cut build: 10,077 leaves, 3,154,179 walk bits = 313.0 bits per leaf), with `IV_PC9QB4.json` (each point's precertified tangent interval). `DATA_PC9Q.json` is the cross-check against am-cert's order-0 figures. Read-only.
- Layout, PC9Q family:
  - split [1][axis 6][mode 1];
  - leaf [0], then for an M leaf [kind bit];
  - per active pair: [κ 2], [j1 7 if κ ≥ 1], [j2 7 if κ = 3], [λ 10 if κ ≥ 2];
  - multipliers [1][c 5][side 1][Yq 13], closed by [0].
- Point semantics (size9pz `gpt`, MREG = 3): jj is RANGE-RELATIVE.
  - bit 6 picks the grid: 2^8 coarse, or 2^5 fine.
  - the low 6 bits give j ∈ 0..32, the position L + (U − L)·j/32, snapped to the grid and clamped to the range.
  - jj = 33 means the range start L.
  - The sizer keeps only the first jj for each distinct point.

**PRE-REGISTRATION (written before decoding).** Contexts measured on the PC9QB4 walk, re-walked with the exact closure so every leaf term has its range [L, U]:
- (P1) Arithmetic candidate list: the distinct points gpt(L, U, jj) over the 67 codes, in code order. No table reads.
  - Prediction: mean log2|list| = 4.5–5.5 bits.
  - The index within the list has empirical entropy 3.0–4.0 bits.
- (P2) Table candidate list: points p of the point table with L ≤ p ≤ U whose tangent interval contains [L, U].
  - Prediction: mean count 3–10, and the entropy of the index within the list is 1.5–2.5 bits.
  - The rules "first in list" and "nearest the midpoint" each hit 25–45%.
  - Read cost: the range spans (U >> 10) − (L >> 10) + 1 point blocks, typically far more than 2. So P2 is NOT a ≤ 2-read context unless a new index is built.
- (P3) Previous M leaf (walk order), same term position, both with κ ≥ 1:
  - same point p in 35–55% of cases;
  - same code jj in 25–40% (jj is range-relative, so it repeats less often than p).
- (P4) Kinds:
  - H(κ | position) ≈ 1.37 (am-cert);
  - H(κ | position, previous leaf's κ at that position) = 0.8–1.1 bits.
- (P5) λ:
  - H(λ | κ) = 8.8–9.4 bits;
  - same λ as the previous leaf ≤ 15%.
- (P6) Bound: at the best measured conditional entropies, 190–230 bits per leaf, against 313.0.
  - With only contexts a kernel can compute with ≤ 2 table reads (term position, previous leaf's fields kept in the walk state, the arithmetic list P1): 220–260 bits per leaf.

**ROUND 12 RESULTS** (`decode_ctx.py`; logs `r12_ctx_pc9qb4.log`, `r12_ctx_pc9q.log`; JSON alongside).
- Re-walk check:
  - PC9QB4: 3,154,179 bits reproduced exactly (10,077 leaves, 313.0 bits per leaf = 789 KB hex).
  - PC9Q: 3,435,015 bits (310.1 per leaf = 859 KB hex).
- Cross-check against am-cert's order-0 figures on PC9Q, all reproduced: κ 1.70, κ | position 1.37, jj 5.16 (5.21 with a Huffman code), λ 9.37, 21.6 codes per leaf.
- Per-leaf field budget, PC9QB4:
  - κ 65.7 bits (32.84 terms), j 154.9 (22.13 codes), λ 66.5 (6.65);
  - multipliers 15.9 (0.75 blocks), splits 8.0, heads 2.0.
- 1 bit per leaf = 2.52 KB of hex at 10,077 leaves.

Entropies on PC9QB4, per symbol: plug-in conditional / adaptive (sequential KT, realisable) / static Huffman per context (in-sample, table cost not included).

| field (width) | context | plug-in | adaptive | static Huffman |
|---|---|---|---|---|
| κ (2) | none | 1.71 | 1.71 | 1.76 |
| κ | position | 1.35 | 1.35 | 1.53 |
| κ | position, previous leaf's κ | 1.09 | 1.09 | 1.36 |
| κ, two terms jointly | position pair | 1.29/term | 1.30 | **1.32/term** |
| κ, two terms jointly | position pair, previous leaf's pair | 1.04/term | 1.07 | **1.09/term** |
| jj (7) | none | 5.15 | 5.16 | 5.19 |
| jj | position, slot | 4.63 | 4.74 | **4.66** |
| jj | position, slot, previous jj | 3.44 | 4.47 | (3.49, sparse contexts, overfits) |
| index in arithmetic list | list size | 4.92 | 4.94 | 4.95 |
| rank in arithmetic list by distance from previous point | position, slot | 3.68 | 3.78 | 3.71 |
| index in table list | list size | 2.95 | 3.01 | 3.01 |
| rank in table list by distance from previous point | position, slot | 3.02 | 3.13 | 3.05 |
| λ (10) | none | 9.30 | 9.35 | 9.33 |
| λ | κ | 8.94 | 9.04 | **8.96** |
| mult c (5), side (1), Yq (13) | — | 4.43, 0.88, 9.00 | 4.45, 0.87, 10.35 | 4.47, 1.00, 9.03 |
| split axis (6) | none / parent axis | 4.93 / 4.58 | 4.96 / 5.02 | 4.97 / 4.62 |

The point index given its range (the lead's question 1):
- Arithmetic list: the distinct gpt points of (L, U), 0 table reads. It has 61.2 candidates on average (log2 5.93), because almost every one of the 67 codes gives a distinct point.
  - The index within it carries 4.92 bits, no better than order 0.
  - "First" hits 0.7% and "nearest the midpoint" 0.8%.
  - The encoder's code is always the canonical first code for its point (0 exceptions in 223,016).
- Table list: reachable table points whose precertified interval contains [L, U]. Every chosen point lies in it.
  - Size: mean 16.6, median 15, log2 3.63. The index carries 2.95–3.01 bits.
  - "First" hits 9.8%, "nearest the midpoint" 18.2%. No cheap rule makes the point deterministic.
  - Cost: a range spans 37 point blocks (x >> 10) on average. This context is NOT a ≤ 2-read context.

Previous M leaf, same term position (question 2): available for 78% of codes.
- Same point 38.5%, same jj 39.6%. The previous point lies in the current arithmetic list 71.9% of the time.
- Ranking the arithmetic list by distance from the previous point gives 3.71 bits. That needs 0 table reads but 67 gpt evaluations and a sort per code in the kernel.
- A same-point flag plus the index otherwise gives 4.50.
- Delta coding (Elias gamma) is worse than fixed: 8.35.

Kinds given the previous leaf's kinds (question 3):
- Per term: 1.36 bits under a 4-ary Huffman code. Joint two-term coding recovers the entropy: 1.32 per term by position pair, 1.09 with the previous leaf's pair.
- Single-term 4-ary Huffman per position gives 1.53, not 1.35. A per-position kinds code reaches am-cert's ≈ −54 KB only with joint (pair) coding.

**Savings in KB of hex at 10,077 leaves, against today's fixed widths**, with kernel cost:

| lever | bits/leaf saved | KB hex | kernel decoder |
|---|---|---|---|
| κ, two-term Huffman per position pair | 22.3 | 56 | 1 table read per pair (17 tables) |
| κ, two-term Huffman, context = previous leaf's pair | 29.9 | 75 | 1 read per pair; walk state +68 bits (previous κ) |
| jj, Huffman per (position, slot) | 51.8 | 130 | 1 read per code (68 tables) |
| jj, order-0 Huffman | 40.1 | 101 | 1 read per code (1 table) |
| jj, rank by distance from previous point, arithmetic list | 72.8 | 183 | 0 reads, but 67 gpt evaluations and a sort per code; state +34·2 points |
| jj, table list | 88.3 | 222 | about 37 block reads per code: not feasible |
| λ, Huffman | κ | 6.9 | 17 | 1 read (3 tables of 1,024) |
| Yq, Huffman | 3.0 | 7.5 | 1 read |
| split axis, Huffman | 1.0 | 2.6 | 1 read |

**Bound, PC9QB4, bits per leaf** (hex KB):
- today: 313.0 (789);
- order 0, adaptive: 255.1 (643);
- kernel-cheap STATIC prefix codes (κ two-term with the previous pair, jj by position and slot, λ | κ, Yq, axis, c): **219.8 (554), i.e. −235 KB**;
- kernel-cheap contexts, adaptive: 202.1 (509);
- with the table list, not ≤ 2 reads: 184.9 (466).
- On PC9Q the same rows are 310.1 / 252.8 / 229.2 (static, without the joint κ) / 203.8 / 185.3.
- Code tables (code lengths) cost a few KB in total (68 × 67 + 3 × 1,024 + 17 × 17 × 16 entries). That cost is not included above.

**Prediction CHECKS:**
- P1: arithmetic list log2 4.5–5.5 and index 3.0–4.0. REFUTED: 5.93 and 4.92. The arithmetic list gives nothing.
- P2:
  - count 3–10: REFUTED (16.6);
  - index entropy 1.5–2.5: REFUTED (2.95–3.01);
  - first / nearest hit 25–45%: REFUTED (9.8% / 18.2%);
  - not a ≤ 2-read context: SUPPORTED (37 blocks).
- P3: same point 35–55%, SUPPORTED (38.5%). Same jj 25–40%, SUPPORTED (39.6%), but jj does not repeat less often than the point.
- P4: 0.8–1.1, SUPPORTED (1.09).
- P5: λ | κ 8.8–9.4, SUPPORTED (9.04). Same λ as the previous leaf ≤ 15%: REFUTED (16.8%).
- P6:
  - best 190–230: REFUTED, lower (184.9);
  - kernel-cheap 220–260: REFUTED, slightly lower (219.8 static, 202.1 adaptive).

## Round 13: shared code spec for the walk codes A (kinds pairs), B (jj per position and slot), C (λ per κ)

Lead's task, recorded:
- Canonical prefix codes built from PC9QB4's decoded walk, with lengths ≤ 15 and an escape for every unseen symbol.
- A JSON spec holding code lengths only, plus the exact bit order.
- A Python reference encoder and decoder with a bit-exact round trip.
- Report bits per leaf per set (A, A+B, A+B+C), table bytes as Lean hex defs, and decode work per leaf.
- The bit order follows the Lean walk. The walk is one natural number read LSB-first: the k-th bit read is bit pos + k. A fixed-width field reads as `(rdw f pos >>> off) &&& mask`, so its first bit is the field value's least significant bit.

**PRE-REGISTRATION (from round 12's in-sample Huffman numbers; written before building the codes).**
- A alone: 313.0 − 32.84 · (2 − 1.32) ≈ 290.7. Predicted 290.5–291.5 bits per leaf.
- A+B: B saves 22.13 · (7 − 4.66) ≈ 51.8. Predicted 238.5–240.5.
- A+B+C: C saves 6.65 · (10 − 8.96) ≈ 6.9. Predicted 231.5–233.5.
- Escapes and the 15-bit cap add < 0.3 bits per leaf in total.
- Tables as Lean hex defs: A 1–2 KB, B 10–16 KB, C 5–7 KB.
- Decode work per M leaf: A 17 symbols, B 22.9, C 6.9. Each symbol takes 1 context-row read plus 1 symbol read, and the length loop runs on average 2.6 / 4.7 / 9.0 iterations.

**ROUND 13 RESULTS** (`walkcode.py`; spec `r13/walkcode_spec_PC9QB4.json`; reports and logs in `r13/`).
- The original PC9QB4 layout re-parses and re-encodes bit-exactly (32 walks, 3,154,179 bits).
- Every set below encodes, decodes back through the closure walk, and reproduces every field: splits, reflected leaves, κ, jj, λ, multipliers.

| set | bits/leaf | KB hex (saved) | codewords / M leaf | length-loop steps / M leaf | context reads / M leaf |
|---|---|---|---|---|---|
| original | 313.0 | 789 | — | — | — |
| A | 290.6 | 732 (−56) | 17.0 | 44.8 (2.6/word) | 17.0 |
| B | 261.1 | 658 (−131) | 22.9 | 106.7 (4.7/word) | 22.9 |
| C | 306.1 | 771 (−17) | 6.9 | 61.7 (8.9/word) | 6.9 |
| A+B | 238.7 | 601 (−187) | 39.9 | 151.5 | 39.9 |
| A+B+C | 231.8 | 584 (−205) | 46.8 | 213.2 | 46.8 |

- Code tables as Lean hex literals (per context: 15 counts, then the canonical symbol list):

| set | contexts | listed symbols (incl. ESC) | max length | literals | estimated dispatch | total |
|---|---|---|---|---|---|---|
| A | 17 | 286 | 14 | 1.0 KB | 1.2 KB | 2.2 KB |
| B | 68 | 3,777 | 13 | 11.2 KB | 4.7 KB | 15.9 KB |
| C | 2 | 1,537 | 14 | 4.4 KB | 0.1 KB | 4.5 KB |

- Net of tables: A −54 KB, A+B −169 KB, A+B+C −182 KB.
- Out of sample: the PC9QB4 spec applied to PC9Q (11,078 leaves, an older build).
  - A 288.9, A+B 242.2, A+B+C 236.6 bits per leaf (−59 / −188 / −203 KB).
  - 667 escapes, of which 664 are in B (0.3% of point codes); every symbol round-trips.
- Context reads: A's and B's contexts are static loop positions (term pair, term and slot). An unrolled leaf decoder reads a constant table, so there is no runtime dispatch. C's context is κ, one of 2.
- **Prediction CHECK:**
  - SUPPORTED: A 290.6 (predicted 290.5–291.5); A+B 238.7 (238.5–240.5); A+B+C 231.8 (231.5–233.5); escape and cap overhead < 0.3 bits per leaf (0 in sample);
  - SUPPORTED: work per M leaf, 17 / 22.9 / 6.9 symbols and 2.6 / 4.7 / 8.9 loop steps per word;
  - mixed: tables B 15.9 KB (predicted 10–16) inside, A 2.2 KB slightly above 1–2 and C 4.5 KB below 5–7.
- Handoff (2026-10-11):
  - am-cert confirmed their Lean decoder implements the r13 spec exactly.
  - Encoded walks per variant are in `r13/walkcode_walks_PC9QB4.json` (environment variable WDUMP in walkcode.py).
  - bridge-port's DATA_PC9QB4_dp.json has the same walks and re-encodes bit-exactly (`r13/walkcode_PC9QB4_dp.log`).
- Longest leaf, from its node bit through the stop bit, against WIN 480: original 448; A 438; B 479; C 443; A+B 463; A+B+C 457.
  - Worst cases under the spec, with every symbol escaped and every κ = 3, are far above WIN (A+B+C 2,236 bits). The fixed layout's worst case is 886.
  - So WIN covers the data, as today, and must be re-checked on every new tree.

## Round 13b: loop-free codes (am-cert's request after the Lean measurement)

am-cert's measurement, recorded:
- The r13 canonical codes decode correctly in Lean. They cost +15% (A), +23% (B) and +34% (A+B) walk kernel instructions on nanoda, and +20/+33/+46% on the Lean kernel, against bars of +2% (A) and +4% (A+B).
- Fit: about 0.76M kernel instructions per codeword plus 0.11M per bit-loop step, against about 89M per fixed leaf check.
- L7/L8/L9 are recommended dropped.
- The ask: loop-free codes with at most 2 branches per term. am-cert's own count for a 1-bit modal-kind flag (else 1 + 2 raw bits) is −14.4 KB on PC9QB4.

**PRE-REGISTRATION (written before counting).** Savings on PC9QB4, in KB of hex:
- K1: modal-kind flag per position, else 1 + 2 raw: 13–16 KB (am-cert counted 14.4).
- K2: ranked two-flag code per position (mode 1 bit, second 2 bits, others 3 bits): 25–35 KB.
- K3: same-κ-as-previous-leaf flag, else 1 + 2: 15–30 KB. Needs the previous κ in the walk state.
- K4: modal pair flag per position pair, else 1 + 4 raw: less than K1.
- J1: modal-jj flag per (term, slot), else 1 + 7: under 10 KB, possibly a loss.
- J2: same-jj-as-previous-leaf flag, else 1 + 7: 50–100 KB. Needs 68 fields of walk state.
- L1: modal-λ flag per κ: under 3 KB.

**ROUND 13b RESULTS** (`loopfree.py`, `r13/loopfree.log`).
- Modal and rank tables are built on PC9QB4 and applied to PC9QB4 (in sample) and to PC9Q (out of sample).
- Savings are in bits per leaf, and in KB of hex.

| code | rule | PC9QB4 | PC9Q (oos) | bits per term or code | walk state |
|---|---|---|---|---|---|
| K1 | modal-kind flag per position, else 1 + 2 raw | 5.72 / 14.4 KB | 4.48 / 12.4 KB | 1.83 | none |
| **K2** | ranked flags per position: [1] mode, [01] second, [00x] others | **15.41 / 38.8 KB** | **14.53 / 40.2 KB** | 1.53 | none |
| K3 | same κ as previous leaf, else 1 + 2 | 13.57 / 34.2 KB | 12.59 / 34.9 KB | 1.59 | 68 bits |
| K4 | modal pair flag per position pair, else 1 + 4 | 8.67 / 21.8 KB | 7.38 / 20.4 KB | 1.74 | none |
| K5 | modal pair flag, else 1 + K1 per term | 2.42 / 6.1 KB | 0.50 / 1.4 KB | 1.93 | none |
| J1 | modal-jj flag per (term, slot), else 1 + 7 | −1.66 / −4.2 KB | −4.31 / −11.9 KB | 7.08 | none |
| J2 | same jj as previous leaf, else 1 + 7 | 30.65 / 77.2 KB | 27.16 / 75.2 KB | 5.61 | 476 bits |
| L1 | modal-λ flag per κ, else 1 + 10 | −5.32 / −13.4 KB | −5.73 / −15.9 KB | 10.80 | none |

- K1 reproduces am-cert's 14.4 KB exactly.
- K2 is the best stateless kinds code. It equals the 4-ary Huffman per position (1.53 bits per term), unrolled as a fixed decision tree: at most 2 flag reads, then 1 raw bit only on the third branch.
- Point codes need walk state to gain anything (J2); λ has no loop-free gain.
- **Prediction CHECK:**
  - SUPPORTED: K1 13–16 (14.4); J1 < 10 (a loss); J2 50–100 (77.2); L1 < 3 (a loss);
  - REFUTED, larger: K2 25–35 (38.8); K3 15–30 (34.2);
  - REFUTED: K4 smaller than K1 (it is 21.8 against 14.4).

## Round 13c: fixed-width point index with escape (lead's quick measurement)

**PRE-REGISTRATION (written before counting).** Only 67 jj values are canonical (33 per grid plus the range start). So:
- per-slot top-63, 6 bits: coverage ≥ 99.5%; saves about 0.97 bits per index ≈ 21.5 bits per leaf ≈ 54 KB hex, about 47 KB net of a 7.5 KB table;
- global top-63, 6 bits: coverage ≥ 99.5% too, almost the same saving with a tiny table, so the better choice;
- per-slot top-31, 5 bits: coverage 80–90%, saving 40–60 KB gross;
- PC9Q out of sample: coverage within 0.5 points of in-sample for top-63.

**ROUND 13c RESULTS** (`top63.py`, `r13/top63.log`).
- Tables are built on PC9QB4 and applied to PC9QB4 and to PC9Q (out of sample).
- 67 distinct jj values occur in total. Today's cost is 7 bits per index: 154.9 bits per leaf on PC9QB4 (22.13 indices per leaf) and 151.2 on PC9Q (21.61).
- Table cost: entries × 7 bits, in hex digits.

| variant | coverage QB4 / Q | worst slot (≥ 20 uses) QB4 / Q | bits/index QB4 | bits/leaf saved QB4 | KB hex saved, net of table, QB4 / Q |
|---|---|---|---|---|---|
| per-slot top-63, 6 bits | 99.977% / 99.682% | 99.71% / 82.6% | 6.00 | 22.1 | 48.2 / 51.0 |
| global top-63, 6 bits | 99.940% / 99.921% | 99.33% / 99.37% | 6.00 | 22.0 | **55.4 / 59.4** |
| **per-slot top-31, 5 bits** | 94.20% / 92.60% | 86.8% / 78.3% | 5.41 | 35.3 | **85.2 / 85.0** |
| global top-31, 5 bits | 90.98% / 90.71% | 83.3% / 84.2% | 5.63 | 30.3 | 76.2 / 80.7 |
| per-slot top-15, 4 bits | 76.97% / 74.58% | 49.4% / 39.6% | 5.61 | 30.7 | 75.6 / 71.2 |
| global top-15, 4 bits | 65.90% / 65.06% | 26.6% / 28.7% | 6.39 | 13.6 | 34.2 / 33.1 |

- Table sizes in hex: per-slot top-63 7.5 KB, top-31 3.7 KB, top-15 1.8 KB; global tables 0.1 KB or less.
- **Prediction CHECK:**
  - SUPPORTED: per-slot top-63 coverage ≥ 99.5% with about 47 KB net (99.98%, 48.2); global top-63 coverage ≥ 99.5% and better than per-slot (99.94%, 55.4); top-63 out of sample within 0.5 points (0.30 and 0.02);
  - REFUTED, larger: per-slot top-31 coverage 80–90% (94.2%) and saving 40–60 KB (88.9 gross, 85.2 net).

**Lean cost of the round-13b/13c codes** (am-cert, 2026-10-11, 4 PC9QB4 walks; walk-only instructions against the current decoder, nanoda / Lean replay):
- K1: +3.6 / +3.6%.
- K2: +2.9 / +4.4%. A dec4F-style variant measured +4.5 / +5.2%.
- Global top-63 point index with escape: +3.6 / +6.8%.
- K2 + top-63: +6.1 / +8.8%.
- About 100k kernel instructions per term per extra branch. Every code lands near 0.75–0.9 board-s per KB saved.
- am-cert reproduced the byte sizes exactly: K2 −38.8 KB, top-63 −55.5 KB, together −94.3 KB.
- The lead's choice waits on INT9Q4's time margin. am-cert's pointer for further work: the lever now is fewer operations per term in the existing leaf check (time), not more coding (bytes).
- Time lever (2026-10-11): NOT NEEDED for this submission. After L6 the board time is ≈ 2,670 s against the 3,000 s gate, a margin of ≈ 330 s; the lead's trigger was < 150 s.
  - am-cert's walk-instruction profile on 4 PC9QB4 walks, for the record:
    - main inequality: 27–32%;
    - lever-1 side conditions: 12–19%;
    - decode, multipliers, splits and navigation: 43–52%.
  - No per-κ breakdown exists. A per-κ variant bench would give one.
