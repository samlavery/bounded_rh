# Lemma P state note: board cost of the current certificate architecture

Author: am-cert, 2026-10-09.

Everything in this note is an estimate. No Lean module was built for it and no script was run. Each number is labelled as one of the following:
- **[measured]**: taken from a kernel, board or Python run that has already happened;
- **[counted]**: read from a script or log;
- **[estimated]**: a projection built from the two above.

"Does not fit" is a statement about the certificate architecture priced here. It says nothing about Lemma P itself.

## 1. Status

- **Board route:** paused (lead, 2026-10-09).
- **Reason:** condition 9 (locality or covering for the per-configuration pieces) is refuted for the positions-only QP-optimal witnesses (e35, e36). Without it, pieces 3 and 4 have no finite count, so the architecture's board cost has no bound.
- **Conditions 2, 3 and 11:** all reported (section 6).
  - Condition 11 is refuted.
  - Conditions 2 and 3 pass as tested. The band in condition 2 was tested in DISTANCE (r ≥ 1 in u), not in cells. At the 1/256 cell resolution near the pair, a band of distance 1 is 256 cells. Re-priced on the tested band, piece 2a alone exceeds both budgets (section 4).

## 2. Calibration constants and their sources

| constant | value | status | source |
|---|---|---|---|
| board seconds per 1e9 net kernel instructions | 0.86 | [measured] | lead's PC8 board calibration. Predicted vs actual: PC8SF 2,295 vs 2,319 s; PC8T 2,969 vs 2,944 s |
| kernel throughput | ≈ 6.7e9 instr/s | [measured] | PC8E4 module replay: 1.368e12 instructions in 204.6 s |
| board-s per kernel-s | ≈ 5.8 | [estimated] | product of the two rows above |
| job model | ≈ 148 + 2·build + 6.7·replay s | [lead] | riemannzeta-fun submission memory |
| base D file | ≈ 1.65 ks board | [estimated] | D-file projection (DE_LEAN_STATE.md) |
| budget left for all Lemma P certificates, conservative | ≈ 950 board-s | [lead] | the safe-job rule ("keep it ≤ about 2,600 s", riemannzeta-fun submission memory) minus the ≈ 1.65 ks base D file |
| budget left for all Lemma P certificates, nominal | ≈ 1,300 board-s | [lead] | the 3,240 s hard timeout minus the base D file and a margin of about 290 s |
| F: one certified Taylor cell of K(u+iy), ψ, c_m, X or g | LOW 5 ms, HIGH 50 ms kernel | [estimated] | GIv cell leaves measured at 1.7–7 ms on 13-term AM-window cells (PC8 series). The Lemma P functions are not ported to GIv |
| F on the D file's current ℚ-interval path | 0.82 kernel-s per cell | [measured] | certH_R8 (DEQfR8.lean): 161 cells, 936e9 instructions (881e9 net), peak 2.4 GB. A test at m_h 5e-5 gave 113 cells, 626e9 net, i.e. 0.83 kernel-s per cell |
| B: one exact table check (tree lookup, a few GMP operations, compare) | LOW 15 µs, HIGH 150 µs | [estimated] | Not measured directly. Naive-path anchor: DESOS `decide` over Finset Int products, 9,216 products in 3.14 s ≈ 0.34 ms each [measured] |

Budget note: two figures are given, the conservative one first.
- The conservative figure, about 950 board-s, comes from the 2,600 s safe-job rule.
- The nominal figure, about 1,300 board-s, comes from the 3,240 s hard timeout.
- UPLOAD_PC8E was accepted on the board at a predicted 2,632 s, so the real ceiling lies between the two.
- The conclusions in section 7 hold under either figure.

The single largest multiplier is the cell evaluator. The measured ℚ path is about 160 times the LOW value of F. Every compressed LOW figure below assumes the GIv port exists.

## 3. Certificate sizes behind the prices [counted]

- **Shared tables (crowd_dp.py):**
  - c_j for j ≤ 9 on a 1/2048 grid up to u = 130, which is 2.4e6 values;
  - g on a 1/8192 grid up to 130, which is 1.06e6 values.
- **Chain DP cells:** K = 7,296 per side. Widths:
  - 1/256 on [0, 5];
  - 1/128 on [5, 16];
  - 1/64 on [16, 48];
  - 1/32 on [48, 128].
- **Mixed allocated DPs (crowd_dp4 A / B / C14):**
  - 64 y-intervals: 15 + 35 + 14;
  - cluster cap 32, masses {1, 2};
  - about 1.06e8 other-bin and 2.3e7 same-bin transitions per DP;
  - Python time 7–8 s per DP [measured].
- **X-lemma (xlemma_exact.py):** d-grid step 0.01 from the class start to 64, with 3 × 21 (y_q, y_p) nodes per y-interval.
- **Allocation check (mixed_alloc_exhaustive.py):**
  - 3^10 = 59,049 neighbour sequences per side, about 6,000 u-nodes, 3 central classes;
  - result sup Σ c_p ≤ 0.9949 [measured].
- **Deep single pair (deep_cert.py):** u-grid 1/512 on [0, 64] (32,769 nodes), y-cells of width 0.002. On [0.8, 12] that is 5,600 cells, about 1.8e8 corners.
- **Dense-block DP (multi_env_dp.py, XL = 1024):**
  - 26,812–39,006 cells, cluster cap 24, P = 16–64;
  - the low-band test function sums about 17,000 nodes per cell edge;
  - Python time 25–73 s per DP [measured].
- **Deep chains (sat9):**
  - n = P + 8 witness coefficients for the positions-only family; 3(P + 8) at K = 2;
  - 16 exact-lattice witnesses in e34_witness.json, with n = 14–56 and hard D from +5.9 to +123 [measured];
  - per bridge-port, witness denominators of 2^32–2^40 are needed.

## 4. Cost table

Units are board-s. "As-is" means the current grids and DPs ported unchanged, with every edge replayed.

"Compressed" means the same inequalities written with:
- Taylor-4 cells;
- pencil tails;
- an in-kernel banded DP replay. A stored potential is ruled out: it is about 4.8e5 values, roughly 4 MB, per DP.

The compressed column depends on the conditions in section 6. All rows are [estimated].

| piece | as-is LOW | compressed LOW | compressed HIGH | size |
|---|---|---|---|---|
| 0. Shared ψ / c_m / g tables (used by 1, 2, 4) | 1.0e5 (3.5e6 grid values, ≥ 40 MB) | 116 (4e3 cells) | 5,800 (2e4 cells) | known |
| 1. Single pair, deep part y ≥ 0.8 | 5.3e6 (1.8e8 grid corners) | 162 (5.6e3 cells) | 6,700 (2.3e4 cells) | known |
| 2a. Allocated chain DPs | 7.3e5 (8.4e9 transitions) | **≈ 8,800** (30 DPs, K = 2,688, band r = 1 in distance as tested, cluster levels as measured, 1.0e8 checks). Mid-case ≈ 26,000 (current K and 64 intervals, 3.0e8 checks). The earlier 270 assumed a band of 4 CELLS, which was not tested (section 6) | ≈ 4.2e5 (64 DPs, K = 7,296, r = 2, 4.8e8 checks) | known |
| 2b. X-lemma, mixed annuli | 7e5 (2.4e7 X evaluations) | 190 (5.4e3 c_m cells for d < 16, IBP beyond, 3.4e5 checks) | 17,400 (6e4 three-dimensional cells) | known |
| 2c. Allocation check | 9.2e5 (1.1e10 weight evaluations) | 5 (pencil reduction plus ≤ 1e4 exact checks) | 3,300 (DP over sequences, 3.8e6 checks) | known |
| 5. Interval upgrade | none (Lean checks are rigorous natively) | +0 | ×2–4 on the cell-dominated rows | known |
| **Known-size subtotal** | **≈ 7.8e6** | **≈ 9,260** (was ≈ 743 on the untested 4-cell band) | **≈ 4.5e5 (×2–4)** | |
| 3. Deep chain, per lattice chain at P = 48 | 2,560 (441 y-cells) | 500, revised to ≈ 920 after e37 (section 5). Would be 12 under condition 11, which is refuted | ≈ 5,000–9,200 | count UNBOUNDED |
| 3. Deep chain, per irregular chain at P = 48 | 6.4e4 | 6,700. Would be 220 under condition 11, which is refuted | ≈ 6.7e4 | count UNBOUNDED |
| 3. Regime B, one (chain, labelling) at K = 2 | | ≈ 3× the positions-only figure | | count UNBOUNDED (K^P labellings) |
| 3. Search node carrying W (n·J = 360) | | ≈ 310 | ≈ 3,100 | count UNBOUNDED |
| 4. Dense block, per DP | 2.7e5 (3.1e9 transitions) + 5.8e4 (low-band sum) | ≈ 4,000–7,600 (band r = 1 in distance over about 17,900 cells at 1/256; 6–15 cluster levels, since in a dense block most cells are within 1 of some pair). The earlier 430 assumed a 4-cell band | ≈ 7.6e4 | count UNKNOWN (no covering method) |

Two notes on scope:
- The single pair with y ≤ 0.8 is a one-element separated set. Piece 2a's DPs therefore cover it and it is not counted twice.
- The compressed split of piece 1 differs from the earlier "400–900" design figure. In that figure the shared tables and the y ≤ 0.8 DPs were inside piece 1; here they are rows 0 and 2a.

## 5. Addendum: piece 3 repriced with bridge-port's sizes

The y-minimum over [0.8, 3] is very sensitive to the witness. The one-body coefficients reach 1e6–1e7 at y = 3 while the margins are D = 5.9 to 123. A plain y-grid would need a step of about 1e-7, i.e. about 2e7 nodes per pair (bridge-port). That is infeasible.

Compressed alternative [estimated]:
- Expand each pair's one-body term in y² to J ≈ 40 orders.
- Compute the coefficients at exact points, to a relative precision of about 1e-13.
- Check positivity of the resulting polynomial per pair on about 22 Taylor-10 subcells.

| item | LOW (board-s) |
|---|---|
| lattice chain, P = 48: about 8,000 point evaluations at 1.5× precision | ≈ 350 |
| lattice chain, P = 48: polynomial checks, about 1.7e6 per chain | ≈ 150 |
| **lattice chain total** | **≈ 500** |
| irregular chain, P = 48 | ≈ 6,700 |

If the endpoint lemma (condition 11) held, two depth nodes per pair would suffice. That would give about 12 per lattice chain and about 220 per irregular chain. Condition 11 is refuted (section 6), so these figures do not apply.

**Revision after e37 [estimated].** The ≈ 500 figure assumed about 22 Taylor-10 subcells per pair. e37 places interior minima at y ≈ 2.5–2.93, with slopes of 10²–10⁴. The per-pair error budget is about 0.1 (D ≈ 5.9 spread over 48 pairs). Certifying the minimum then takes about 170 subcells per pair on [2.4, 3]. Each subcell needs a local Taylor-10 expansion taken from the degree-80 series, about 800 operations.
- The polynomial-check line rises from ≈ 150 to ≈ 570.
- The lattice-chain LOW rises from ≈ 500 to ≈ 920.

Within one chain the bisection is finite: its size is set by slope × width / slack. What is unbounded is the family of chains.

## 6. The eleven conditions for the compressed version to fit, and their status

| # | condition | status (2026-10-09) |
|---|---|---|
| 1 | The Lemma P functions (K at complex arguments, ψ, c_m, X, g) are ported to the GIv engine at ≤ about 5 ms per cell | NOT BUILT. The measured ℚ path costs 0.82 kernel-s per cell |
| 2 | Banded DP: bonds beyond r cells are replaced by 0 (g ≥ 0, certG_R8) plus a suffix minimum, and the margins survive | **PASS as tested, with r in DISTANCE** (window-scope round 5). A band in cells (r ≲ 1/16 in distance near the pair) is NOT TESTED; it is the test that decides piece 2a's cost |
| 3 | Cluster monotonicity: the DP value is monotone in the cluster count p, so at most 3 levels need replay | **PASS (partial)** (window-scope round 5). Monotone exactly. ≤ 3 levels away from the pair; for u < 1, up to 6 levels (B) or 15 (C14) |
| 4 | Pencil tails: ψ from u ≥ 16 (now 128), deep asymptotics from y ≥ 3 (now 10, numerical in deep_asym), X from d ≥ 16, piece-4 fields beyond 16 | NOT STARTED |
| 5 | y-intervals coarsened from 64 to about 30 by Taylor bounds in y² | NOT TESTED |
| 6 | The X-lemma triangle bound across Taylor orders loses < 3 % on class a's binding interval [0.175, 0.1875], where m − R = 0.038 on R = 1.24 | NOT TESTED |
| 7 | The allocation check closes by a pencil reduction | NOT STARTED. The numerical exhaustive check passes with 0.5 % slack (0.9949) [measured] |
| 8 | Piece 5's heuristic allowances (xlemma's ×2 neighbour variation, ×1.05 finite-difference constants) are replaced by proven bounds without extra cells | NOT TESTED |
| 9 | Locality or covering: pieces 3 and 4 together reduce to about one certified unit, i.e. ≤ about 207 board-s (conservative) or ≤ about 557 (nominal) | **REFUTED for QP-optimal positions-only witnesses** (details below). Piece 4 has no covering method |
| 10 | Byte headroom of about 100–300 KB in the D file for the Lemma P modules | UNKNOWN. The D file's byte count is not available to me. If it carries a PC8-sized AM chain, the headroom is about 60 KB |
| 11 | Endpoint lemma: each pair's one-body minimum over y ∈ [0.8, 3] sits at y = 0.8 or y = 3 | **REFUTED, numerical strength** (bridge-port e37 / e37b; details below) |

The evidence for condition 9 is two transplant tests on QP-optimal positions-only witnesses:
- **e35:** end radius r ≤ 12, P = 24 → 48. Losses 3e3 to 5e6.
- **e36:** r = 16 / 20 / 24, P = 64 → 128. Hard D at r = 24 is −2.2e4, −1.4e4, −7.3e4 and −5.5e4 for a = 0.60 / 0.70 / 0.76 / 0.80. At r = 16 the losses reach 3.5e5.
- The witness interior is not converged in P. At a = 0.6 its median falls from 0.017 at P = 64 to 0.00016 at P = 128.
- Strength: these are numerical results, double precision, with hard evaluation on a y-grid of step 0.005.
- Not tested: regularised duals, and a lower top depth (bridge-port's suggested fixes).

The evidence for conditions 2 and 3 is window-scope's round 5 (band1/crowd_dp4_banded.py; band1/round5_banded_{A,B,C14}.log):
- **Condition 2, what was tested.** Every bond whose cell distance exceeds r is set to 0, and the successor search beyond r becomes a suffix minimum. Here r is a DISTANCE in u: `searchsorted(lo, hi[k] + r)`.
- **Condition 2, results** (min of margin − X charge, per class):

  | band | A | B | C14 |
  |---|---|---|---|
  | r = ∞ (validation; reproduces the logged bounds) | +0.0378 | +0.1924 | +9.6174 |
  | r = 4, r = 2 (lossless to 4 decimals in all 64 intervals) | +0.0378 | +0.1924 | +9.6174 |
  | r = 1 | +0.0205 | +0.1811 | +9.6124 |

  All three classes stay closed at every band tested. Strength: numerical, double precision.
- **Condition 3.** W[m, p, k] is non-decreasing in p, with 0 violations. Saturation levels p* (W constant beyond p*):
  - A: p* ≤ 1;
  - B: p* ≤ 5;
  - C14: p* ≤ 14.

  More than 3 levels are needed only for u < 1: at most 257 of 7,296 cells per interval, plus one stray B cell.
- **Cost consequence [estimated].** The compressed 2a price of 270 assumed a band of about 4 CELLS, i.e. 5 transitions per state. The tested band is distance 1. At the 1/256 resolution on [0, 5] that is 256 forward cells per state: about 192 in other half-bins and about 64 in the same half-bin, the latter times the cluster levels.
  - Per DP (K = 7,296, r = 1): ≈ 2.2e6 other-bin transitions plus ≈ 2.2e6–2.9e6 same-bin transitions, giving 4.4e6–5.2e6 checks.
  - 64 DPs: ≈ 3.0e8 checks, ≈ 26,000 board-s at the LOW check cost.
  - With conditions 4 and 5 (K = 2,688, 30 DPs): ≈ 1.0e8 checks, ≈ 8,800 board-s.
  - Even at a check cost of 5 µs (below any measured anchor), this is ≈ 2,900 board-s.
- **What would bring 2a back to the hundreds,** both untested:
  - a cell-scale band, r ≈ 1/64–1/16 in distance near the pair;
  - a coarser near-pair cell grid with Taylor bounds for the bonds.

  Whether a band below about 1 survives is an open numerical question. Nothing in this note decides it.

The evidence for condition 11 is bridge-port's e37 and e37b (sat9/e37_endpoint.py, e37b_check.py and their logs):
- **Interior minima.** 440 pairs across all witness families have an interior y-minimum below both endpoints, beyond the grid error, at y ≈ 2.5–2.93.
- **Dip sizes.** Up to 0.14 for positions-only witnesses (e36, a = 0.80, P = 128) and up to 0.54 for D_K witnesses (e23 minimiser, P = 16).
- **Quadrature check.** A 4× finer y-grid (6,001 → 24,001 nodes, e37b) leaves the argmins and dips unchanged to within about 3e-3.
- **The proposed mechanism, half by half:**
  - "g_p has one sign change" is false: g_p has 4–213 sign changes per pair;
  - "B_{y'}/B_y is monotone in α" is true, with a pencil proof.
- **Strength:** numerical, double precision.
- **Consequences:**
  - The two-node saving (≈ 40×) does not follow.
  - The data support only min ≥ min(endpoints) − 0.6, and even that is uncertified.

## 7. Totals against the budget, ≈ 950 (conservative) and ≈ 1,300 (nominal) board-s [estimated]

**As-is.** The known-size LOW is about 7.8e6 board-s. Under the pre-registered rule, the current architecture ported as-is does not fit the board budget under either figure.

**Compressed, with the band as tested (final).** The known-size LOW is about 9,260, of which piece 2a is about 8,800. Under the pre-registered rule, the compressed architecture also does not fit the board budget, under either figure.

At the smallest count, one dense-block DP (≈ 4,000) plus one lattice chain (≈ 920): ≈ 14,200 board-s.

**Superseded figures, kept for the record:**
- The compressed known-size LOW of ≈ 743 assumed a 4-cell band, which was not tested.
- With it, the smallest-count totals were 1,673 and 2,093 (lattice chain at 500 and 920), and 1,185 under condition 11, which is now refuted.

**What remains open, and would change this [both untested]:**
- a cell-scale band, r ≈ 1/64–1/16 in distance near the pair, for pieces 2a and 4;
- a coarser near-pair cell grid.

If a cell-scale band held, piece 2a would return to about 200 and the known-size LOW to about 680. Even then, pieces 3 and 4 have no finite count: condition 9 is refuted for the tested witness family. So this architecture's board cost has no bound either way.

**Dominant costs:**
- Among the known-size pieces, piece 2a dominates: ≈ 8,800–26,000 LOW. Its cost is the distance band of 1 times the 1/256 near-pair resolution.
- Overall, the per-configuration pieces 3 and 4 have no count bound, at ≈ 920–7,600 per unit at LOW.
- The largest multiplier is the cell evaluator: at the measured ℚ-path rate, pieces 0, 1 and 2b alone come to about 85,000 board-s.

## 8. Prediction check

**What was predicted.** Before reading the scripts, I pre-registered that the LOW estimates of the known-size pieces would exceed 1,300 board-s, with confidence about 65 %. That prediction is the "does not fit" branch.

**Outcome:**
- **As-is reading:** confirmed (about 7.8e6).
- **Compressed reading on the first pass:** refuted (about 743).
- **Compressed reading on the band as tested (final):** confirmed (about 9,260).

The first-pass refutation rested on my own unchecked assumption that the band would be a few cells.

**What was wrong in the reasons:**
- I expected the interval upgrade (piece 5) to multiply cell costs 2–5×. In Lean the checks are rigorous natively, so it adds +0 at LOW.
- I expected one dense-block DP to cost at least 1,700 because of the cell resolution. The final figure, ≈ 4,000–7,600, comes from the band width instead.
- I wrote condition 2 as "r cells" without fixing the unit. The test fixed it as distance, and the first-pass 743 depended on the narrower reading.

**What held:**
- Adding the unknown-count pieces at their smallest counts takes the total past both figures.
- The DP replay is the dominant known-size cost.

## 9. Sources

- band1/crowd_dp.py, crowd_dp4.py, crowd_dp4_mix{A,B,C,C14}.log
- band1/xlemma_exact.py, xlemma_mix{A,B,C,C14}.log
- band1/mixed_alloc_exhaustive.py and its .log
- band1/deep_cert.py, deep_cert_06_12.log
- band1/multi_env_dp.py, round2_scan5.log, round3_far_*.log
- sat9/e32d_qp.py, e33_classK.py, e34_witness.json, e35_locality.py, e36_transplant.py and their logs
- rootR8f/AMW/DEQfR8.lean (certH_R8 measurement)
- band1/crowd_dp4_banded.py, round5_banded_{A,B,C14}.log (conditions 2 and 3)
