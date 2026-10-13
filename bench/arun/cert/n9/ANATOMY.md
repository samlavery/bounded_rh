# PC9L / t570 leaf anatomy and engine levers (bridge-port, 2026-10-10)

Phase 1 of the 9-point fit campaign: diagnosis only, no Lean builds. Inputs are the saved sizing dumps:
- `cert/n9/dump_kb_2e-4.pkl`: PC9L, lp9 weights, δ 2e-4, 17,551 leaves.
- `cert/n9/dump_full_t570.pkl`: t570, δ 5e-5, 14,906 leaves.

## 0. Pre-registration (written before any anatomy number or counterfactual run exists)

### Method

**(A) Anatomy from the dumps** (`anat9.py`). For every leaf it records:
- widths per gap in gap units, and depth;
- relative excess F/c − 1 at the box centre, using the exact float kernel;
- Euclidean distance in gap space to the nearest near-binding word (lp9: the 16 basins in `est/cert9_inputs.json`; t570: the
  file's `root_hints_near_binding`);
- the minorant kind per term from the payload (constant / tangent / constant+tangent / two tangents), and the curvature class of
  the term's range (w″ > 0 throughout, w″ < 0 throughout, or mixed);
- leftover slack: (min over the leaf polytope of the float certificate − cN)/cN, compared with the true slack
  (min F over the leaf − cN)/cN.

**(B) Why parents split** (`anat9.py`, a random sample of last-level split nodes, i.e. nodes with two leaf children). In float:
- s_true = min F over the cell / cN − 1;
- LP1 = the LP relaxation with exact constants and the engine's tangent positions under EXACT validity;
- LP2 = LP1 plus second-order (chord-of-quadratic) candidates.

Classification of each sampled parent:
- **engine-specific** (validity tchk / table / quantisation): LP1 ≥ 0;
- **first-order curvature**: LP1 < 0 ≤ LP2;
- **beyond second order** (width): LP2 < 0;
- **near-binding margin**: s_true < 1e-3 (reported as an overlay, not a separate bin);
- **root-box / linear-pay**: depth ≤ 3, or a gap range reaching into the linear-pay band.

**(C) Counterfactual sizings with the real sizer** on the calibrated subset (roots 2/5/9). Every variant runs with LPACCEPT=1 (the
leaf passes on its LP value; this removes multiplier rounding), against a baseline that also uses LPACCEPT=1. The variants
isolate one lever each:
- **V**: EXACTV=1, tangent validity by an exact check; lever (iv), precertified validity;
- **C**: EXACTC=1, exact constant minorants; the table-resolution limit;
- **VC**: both;
- **SO**: second-order candidates, chord of the quadratic minorant with m = min w″ on the range (my sizer copy `size9so.py`);
  lever (i);
- **SOVC**: SO + V + C;
- **PF16**: PFK=16 against 8, with the normal leaf test; lever (iii), split-axis choice.

All of these are sizing-only float models of a future engine, not certificates.

### Predictions

1. **Leaf location:** leaves are spread through the bulk. The median relative excess at the leaf centre is > 1e-2 (above the
   near-binding level). Leaves within distance 0.05 of a near-binding word are < 20 % of all leaves.
2. **Minorant use:** ≥ 30 % of term slots in leaves use the constant minorant alone. Those terms are mostly on concave or mixed
   ranges, where tangents fail validity.
3. **Parent split reasons** (sampled last splits):
   - first-order curvature (LP1 < 0 ≤ LP2) is the largest bin, 40–60 %;
   - engine-specific 15–35 %;
   - beyond second order 10–25 %;
   - near-binding margin < 15 %.
4. **Leftover slack:** the median leaf keeps < 50 % of its true slack. Halving loses a factor 2–4 in loss, so leaves are not
   grossly over-split.
5. **Counterfactual leaf reductions** against the LPACCEPT baseline:
   - V −10 to −25 %; C −5 to −15 %; VC −15 to −35 %;
   - SO −30 to −50 %; SOVC −40 to −60 %;
   - PF16 −5 to −10 %.
6. **Far-field test (ii):** about 0 % on leaf count. The constant minorant already is the far-field bound. Its value is per-leaf
   kernel time in large-excess boxes.
7. **Ranking:** SO > VC > V > C > PF16 > far-field. No single lever reaches ≲ 8–9k from 17.6k (it needs −50 %); SOVC might, for
   t570 (14.9k → ≲ 8k needs −46 %).

### Addendum to the pre-registration (written 17:30, after a 20-parent smoke test of `anat9.py` and before any counterfactual or full-sample number)

**What the smoke test showed** (20 t570 parents): the ideal first-order LP value LP1 sits at ≈ 0 for most parents (−0.009 … +0.014),
and LP2 = LP1 to 4 digits.

**Why (pencil):** every linear minorant of w on a term's range lies below the convex envelope of w on that range. So an LP leaf test
with linear-per-term minorants is capped at the convex-envelope bound, and the chord-of-quadratic candidates cannot beat it. SO
therefore tests the wrong form of lever (i).

**Added test, NSO:** the NON-CONVEX second-order leaf test.
- Per term, q_t(s) = w(p) + w′(p)(s − p) + m_t(s − p)²/2, with m_t = min w″ on the range.
- Accept when min over the cell of b·g + Σ a_t q_t(s_t) ≥ c. The minimum is computed by local SLSQP from several starts, so the
  estimate is optimistic.
- This is the lead's lever (i) as stated ("tangent + certified curvature lower bound"). In Lean it needs a non-convex check: for
  example vertex enumeration when every q_t is concave, or a small branch inside the leaf.
- Runs: `size9so.py` with NSO=1, counterfactual t570_NSO; `anat9.py` reports `nso` per parent.

**Predictions:**
- SO: −0 to −10 % (revised from −30 to −50 %, because of the convex-envelope cap).
- NSO: −20 to −40 %.
- Parent bins: engine-specific (LP1 ≥ 0) 30–50 %, the convex-envelope gap (LP1 < 0 ≤ NSO) 30–50 %, beyond second order 10–30 %.

These revisions are recorded as made AFTER the smoke test. The original predictions above stand for scoring.

### Addendum 2 (written 17:45, after the full anatomy and the span breakdown, before any SEP number)

**What the anatomy showed so far:**
- NSO never passes. Its curvature bound over ~0.5-unit term ranges is far too negative.
- At failing parents, 50 % of the ideal-LP relaxation error sits on the ADJACENT terms (span 1, s_t = g_r). 92 % sits on terms that
  already have tangent candidates. So the loss is the convex-envelope gap, not missing tangents.

**New lever SEP (separable adjacent terms):** take the LP's own duals. In the Lagrangian, replace each adjacent term's dual-mixed
lines by a_t·w(g_r) itself and minimise gap by gap.
- It is a valid bound, and at least the LP value.
- In Lean it is a 1-D per-gap check against the w table: a few table reads per gap, no new walk fields.
- Implemented sizing-only in `size9so.py` (SEP=1); compared against B0.

**Prediction:** SEP −20 to −35 % against B0; SEP+V −25 to −40 %.

## 1. Results (18:20)

Sources:
- `anat/anat_t570.json` and `anat/anat_pc9l.json`: all leaves; 3,000-leaf and 1,500-parent samples (`anat9.py`).
- `anat/anatb_t570.json`: 800 parents (`anat9b.py`).
- `cfx/t570_*.log`: `cfx9.sh`, t570 at δ = 5e-5, roots 2/5/9, the calibrated subset (normal engine = 3,966).

### 1.1 Where the leaves are (prediction 1: HELD)

| | t570 | PC9L |
|---|---|---|
| excess F/c − 1 at the leaf centre, q10 / q50 / q90 | 1.72 / 2.53 / 3.35 | 1.62 / 2.50 / 3.26 |
| leaves with excess < 1e-2 / < 0.1 / < 1 | 0.0 % / 0.1 % / 1.6 % | 0.0 % / 0.1 % / 3.2 % |
| distance to the nearest near-binding word: median; share < 0.05 / < 0.5 | 3.30; 0.0 % / 0.4 % | 2.63; 0.0 % / 2.6 % |
| depth q10 / q50 / q90 | 14 / 24 / 32 | 13 / 24 / 35 |
| median width per gap (gap units) | 2.73 1.03 0.48 0.44 0.44 0.48 1.00 2.71 | 2.84 0.99 0.48 0.44 0.44 0.48 1.01 2.90 |
| narrowest gap per leaf, median | 0.44 | 0.44 |

The leaves are in the BULK: the median leaf centre sits at F ≈ 3.5c, far from every basin. The middle gaps are cut to ≈ 0.44.

### 1.2 Minorants (prediction 2: HELD)

| | t570 | PC9L |
|---|---|---|
| term slots using the constant minorant alone | 49 % | 50 % |
| term slots using a tangent / constant+tangent / two tangents | 31 % / 9 % / 11 % | 31 % / 9 % / 10 % |
| term ranges with MIXED curvature (w″ changes sign) | 97.5 % | 95.8 % |
| term ranges purely convex / purely concave | 2.4 % / 0.2 % | 3.8 % / 0.4 % |

w has lobes about 0.5–1 wide in s. Pair ranges of ≥ 0.44 almost always straddle an inflection.

### 1.3 Leftover slack (prediction 4: HELD, and stronger)

Certificate slack ÷ true slack per leaf (the float certificate minimised over the leaf polytope, against the true min of F there):

| | q10 | q25 | q50 | q75 | q90 |
|---|---|---|---|---|---|
| t570 | 0.017 | 0.042 | 0.108 | 0.24 | 0.49 |
| PC9L | 0.018 | 0.044 | 0.117 | 0.24 | 0.56 |

**The leaf certificate keeps about 11 % of the true slack.** Leaves are about 9× tighter than the function needs, but only as tight as the
LP relaxation needs.

### 1.4 Why parents split (prediction 3: REFUTED in its main bin)

Bins over 1,500 sampled last-level parents:

| bin | t570 | PC9L |
|---|---|---|
| engine-specific: the ideal first-order LP passes (LP1 ≥ 0), so rounding, validity tables or constant tables made it fail | **60.7 %** | **66.1 %** |
| fixed only by the second-order chord candidates (LP1 < 0 ≤ LP2) | 1.7 % | 1.3 % |
| fixed only by the non-convex second order (NSO) | 0.0 % | 0.0 % |
| beyond all of these (convex-envelope gap) | 37.6 % | 32.6 % |
| overlay: near-binding (true slack < 1e-3) | 0.0 % | 0.9 % |
| overlay: root box (depth ≤ 3) | 0.2 % | 0.7 % |
| overlay: a constant-only exact bound would pass | 21 % | 29 % |

- LP1 at the parents clusters at 0: q50 is +0.003, and 19 % of parents sit in [−0.01, 0).
- **Relaxation error at the LP point** (800 parents): 50 % on the adjacent terms (span 1). Spans 2–8 carry 9 / 9 / 9 / 7 / 6 / 5 / 4 %.
  92 % is on terms that HAVE tangent candidates. So the loss is the convex envelope of a mixed-curvature w, not missing candidates.
- **Pencil:** every linear-per-term minorant lies below the convex envelope of w on the range. An LP leaf test is therefore capped at
  the convex-envelope bound, whatever the candidates.

### 1.5 Counterfactual sizings (t570 subset; normal engine 3,966 leaves, 305 bits/leaf)

**Real engine (meval on):**

| variant | subset leaves | vs normal | bits/leaf (sizer) |
|---|---|---|---|
| normal (λ 8 bits, multiplier quantum 2⁻¹⁴, PFK 8) | 3,966 | — | 305.0 |
| **λ 10 bits (LSC 1024)** | 3,512 | −11.4 % | 309.0 |
| multiplier quantum 2⁻¹⁶ (YFRAC 16) | 3,738 | −5.7 % | 308.4 |
| **both** | **3,274** | **−17.4 %** | 313.1 (walk bits −15.3 %) |
| PFK 16 (wider split choice) | root 2 alone ≥ 5,000 when stopped (normal: 1,230) | WORSE, ≥ ×4 | — |

**Leaf accepted on its LP value (rounding removed), sizing-only:**

| variant | subset | vs B0 |
|---|---|---|
| B0 | 3,143 | (−20.8 % vs normal: the whole rounding loss) |
| C (exact constants, i.e. tables) | 3,080 | −2.0 % |
| SEP (separable adjacent terms) | 3,035 | −3.4 % |
| SO (second-order chords) | 3,023 | −3.8 % |
| V (exact tangent validity: lever 1 / iv) | 2,965 | −5.7 % |
| VC | 2,936 | −6.6 % |
| SEP+V | 2,826 | −10.1 % |
| SO+V+C | 2,808 | −10.7 % |
| **ALL (SO+V+C+SEP)** | **2,695** | **−14.3 %**; **−32.0 % vs normal** |
| NSO (non-convex second order) | identical to B0 on roots 2 and 5; stopped | 0 % |

**Scoring prediction 5:**
- V, C, VC, SO+V+C: each BELOW its predicted range (smaller gains).
- SO: inside the revised range, below the original one.
- PF16: refuted, wrong sign.
- NSO: refuted, 0 %.
- SEP: refuted (−3.4 % against −20…−35 %).

**Prediction 6 (far field):** no separate run. Every parent a constant-only exact bound passes also passes LP1, so the far field adds
no leaf-count gain. It is a kernel-time lever only. Held, as an inference.

### 1.6 Ranked levers, with estimated full leaf counts

The estimates apply the subset ratio to the full counts: t570 14,906, PC9L 17,551.

1. **Certificate quantisation** (λ 10 bits + multiplier quantum 2⁻¹⁶): −17.4 % leaves, +2.7 % bits/leaf, so −15 % walk bytes.
   - t570 ≈ 12.3k; PC9L ≈ 14.5k.
   - It is a field-width change (LB from the data, SIGSH 14 → 16 in emit/generators and the Inst `SIG`), the cheapest lever.
2. **Exact tangent validity** (precertified validity, lever 1/iv): about −6 % more.
3. **Second-order chords** (−4 %), **separable adjacent terms** (−3 %), **exact constant tables** (−2 %).
4. **Everything above together:** −32 % against the normal engine, giving **t570 ≈ 10.1k and PC9L ≈ 11.9k.**
5. NSO as stated (curvature-bound quadratic): 0 %. A wider split choice (PFK 16): worse.

**The target ≲ 8–9k is NOT reached by any combination measured here.** The best estimate is t570 ≈ 10.1k, still 1.1–1.3× over.

**Measured cause:** the leaf test is an LP relaxation. Its value is capped by the convex envelope of a w whose lobes are as wide as
the term ranges (96–98 % mixed curvature), so the certificate keeps about 11 % of the true slack. Minorant improvements are bounded by
that envelope, which the ALL run reaches at −14 %.

**What would move it** (not measured):
- a leaf test with internal case analysis over w's lobes: a piecewise or disjunctive minorant inside one walk node, which trades walk
  bits for kernel time;
- fewer walk bits per leaf (am-cert's encoding track, entropy floor 79–154 bits/leaf against 286).

**Bytes at about 10k leaves:**
- PC9L's non-walk part is ≈ 0.62 MB: Data 1.73 MB minus 1.26 MB of walk, plus Inst 0.14 MB.
- Of the ≈ 1.19 MB the certificate may take, that leaves ≈ 0.57 MB of hex walk, about 2.3 Mbit, or ≈ 230 bits/leaf. Today's walk
  runs at 286.
- So the byte target is a 1.25× payload compression. That is an encoding target, and memory (≈ 0.35 MB/leaf) still binds at 10k.

## 2. Round 2 (lead's decision 10-10 evening): the build engine, honestly sized; the lobe-case test

### Pre-registration (written before any run of this round)

**Answers to the lead's questions, from the source:**
- **ALL used LPACCEPT=1 (ideal rounding) and included SEP** (SO + V + C + SEP).
  - The realistic figure applies the measured real-to-ideal rounding ratio, 3,274/3,143 = 1.042: 2,695 × 1.042 ≈ **2,808 (−29 %)**,
    so t570 ≈ 10.6k. This confirms the lead's estimate.
- **Rank-1 quantisation is GENERATOR-SIDE ONLY. No checker change is needed.**
  - The Lean leaf decoder `dec4F lb …` reads λ in `lb` bits and scales it by 2^(10 − lb). The kernel's scale is already 1024.
  - The multiplier list `ydec … qb …` reads Yq in `qb` bits.
  - SIG is an Inst `def`, (1024·U1·SA) >> SIGSH.
  - The generators must change in these places:
    - emit: SIGSH param = YFRAC, not a hard-coded 14;
    - make…C `leafend`: λ width from `LB`, Yq width from `QB`, not hard-coded 8 / 12;
    - genpcellQ: env SIGSH=16; LB already comes from the data.
  - The full-tree run checks that QB = 12 still fits (subset: YW = 12).
  - These edits go into new copies `emit9q.py` / `make9qC.py`, after this sizing.

**Task 1, full-tree t570 on the build engine** (λ 10 bits, quantum 2⁻¹⁶, exact validity V, normal leaf test with meval, no
LPACCEPT; dump `dump_full_t570_qv.pkl`):
- Prediction: 11.0k–12.2k leaves.
  - Basis: −17.4 % from quantisation; V adds −4…−7 % on the real engine (−5.7 % under LPACCEPT); 14,906 × (0.78–0.82).
- Sizer bits/leaf ≈ 310–320. Its accounting already budgets 10-bit λ, so the emitted 6-bit-axis layout comes out ≈ 6 % lower:
  ≈ 292–300.
- Walk ≈ 0.80–0.90 MB hex.

**Task 2, lobe-case leaf test** (subset roots 2/5/9, the same build engine, LOBE = k ≤ 3; split adjacent ranges at w's inflection
nearest the midpoint):
- Baseline: the same engine without LOBE (subset QV).
- Prediction for LOBE = 3 against QV:
  - leaves −8 to −18 %;
  - bits/leaf +40 to +120 %, since every case carries a full payload;
  - kernel checks per leaf 1.5–3 (each case is a leaf check);
  - so walk bytes are WORSE (+10 to +60 %) and kernel time per surviving leaf roughly ×1.5–3.
- **Expected verdict: NOT a net lever under the time-and-bytes budget.**

### Results, round 2 (19:45)

**Task 1: full-tree t570 on the build engine** (`size9_full_t570_qv.log`, dump `dump_full_t570_qv.pkl`; 4,523 s, sizer peak
12.6 GB):
- **10,452 leaves** (10,122 M + 330 reflected), against 14,906 on the normal engine: **−29.9 %**. Per root it is −22 to −43 %.
- **3,285 points.** Tables: w 1,984 cells; derivative table **0 cells**, because exact validity reads no derivative table; lever 1's
  precertified intervals replace it.
- Emit (`emit9q.py`, QB = 13 because the multipliers need 13 bits): replay 0 failures. **Walk 3,278,324 bits = 313.7 bits/leaf =
  819.6 KB hex.**
- **Modules** (`root_PC9Q/`, bytes-only generation): **PC9QData.lean 1,163,040 B + PC9QInst.lean 141,262 B = 1.304 MB raw.** PC9L was
  1.873 MB. Lever 1's interval table adds ≈ +35–40 KB.
- **Point-table range:** 40 of the 3,285 tangent points lie at pair distance ≥ 16 units (max 59.8). Exact validity accepts tangents
  that far out; the Lean point table (`assert x < 524288`) covers < 16. The lever-1 build must either extend the table or cap tangent
  positions below 16 in the sizer, at a small leaf cost not measured here. The bytes above used PTMAX = 2²¹.
- **Prediction (11.0–12.2k): MISSED, low.** The engine did better than predicted. Bits/leaf landed at 313.7 against the predicted
  292–300 emitted, because the 13-bit Yq and 10-bit λ are wider. Walk 0.82 MB, inside the predicted 0.80–0.90.

**Task 2: lobe-case leaf test** (`cfx/t570_QV.log`, `cfx/t570_QVL3.log`, subset roots 2/5/9, the build engine):

| | leaves | walk bits (sizer) | bits/leaf | kernel checks/leaf | LP solves/leaf (sizing) |
|---|---|---|---|---|---|
| QV | 3,068 | 971,092 | 316.5 | 1.00 | — |
| QV + LOBE = 3 | 2,660 (−13.3 %) | 1,593,668 (+64 %) | 599 | 1.87 | 7.0 |

- 346 lobe leaves; 6,823 cases tried.
- Kernel checks rise from 3,068 to 4,974 (+62 %).
- **Verdict: NOT a net lever. Bytes +64 % and kernel time +62 % to save 13 % of leaves.**
- **Predictions HELD:** leaves −13 % (predicted −8…−18), bits/leaf +89 % (+40…+120), checks 1.87 (1.5–3). Bytes +64 % came in just above
  the predicted +10…+60.
- A first QVL3 run had an LP-point bug: a failed case overwrote the cell's LP point used by the split choice. It was fixed and rerun;
  the bad log is kept as `t570_QVL3_LASTXBUG.log`.

**Budget reading for t570 on the build engine (10,452 leaves):**
- **Time:** the lead's model gives 1,659 + 0.253 × 10,452 × 0.58 ≈ **3,190 board-s**. That is over the 2,600 soft rule and 50 s under
  the 3,240 hard limit.
- **Bytes:** 1.30–1.34 MB raw against ≈ 1.19 MB available, ≈ 1.1× over.
- **Memory:** ≈ 0.35 MB/leaf → ≈ +3.7 GB over the import, so still over 8 GB.
- **The structural far-field lever** (window-scope's box-restricted decoupling, run on this dump) has to provide the rest. The target
  is ≈ 6–7.5k leaves.

## 3. Round 3 (lead 10-10 ~20:00): the tangent cap; end-gap recursion in the real sizer

### Pre-registration (written before any run of this round)

**Task 1: tangent-position cap.**
- Run: QV with tangent positions p < 2¹⁹ (16 units; `size9so.py` TCAP=524288), subset roots 2/5/9. Baseline QV 3,068 leaves.
- Prediction: +0 to +1 % leaves, bits/leaf unchanged within ±1 %. Only 40 of 3,285 points lie beyond 16 units, and w there is ≤ 1e-3.
- Rule (lead): ≤ 1 % → cap, and am-cert does not extend the table.

**Task 2: end-gap recursion, sizing only.** By the reflection the certificate covers g_0 ≤ g_7, so one end suffices: decouple point 8
when g_7 ≥ g*.
- F ≥ b_7·g* + F_L(g_0..g_6), where F_L is the 8-point sub-frame on points 0..7. The cross pairs (i, 8) are dropped (≥ 0).
- **Main tree:** each root box is capped at g_7 < g* (`size9so.py` EGCAP), on the QV engine, subset 2/5/9.
- **Sub-certificate:** F_L ≥ cN − b_7·g*, as a FULL-domain 8-point certificate. It is not mirror-symmetric (points 0..7 of a weight
  vector symmetric about 4), so it runs with NOREFL, on the QV engine. One sub-certificate serves every root and both ends: by the
  reflection only g_7 ≥ g* is needed, and its domain contains the union of the projections.

**Pencil feasibility.** window-scope's T2 sub-frame minimum, the right part of r = 0, is ≈ 0.00778, so mine is ≈ 0.00778 by
symmetry. The sub-certificate needs min F_L ≥ cN − b_7·g* = 0.0085638 − 0.0002713·g*. **⇒ g* ≥ ≈ 2.9.**
- g* ∈ {1.5, 2.0, 2.5} are INFEASIBLE in this one-split form: the sub-frame inequality is false, so no certificate exists.
- So the sweep becomes g* ∈ {3.0, 3.5, 4.0}. `subframe9.py` re-measures the minimum and the margins first.

**Predictions:**
- Main-tree subset: −35 to −55 % at g* = 3.0; −25 to −45 % at g* = 4.0.
- Sub-certificate: 5k–9k leaves. It is a full 8-point NOREFL certificate whose margin is only 0.4 % to 4 %.
- **Net, with the full main tree at subset × 3.41 (the QV calibration, 10,452/3,068) plus the sub-certificate once: between −10 % and
  +15 % against 10,452. So NOT a clear win.** The ideal −71 % assumes free sub-certificates; here the sub-certificate is a whole
  8-point certificate.

### Results, round 3 (21:45)

**Task 1: tangent cap p < 16 units** (`cfx/t570_QVT.log`):
- 3,120 leaves against QV's 3,068: **+1.7 %**. Per root 889 / 1,083 / 1,148 against 856 / 1,071 / 1,141.
- Bits/leaf 315.9 against 316.5; walk bits +1.5 %.
- **Above the 1 % bar**, so by the rule am-cert should extend the point table (40 points) rather than cap.
- Prediction (+0…+1 %): MISSED, the cap costs more than predicted.

**Task 2: end-gap recursion, one top-level split at g*** (`subframe9.py`, `cfx/t570_QVE*.log`, `size_sub_t570_g*.log`):

**Feasibility, measured:** the left sub-frame (points 0..7) has global min F_L = 0.0077795. The sub-certificate needs
F_L ≥ cN − b_7·g*. The margin min F_L / cN_L − 1 at each g*:

| g* | 1.5 | 2.0 | 2.5 | 3.0 | 3.5 | 4.0 |
|---|---|---|---|---|---|---|
| margin | −4.63 % | −3.01 % | −1.34 % | +0.38 % | +2.17 % | +4.02 % |
| verdict | INFEASIBLE | INFEASIBLE | INFEASIBLE | feasible | feasible | feasible |

At g* < 2.9 the sub-frame inequality is false, so no single sub-certificate can exist (pencil held).

**Main tree (subset, with the tangent cap) and sub-certificate (full-domain 8-point, NOREFL, build engine):**

| g* | main subset | vs tangent-cap baseline 3,120 | sub-cert leaves (once) | sub-cert walk bits | est. full total (main × 3.407 + sub) | vs 10,629 (cap baseline, full) |
|---|---|---|---|---|---|---|
| 3.0 | 2,912 | −6.7 % | 2,422 | 643,913 | 12,343 | **+16 %** |
| 3.5 | 3,025 | −3.0 % | 1,801 | 467,827 | 12,107 | **+14 %** |
| 4.0 | 2,980 | −4.5 % | 1,730 | 434,468 | 11,883 | **+12 %** |

- Walk bits rise +8 to +12 % in the same way. Kernel checks rise in proportion to leaves.
- **Verdict: NET WORSE (+12 to +16 %).** End-gap recursion in the one-split form is not a lever.

**Why** (`dump_full_t570_qv.pkl`, leaf boxes):
- Only **4.7 %** of the build-engine leaves lie wholly at g_7 ≥ 3; it is 2.5 % at ≥ 3.5 and 1.4 % at ≥ 4.
- Long gaps are mostly MIDDLE gaps. A middle gap has lower bound ≥ 2.0 in 57.5 % of leaves and ≥ 2.5 in 36 %.
- Middle-gap decoupling with GLOBAL sub-frame minima needs g ≳ 4.6 (window-scope's T2), where only 2.1 % of leaves lie.
- So the ideal −71 % must come from BOX-RESTRICTED sub-frame minima deep in the tree: window-scope's round 11, the recursive form
  that is held.

**Scoring:**
- Feasibility pencil: HELD.
- Main −35…−55 %: REFUTED (−3…−7 %).
- Sub-certificate 5–9k: REFUTED, it is cheaper at 1.7–2.4k.
- Net −10…+15 %: at the top end and slightly beyond (+12…+16 %).

**Lean consequences, had it been a win** (noted as the lead asked):
- an OpethN-generic n = 8 sub-frame certificate theorem on points 0..7 with its own floor cN_L. NOREFL, so the PgL statement form;
- a combination lemma: for g_7 ≥ g*, F(g) ≥ b_7·g* + F_L(g_0..g_6) (cross pairs dropped as w ≥ 0), plus the top-level split.

**Decision note (lead, 10-10 ~22:00):** tangent positions are CAPPED at the Lean convex-region limit **p < 507,904**, about 15.5
units, not 16.
- Read at source by am-cert, PCDZ.lean:43–61: `tcheckZC` needs a region k = (p + 16384) >> 15 < 16, and lever 1's `ivOk` has the
  same limit. So the 40 far points were never certifiable; PTMAX = 2²¹ was bytes-only.
- `cfx9.sh` and `full9.sh` now default to TCAP = 507904 with the `size9so.py` sizer whenever EXACTV = 1.
- The 10,629 full-tree figure used the 16-unit cap (TCAP = 524288). It is to be re-sized at 15.5 when the full tree is next touched.

## 4. Round 4 (10-11, resumed): the QV full tree at the region cap; real emission

### Pre-registration (written before the run)

**Re-size** t570 on QV + TCAP = 507,904 (the region limit), full tree, dump `dump_full_t570_qvt.pkl`.
- Prediction: 10.50k–10.80k leaves (the subset said +1.7 % at the 16-unit cap; 10,452 × 1.017 ≈ 10,630).
- Bits/leaf 313–316.
- Points 3,200–3,300: the ≥ 15.5-unit tangents vanish, and the rest are reused.

### Correction (09:20): the QV tree is not lever-1 emittable; the realizable engine is Q

- I replayed `dump_full_t570_qv.pkl` through the emit with EXACTV off, i.e. with the table-based tcheck that Lean's `ptlOkI` /
  `tcheckZC` use. **5,551 of 10,452 leaves FAIL** (`tvtest/`).
- Lever 1 certifies each point's interval with that same table check, once per point. So it is a kernel-TIME lever. V (exact
  validity) is not realizable by it.
- The realizable engine is Q (λ 10 bits + quantum 2⁻¹⁶, table check): subset 3,274 ⇒ full ≈ 12.3k.
- The lead has retired the 10,452 baseline. The QVT re-size was stopped (`size9_full_t570_qvt_STOPPED.log`).

### Step 1 pre-registration: why exactly-valid tangents fail the table check

**Method:** `size9so.py` DIAGT=1. On the QV subset sizing (EXACTV, TCAP 507904), every used tangent range (p, L, U), and every
point's hull, goes through the FAITHFUL table check (tchk's non-EXACTV path) on the built tables, at ZN ∈ {8, 16, 32, 64, 128}. It
reports the first failing stage: region / outside / deriv / right extension / left extension.
- Run A: tables as sized (DLO 7, DHI 8, WMIN 8).
- Run B: finer derivative and pyramid tables (DLO 9, DHI 10, WMIN 10).

**Prediction:**
- At ZN = 8, 75–90 % of used ranges pass, and point hulls pass less.
- Most failures are right/left extension, which ZN fixes: at ZN = 64, ≥ 95 % of ranges pass.
- A residue of 1–5 % at 'outside' or 'region' that ZN cannot fix. That residue is where the per-point subdivided check (k stored
  sub-ranges) would apply.
- Finer tables (B) add a few points at each ZN.

### Step 2 pre-registration: faithful lever-1 sizings (table check, no EXACTV)

**Runs** (subset 2/5/9, Q engine LSC 1024 / YFRAC 16, TCAP n/a since the table check already needs the region):
- ZEXT ∈ {16, 32, 64}; baseline Q at ZEXT 8 = 3,274 (`cfx/t570_L10Y16.log`).
- Finer tables (DLO 9, DHI 10, WMIN 10) at ZEXT 8 and 32.

**Cost per setting:**
- leaves and walk bits;
- table cells (w / d) and points, which set the bytes;
- one-time kernel cost ∝ points × ZN, for the per-point interval checks.

**Prediction:**
- ZEXT 16: −2 to −4 %; ZEXT 32: −3 to −6 %; ZEXT 64: −4 to −7 % (QV's −6.3 % is the exact-validity limit).
- Finer tables add a further −1 to −2 %, at +20–60 % table cells.

### Step 1 and step 2 interim results (10:35)

**Step 1, DIAGT on the QV@15.5 subset tree** (`cfx/t570_DIAGA.log`: 3,178 leaves; the EXACTV sizing at TCAP 507,904).
- **Used tangent ranges** (30,319), faithful table check:

| ZN | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| pass | 93.9 % | 95.6 % | 96.1 % | 96.3 % | 96.4 % |

- **Every failure is an extension** (left / right). There are no region, outside or deriv failures (TCAP).
- **Residue ≈ 3.6 %**, which ZN cannot fix. It is set by the table resolution of the extension reads, not by the piece count.
- **Point hulls** pass at 76.6 % (ZN 8) to 81.0 % (ZN 128). Every failing hull contains a failing range.
- **Pencil:** the table check's right side depends only on (p, U) and its left side only on (p, L). So in a tree sized with the
  faithful per-range check, every hull [min L, max U] passes automatically: each side is the side of one passing range. That is
  why PC9L's hulls all passed.
  - **⇒ the per-point subdivided check (k sub-ranges) is NOT needed** for a table-faithful tree.
  - It also would not rescue the EXACTV ranges, whose own sides fail.
- **Run B MISLABELLED:** DLO 9 / DHI 10 / WMIN 10 are COARSER tables (the finest level is 2^level units: 496 w cells against 1,984).
  B's lower pass rates (85.6 % of ranges) show the coarse-table effect.

**Step 2, faithful sizings** (the table check; subset 2/5/9; Q engine):

| setting | leaves | vs Q 3,274 | walk bits | w / d cells | points |
|---|---|---|---|---|---|
| Q, ZEXT 8 (`t570_L10Y16`) | 3,274 | — | 1,025,025 | 1,984 / 2,240 | — |
| ZEXT 16 | 3,223 | −1.6 % | 1,006,617 | 1,984 / 2,240 | 2,240 |
| ZEXT 32 | 3,188 | −2.6 % | 1,002,409 | 1,984 / 2,240 | 2,255 |
| ZEXT 64 | (running) | | | | |
| coarser tables, ZEXT 8 (mislabelled "F") | 3,147 | −3.9 % | 983,540 | 496 / 560 | 2,114 |
| coarser tables, ZEXT 32 | 3,211 | −1.9 % | 1,001,202 | 496 / 560 | 2,161 |
| reference: QV@15.5 (exact validity, unrealizable) | 3,178 | −2.9 % | 1,000,034 | — | 2,288 |

- **The whole validity lever is worth ≤ ≈ 3 % at the region cap.** QV@15.5 is −2.9 %.
- Faithful ZEXT 32 (−2.6 %) already reaches it, at a one-time cost of ≈ 4× (ZN 32 / 8) per point check, ≈ 2.3k points on the subset.
- **Noise caveat:** between nearly-equivalent engines, single roots swing by up to ±20 % (the coarser-table ZEXT 8 run has root 5 at
  +18 % and root 9 at −24 % against Q). Subset totals of ≈ 3k leaves therefore carry about ±3–4 % split-order noise.
  - The lever differences in this table, and the 2–4 % levers of §1 (C, SEP, SO), are at or below that noise.

### Step 3 pre-registration: full tree on the faithful engine

**Setting:** Q (λ 10 bits, quantum 2⁻¹⁶), table check, ZEXT 32, standard tables, no EXACTV, no TCAP needed. Dump
`dump_full_t570_qz32.pkl`.
- ZEXT 32 matches the exact-validity limit within noise, at half ZEXT 64's per-point cost.
- A finer-table run (DLO 6 / DHI 7 / WMIN 7) goes in parallel, to see whether it adds anything.

**Prediction:** 11.6k–12.4k leaves (≈ 14,906 × 3,188/3,966 ≈ 11,980).
- Bits/leaf ≈ 313; walk ≈ 0.91–0.97 MB hex.

**Then:**
1. emit9q (QB 13, SIGSH 16);
2. lever1_ivs.py must verify every hull (pencil: all pass);
3. make9qI + genpcellQI (WIN 512; CHB, CHL as agreed with am-cert);
4. Lean build under the lock with `set_option Elab.async false`; axioms; bytes; footprint; walk-only nanoda via stage_bench.sh.

### Step 2 final and step 3 results (11:30)

**Step 2, final rows:**
- ZEXT 64: 3,179 (−2.9 %; 2,260 points). It equals QV@15.5, the exact-validity ceiling.
- Genuinely finer tables (DLO 6 / DHI 7 / WMIN 7, ZEXT 32): 3,282 (+3 % against ZEXT 32's 3,188) at 2× table cells. **No help.**

**Step 3: PC9Q, the real emission of the faithful tree.**
- **Tree:** `dump_full_t570_qz32.pkl` (Q engine, table check, ZEXT 32).
  - **11,078 leaves** (10,735 M + 343 reflected); 3,190 points.
  - Walk **3,435,015 bits = 310.1 bits/leaf = 858.8 KB hex**.
  - Sizing 3,786 s at 4.5 GB peak. Prediction 11.6–12.4k: MISSED, low.
- **Verification:**
  - the emit replay (`emit9q.py`) gave 0 failures;
  - the **independent replay (`arun/lever1_ivs.py` on `verify8pz.py`) passed every walk, and all 3,190 point hulls pass tcheck**
    (`IV_PC9Q.json`). The hull pencil is confirmed.
- **Modules** (`gen9qi.sh`: `make9qI.py` + `genpcellQI.py`; CHB 100000, CHL 1, WIN 512, CSH 4, ZN 32, QB 13, SIGSH 16, LB 10;
  `set_option Elab.async false` after the imports):
  - PC9QData.lean 1,676,292 B; PC9QInst.lean 145,610 B; **1.82 MB raw**.
  - Data composition: walk literals 863 KB (52 %), point table with intervals ≈ 245 KB, chunk-boundary state literals ≈ 233 KB
    (198 boundaries; removable with am-cert's compact boundaries), w/d tables ≈ 187 KB, chunk theorems ≈ 89 KB.
- **Lean** (`lean_PC9Q.log`, under the lock, LEAN_NUM_THREADS 2, `leanc2.sh`):
  - Inst: 58 s, peak footprint 1.68 GB.
  - **Data: 262 s, peak footprint 2.65 GB.**
  - No errors.
  - **`AMW.Cert.PC9Q_cert_full` depends on [propext, Classical.choice, Quot.sound].**
- **Walk-only nanoda** (`nanoda_PC9Q.log`; stage_bench.sh with TARGETS = AMW.Cert.PC9Q_cert_full):
  - export 42 s (308 MB, footprint 1.36 GB);
  - **nanoda 211 s (footprint 2.93 GB)**;
  - Lean full-closure replay 266 s (48,560 constants, footprint 1.38 GB);
  - all exit 0.
- **Budget:**
  - bytes ≈ 1.82 MB raw, ≈ 1.59 MB with compact boundaries, against ≈ 1.19 MB;
  - time (lead's model) ≈ 1,659 + 0.253 × 11,078 × 0.58 ≈ 3,285 board-s.
  - **The pipeline is proven end to end; the certificate is not an upload candidate.**

### Round 4b (lead 10-11 ~11:20): PC9QB with limb walks; INT9Q end to end

**PC9QB** (`root_PC9QB/`): the same tree and IVs as PC9Q.
- Generators: `make9qIL.py` (am-cert's 10:30 make9pcI.py + JB/LB/QB) and am-cert's genpcellQI.py (10:30). Settings: LIMB 16384,
  WIN 512, ZN 32, CSH 4, SIGSH 16, QB 13, no CHB/CHL. `set_option Elab.async false` after the imports.
- Bytes: Data 1,408,753 + Inst 145,876 = **1.555 MB**. PC9Q chunked was 1.822 MB.
- `PC9QB_cert_full` → standard axioms.

| stage | time | instructions | peak footprint |
|---|---|---|---|
| Lean build, Inst | 45 s | 4.09e11 | 1.68 GB |
| Lean build, Data | 243 s | 1.663e12 | 5.09 GB |
| walk-only export | 46 s | 1.96e11 | — |
| walk-only nanoda | 203 s | 1.560e12 | 6.40 GB |
| walk-only Lean replay | 244 s | 1.706e12 | 3.98 GB |

- Against chunked PC9Q: nanoda −13.7 % and replay −9.2 % in instructions. **Peak memory ×2–3**, since each root walk is one theorem.

**INT9Q** (`arun/int9q.sh` = int9.sh with PC9QB):
- **Assembly:** swap_cert9 into MOPX9_full.lean; PCBias and **PCellIV** (the lever-1 engine module) inserted before the certificate
  region.
- **INT9Q.lean = 2,473,842 B raw.** κ = 66780167/99143618 = 0.6735700023.
- **Private check** against record 167031227639218487/247987190000000000: **BUILD EXIT 0, standard axioms on all three theorems,
  REPLAY EXIT 0.**

| stage | time | instructions | peak footprint |
|---|---|---|---|
| build | 481 s | 3.884e12 | 7.09 GB |
| kernel replay (6,858 constants) | 257 s | 1.795e12 | 6.03 GB |
| export (674 MB) | 44 s | 0.339e12 | 1.61 GB |
| nanoda | 266 s | 1.881e12 | 6.45 GB |
| closure replay (76,791 constants) | 312 s | 2.207e12 | 4.24 GB |

- Against INT9 (PC9L, 10-10): build −40 %, replay −42 %, export −46 %, nanoda −74 %, closure −35 % in instructions. **Total
  10.1e12 against 20.9e12.**
- **Board, per am-cert's per-stage weights** (0.289 s / 1e9 build; 0.356 s / 1e9 export + nanoda + closure):
  1,122 + 121 + 670 + 786 ≈ **2,700 s**, without the private-check replay stage (+639 s if the board pays it at 0.356).
- **Lead's per-leaf model:** 1,659 + 0.110 × 11,078 ≈ 2,880 s.
- **Bytes:** 2.47 MB against the 2.0 MB cap, **≈ 0.47 MB over**. The base (MOPX9_full minus its certificate) is ≈ 0.9 MB unstripped.

**INT9Q memory, explicit:** full-closure nanoda peak 6.45 GB, below the lead's 7.0 GB bar, so no root split is needed. The highest
stage is the build, at 7.09 GB.

**ZN 32 point-check cost** (`rt_PC9QB.tsv`, ReplayTimes on PC9QBData.olean; 196.4 s total kernel replay):

| part | kernel replay | share |
|---|---|---|
| walk theorems | 162.1 s | 82.5 % |
| PTL_*_ok, 3,190 points | 20.4 s | 10.4 % |
| w/d table checks | 12.1 s | 6.2 % |

- Per point: 6.4 ms at ZN 32, against 4.7 ms at ZN 8 (am-cert's PC9LI), i.e. ≈ +5 kernel-s ≈ +30 board-s at this point count.
- A per-point ZN is not worth building.

## 5. Root promotion (lead 10-11 ~12:40): cap the largest walk near 650 leaves

**Data-driven? YES. No Lean change is needed.**
- The LIMB instance (genpcellQI, 10:30) already states `walkC` and `covered_of_walkCP` over `bits : ℕ → ℕ`, and has the compact
  boundary lemmas `chA` / `chB` / `gsplitc_to` / `ssplitc_to` and `tm_to`.
- Only the data generator forbade LIMB with CHB. The new copy `make9qIP.py` lifts that: a subtree above CHB bits splits at its own
  cut, CHE compact children, and every piece runs `walkC` on the root's own limb function `WD{n}` from its absolute bit position.
  There is no new literal; there is one root closed-state def per promoted root.
- The per-gap root cover (COV / rootCl / `run`) is unchanged: a promoted root is still one `rc{n}` theorem, proved through `tm_to`
  plus the split.

### Pre-registration

**Run:** PC9QB2 = PC9QB's tree and IVs with LIMB 16384, WIN 512, CHB 201500 (≈ 650 leaves × 310 bits), CHE 1, no CHL. Eight roots
exceed it (1, 2, 3, 4, 5, 6, 9, 10).

**Predictions:**
- Largest walk ≤ ≈ 650 leaves.
- Data bytes +5–15 KB (≈ 8–12 boundaries).
- Cert-only Data build peak 5.09 → ≈ 3.2–3.8 GB.
- Walk-only nanoda peak 6.40 → ≈ 3.9–4.6 GB (am-cert's slopes 3.3 / 4.3 MB per leaf of the largest walk).
- Instructions within ±5 % of PC9QB.

### Results, root promotion with compact boundaries (PC9QB2, finished 13:08)

| | PC9QB (limb, 16 walks) | PC9QB2 (promoted, CHE) | change |
|---|---|---|---|
| largest walk | 1,170 leaves (root 9, exact from the dump) | ≈ 632 leaves | — |
| boundaries / pieces | 0 / 16 | 96 / 208 | — |
| Data bytes | 1,408,753 | 1,451,534 | +42.8 KB |
| Data build: peak footprint | 5.09 GB | **3.49 GB** | −1.60 GB |
| Data build: instructions | 1.663e12 | 2.140e12 | **+28.7 %** |
| Data build: time | 243 s | 295 s | — |
| walk-only nanoda: peak | 6.40 GB | **4.87 GB** | −1.53 GB |
| walk-only nanoda: instructions | 1.560e12 | 1.889e12 | **+21.1 %** |
| walk-only closure replay: peak | 3.98 GB | 2.41 GB | — |
| walk-only closure replay: instructions | 1.706e12 | 2.116e12 | **+24.0 %** |

- Axioms: standard.
- **Memory targets MET:** build 3.49 GB, inside the predicted 3.2–3.8; nanoda 4.87 GB, slightly above the predicted 3.9–4.6.
- **Instructions REFUTED** (predicted ±5 %). The 96 compact boundaries chain `chA` / `cuB` about 12 deep, and every piece's
  `decide +kernel` re-evaluates its chain from the root literal.
- Converted with the calibrated weights (build +52 s ×2, nanoda +37 s and replay +81 s ×2.46), that is ≈ +390 board-s, which would push INT9Q (≈ 2,920 s) over the 3,240 hard limit.

**Next, pre-registered: PC9QB3**, the same cut set with LITERAL child states (CHE off: `gsplitq_to` with `rfl`). Each boundary is
checked once against its parent literal, so there is no chain.
- Predictions: Data bytes +100–130 KB over PC9QB (192 state literals of ≈ 600 B); instructions within +3…+10 % of PC9QB; peaks as
  in PC9QB2.

**Decision rule for PC9QB3**, added after launch but before any result:
- Per-walk kernel time in PC9QB (rt_PC9QB.tsv, 16 walks) fits t = 0.25 s + 14.3 ms/leaf. Small walks run at 15.9–16.5 ms/leaf,
  so the intercept is real.
- Two readings of the PC9QB2 excess:
  - (i) chain re-evaluation, which literal states remove;
  - (ii) a fixed cost per piece (≈ 0.25 s × 192 extra pieces ≈ +48 kernel-s ≈ +25 %), which they do not.
- In PC9QB the intercept includes the root-only `tm` box closure, which pieces do not pay. So the prediction stays at (i).
- Rule:
  - PC9QB3 instructions ≤ +12 % over PC9QB: (i) holds.
  - PC9QB3 instructions ≥ +18 %: (ii) holds. The piece count is the lever, and that piece count is forced by the subtree-only
    cut at a given CHB, since every node with more than CHB bits must be a boundary.
  - Between +12 % and +18 %: mixed.

## 6. Finer root partition, no boundaries (lead 10-11 ~13:15, option (d))

**Data-driven?**
- **Lean: YES.**
  - `COV` is a data def: per gap, a list of `(l, u, clear)`.
  - `cert_of` checks it with `coverChk` (contiguity, and the cleared pieces clear).
  - `run` is generated over the product of the `false` (bad) intervals, so one more `false` entry in a gap is one more region
    axis. No Lean change is needed.
- **Sizer: YES, with a one-line hook.** It builds `bads` from `phase1` and the roots as their product. `size9pr.py` / `run9pr.py`
  add `RCUT="g:m"`, which splits gap g's bad interval at m.

**Constraint: the roots are a PRODUCT.**
- Roots 9, 5, 10 and 4 are (i2, i3, i4, i5) = 1001, 0101, 1010, 0100, so they share no single gap-2..5 interval.
- A cut that halves all four therefore has to be on gap 0, 1, 6 or 7, which doubles every root (16 → 32).

**Measured on the QZ32 tree** (`rootcut9.py`):
- The leaves are cut by PAIR SUMS, not gaps. On every gap axis most leaves' closed boxes straddle any interior cut.
- Best cut per axis (straddling leaves of 11,078, and the largest side, which includes the straddlers):

| gap | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| straddle | 8,864 | 6,624 | 1,783 | 5,605 | 5,799 | 2,619 | 6,896 | 7,843 |
| largest side | 1,034 | 990 | 1,120 | 1,151 | 1,150 | 1,079 | 1,027 | 968 |

- For example, gap 1 cut at 51,168 splits root 9 as 180 below / 181 above / 809 straddling.
- The trees also start with about 10 one-leaf peels (root 9: 1,169/1, 1,168/1, …), which is why the CHB boundaries chain.

**Test, sizing only.** Root 9's two halves under `RCUT=1:51168` (ROOTSEL 9, 25), with the same engine as QZ32. In parallel, a control:
root 9 alone, unsplit (ROOTSEL 9, run9pz). This separates the cut's effect from subset noise (single roots swing ±20 %).

**Prediction:**
- Halves combined 1,500–2,000 leaves, against the control's ≈ 1,170.
- The larger half ≥ 800.

**Decision rule:**
- Combined ≤ 1.05 × control and both halves ≤ 650: (d) is viable; run the full re-size.
- Otherwise (d) is retired for this tree (a gap-axis region cut does not halve sum-organised trees), and (b) goes ahead.

### Test result (13:30): the prediction is REFUTED, in the favourable direction

| run | leaves | time |
|---|---|---|
| control: root 9 unsplit (`cfx/t570_R9ctl.log`) | **1,170** (identical to the full run, so root sizing is deterministic and independent of the other roots) | 435 s |
| `RCUT=1:51168`, lower half (root 9) | **649** | — |
| `RCUT=1:51168`, upper half (root 25) | **320** | — |
| `RCUT=1:51168`, combined (`cfx/t570_RCUT1.log`) | **969 = −17.2 %** | 367 s |

- I predicted 1,500–2,000 combined and a larger half ≥ 800. Both halves are ≤ 650.
- **Decision rule: (d) VIABLE.**
- **What refuted the prediction:** the straddle count of the existing leaves is not a predictor. In a half box the sizer builds a
  different, smaller tree. A plausible cause, untested, is that the closure of a narrower root box gives tighter pair-sum bounds.
  The 10 one-leaf peels at the top of root 9 do not reappear in the same form.

### Full re-size pre-registration (PZ32R1)

**Run:** all roots under `RCUT=1:51168`, i.e. 32 roots; the same engine as QZ32 (run9pr.py; LSC 1024, YFRAC 16, ZEXT 32); dump
`dump_full_t570_qz32r1.pkl`.

**Predictions:**
- Total 9.6k–11.4k leaves, against 11,078 (root 9's −17 % will not hold uniformly, and the small roots gain from their split).
- Largest root ≤ 720.
- Walk bits within ±12 % of 3.435 Mbit.
- 32 roots × root overhead (≈ 0.25 kernel-s each) ≈ +4 kernel-s.

**Decision rule:**
- Total ≤ 11,078 and every root ≤ 650: emit PC9QB4.
- A root > 650: report it, and emit anyway if it is ≤ 720.
- Total > 11,400: hold and report.

## 7. Root-granularity sweep (lead 10-11 ~13:35): root size as a LEAF lever

**First data from PZ32R1, in progress:**
- root 0 lower half: 53 leaves (old root 0: 270);
- root 1 lower half: 217 leaves (old root 1: 669).
- The upper halves come later, at indices 16–31.

**Configurations** (mirror-paired cuts, so the root set is reflection-symmetric):
- **PZ64:** `RCUT=1:51168,6:51168` (64 roots).
- **PZ64b:** `RCUT=0:52056,7:52056` (64 roots; 52,056 is the gap-0 scan's best cut, by the same logic as 1:51168).
- **Optional PZ128:** PZ64 plus the better of the gap-0/7 pair, if PZ64 is still dropping by ≥ 5 %.

**Subset first: old roots 2, 5, 9**, the calibrated subset (QZ32 subset = 898 + 1,120 + 1,170 = 3,188).
- PZ32: ROOTSEL 2,5,9,18,21,25, read from the PZ32R1 full run.
- PZ64 and PZ64b: ROOTSEL 4,5,10,11,18,19,36,37,42,43,50,51 (index = 32·i_a + 2·r + i_b).
- Two sizings in parallel on 12 cores (≈ 1.9 GB each).

**Per-root fixed overhead model, to be calibrated:**
- Bytes per root: COV entry, `wr`/`rc` theorems, the `run` match case, limb defs and dispatch, and a partial last limb.
- Time: ≈ 0.25 kernel-s per walk (the PC9QB intercept, which includes `tm`). That is ≈ 1.6 board-s per root with the calibrated
  weights (build ≈ replay, nanoda ≈ 0.83 replay, so 0.25 × (2 + 2.46 × 1.83)).
- Per leaf: 14.3 ms kernel ≈ 0.093 board-s, and ≈ 78 B of walk hex (≈ 127 B all-in).
- So one added root costs ≈ 17 leaves in time.

**Stop rule (lead):** stop when the marginal saving per doubling falls below the overhead per added root. Going 32 → 64 adds
32 roots ≈ 540 leaf-equivalents in time, so it needs ≥ ≈ 5 % of an ≈ 10k tree.

**Predictions:**
- PZ64 subset = 0.85–0.95 × the PZ32 subset.
- PZ64b similar, within ±5 % of PZ64.
- The largest root ≤ 500 in both.

**Per-root bytes, measured on PC9QB:**
- Root-specific text other than the walk's hex is ≈ 2.97 KB per root: two copies of the root-state literal (in `wcc`/`cc`), the
  theorems, `rc`/`run` cases and the limb dispatch.
- **Lever, PC9QBR** (`make9qIR.py`): make9qIL plus am-cert's RCOMP path (`rcOf` with the walk on `ofCl (RC i…) 0`, so no
  root-state literal), with LIMB support (`wb : ℕ → ℕ`, `WD{n}`). Same tree as PC9QB.
  - Data **1,373,688 B (−35.1 KB, −2.2 KB per root)**, measured.
  - The per-root fixed cost is now ≈ 0.8 KB: `rc` line, `run` case, limb dispatch and a partial limb.
- **Build pre-registration, PC9QBR** (queued with PC9QB3):
  - compiles with standard axioms;
  - Data build and walk-only instructions within ±2 % of PC9QB (`ofCl (RC …)` is a list lookup);
  - peaks as PC9QB (5.09 / 6.40 GB).
- Every root count in this sweep is costed on this layout.

### Sweep results, subset of old roots 2, 5, 9 (13:35–14:00)

| config | roots | subset leaves | against PZ32 | largest root on the subset | walk bits |
|---|---|---|---|---|---|
| QZ32 | 16 | 3,188 | — | 1,170 | — |
| PZ32 (gap 1; from PZ32R1) | 32 | 2,734 | — | 649 | — |
| PZ64 (gaps 1 + 6) | 64 | 2,688 | **−1.7 %** | 359 | 848,160 |
| PZ64b (gaps 0 + 7, no gap-1 cut) | 64 | 3,966 | **+45 %** (+24 % against QZ32) | 523 | 1,198,444 |

- **Predictions refuted:** PZ64 was predicted at 0.85–0.95 × PZ32 and came in at 0.983. PZ64b was predicted within ±5 % of PZ64
  and came in at +47.5 %.
- **The lever is the gap-1 cut, not root granularity as such.** A gap-0/7 cut makes trees larger.
- **Stop rule: STOP at 32 roots.**
  - 32 → 64 saves 1.7 % on the subset (≈ 170 leaves full-scale, inside the ±3–4 % subset noise).
  - 32 added roots cost ≈ 0.8 KB each in bytes, about 26 KB.
  - In time, the per-piece kernel cost from PC9QB3 (≈ 4.3e8 instructions ≈ 0.12 s per piece) gives ≈ 0.8 board-s per root,
    about 26 board-s ≈ 280 leaves.
  - Net zero or negative, so PZ128 is not run.

### PC9QB3 and PC9QBR builds (13:57–14:30)

| | PC9QB | PC9QB3 (literal boundaries) | PC9QBR (root layout without literals) |
|---|---|---|---|
| Data bytes | 1,408,753 | 1,558,713 | **1,373,688 (−35.1 KB)** |
| Data build instructions | 1.663e12 | 1.902e12 (+14.3 %) | 1.660e12 (−0.2 %) |
| Data build peak | 5.09 GB | 3.55 GB | 5.11 GB |
| walk-only nanoda | 1.560e12 / 6.40 GB | 1.648e12 (+5.7 %) / 4.20 GB | 1.572e12 (+0.8 %) / 6.46 GB |
| walk-only replay | 1.706e12 / 3.98 GB | 1.789e12 (+4.9 %) / 2.31 GB | 1.706e12 (0.0 %) / 3.99 GB |
| axioms | std | std | std |

- **PC9QB3, decision rule:** the kernel stages are +5–6 %, which is ≤ +12 %, so the chain reading (i) holds. The build is +14.3 %,
  in the mixed band; the extra is elaborator-side `rfl` on 192 literal equalities.
- **Per-piece fixed cost, calibrated:** +8.3e10 replay instructions for 192 extra pieces ≈ 4.3e8 per piece ≈ 0.12 kernel-s.
- **PC9QBR:** all three predictions held (std axioms, ±2 %, same peaks). Adopted as the root layout.

### PC9QB4 (lead 10-11 ~15:15): PZ32R1 with every adopted byte lever

**Inputs:**
- Tree PZ32R1: 10,077 leaves, 32 roots, largest root 784 (root 10).
- `emit9qr.py` (RCUT 1:51168): 0 verification failures, 3,154,179 walk bits.
- `lever1_ivs.py`: 3,262 points, all with an interval.
- L5 `dprune.py`: 135 of 496 derivative blocks kept (96 hulls need D); all 3,262 hulls pass on the pruned table.

**Data module** (`make9qIR.py` + the L2 point tree, ported verbatim from am-cert's make9pcI.py 12:36):
- ROOTC/RCOMP root layout; LIMB 32768; WIN 480 (longest leaf word ≤ 452 bits, from the dump); PTREE 3.
- Instance: genpcellQI with LIMB 32768, WIN 480, ZN 32, CSH 4, SIGSH 16, QB 13.
- **Data 1,109,370 B (−299 KB against PC9QB); Inst 145,870 B.** `Elab.async false` added by Edit.

**Pre-registration:**
- Standard axioms.
- Data build instructions 1.45–1.65e12. Leaves −9 %; limb reads over 33 kbit +3–10 %; dprune shifts the point checks to the
  zero-order extension, +10–60 % on a small share.
- Data build peak 3.5–4.5 GB (784-leaf walk), unless the point-tree check dominates. am-cert's PC9LP build peaked at 8.4 GB on
  larger walks.
- Walk-only nanoda peak 4.0–5.0 GB.

### INT9Q4 assembly (15:26) and pre-registration

- **Assembly:** `arun/int9q4.sh` (int9q.sh steps 1–4, with PCellPT inserted after PCBias and PCellIV) gives `INT9Q4_pre.lean`,
  2,178,618 B.
- **`INT9Q4.lean`** is a copy carrying the master-of-puppets2 window edits, made by hand with Edit (the UPLOAD_PC8R → PC8R2 diff,
  applied to the 9-point skeleton): Arun's circle-enclosure notice block; "and master-of-puppets2"; the change bullet;
  `cos_theta0_le`; `sin_theta0_ge` (circle enclosure); `floor_numeric`; `HW_ge` (672168410556873948/10¹⁸); the OpethN counting
  constant everywhere, with `hHW` through PC8R2's `calc`; the final instantiation; `candidateKappa`. 2,180,049 B.
- **Candidate κ** = (672168410556873948/10¹⁸ − 436674/10⁸)/(1 − 856382/10⁸) = **166950417639218487/247859045000000000 =
  0.6735700028**. That is +2.22e-5 over the master-of-puppets2 record 167031227639218487/247987190000000000 = 0.6735478056.
- **Pipeline:** `arun/int9q4b.sh`:
  1. private check of the unstripped file (specroot_int9q4);
  2. ReachQ4 (my copy of am-cert's ReachQ.lean);
  3. strip9.py with am-cert's keep.txt, giving INT9Q4S.lean;
  4. private check of INT9Q4S (specroot_int9q4s), then the stages.
- **Pre-registration:**
  - All three scored theorems on standard axioms.
  - Stripped bytes 1.96–2.00 MB (INT9Q's strip removed 200 KB).
  - Full-file build peak 5.5–6.2 GB (INT9Q 7.09; largest walk 1,170 → 784).
  - Build 420–500 s.
  - Calibrated board time 2,650–2,950 s (INT9Q ≈ 2,920).
  - If the strip build fails on a missing name, add it to keep.txt and rerun step 3 onwards (am-cert's procedure).

### PC9QB4 module build (15:24–15:48)

| | PC9QB | PC9QB4 | change |
|---|---|---|---|
| Inst | 4.09e11 / 1.68 GB | 4.10e11 / 1.68 GB / 47 s | — |
| Data instructions | 1.663e12 | **1.454e12** | **−12.6 %** (predicted 1.45–1.65e12: at the bottom of the range) |
| Data build peak | 5.09 GB | **3.67 GB** | predicted 3.5–4.5 GB: in range |
| Data build time | 243 s | 213 s | — |
| axioms | std | **std** | — |

Walk-only stages follow (`nanoda_PC9QB4.log`). The INT9Q4 pipeline (`int9q4b.sh`) is queued behind them.

**Walk code (window-scope r13, am-cert's decoder to follow):**
- On DATA_PC9QB4_dp, A+B+C re-encodes 3,154,179 → 2,335,720 bits: −205 KB of hex, ≈ −182 KB net after its tables.
- Maximum coded leaf lengths, to check against WIN 480: A 438, B 479, A+B 463, A+B+C 457.
- Scheduled as a separate re-emission after INT9Q4.

**PC9QB4 walk-only stages** (TARGETS `PC9QB4_cert_full`, the whole closure):

| stage | PC9QB | PC9QB4 |
|---|---|---|
| export | 1.96e11 | 1.88e11 / 1.36 GB |
| nanoda | 1.560e12 / 6.40 GB | **1.490e12 (−4.5 %) / 6.16 GB** |
| replay | 1.706e12 / 3.98 GB | **1.578e12 (−7.5 %) / 2.79 GB** |

- **The nanoda peak prediction (4.0–5.0 GB) is REFUTED.** It came in at 6.16 GB, although the largest walk fell 1,170 → 784.
- So the nanoda high-water is not set by the largest walk alone. The candidates are the PTREE subtree checks (`PTT_i_ok`;
  am-cert's PC9LP walk-only nanoda peaked at 9.4 GB) and the 33-kbit limb literals. Nothing measured yet tells them apart.
- A decision test is to run nanoda with TARGETS limited to {`rc10`} against {`PTT_ok`}. It needs the lock after INT9Q4.

**INT9Q4, first private check:**
- BUILD EXIT 1, from 5 errors, all "already declared" on PCellPT.
- Cause: the swap region already carries PCellPT, because the assembler orders it between PC9QB4Inst and PC9QB4Data inside the
  region, so my inserted copy was a duplicate.
- Fix: removed the inserted copy by Edit. INT9Q4.lean is now 2,177,497 B. The failed run is kept as specroot_int9q4_dupPT and
  int9q4b_dupPT.log; the pipeline was relaunched at 16:19.
- The failed build still gives one usable figure: 479 s, peak **5.51 GB**.

### nanoda peak isolation (lead approved 16:20; runs after INT9Q4)

**Runs:** walk-only `stage_bench.sh` on root_PC9QB4, with TARGETS (a) `AMW.Cert.PC9QB4Data.rc10` (the 784-leaf walk and its
closure) and (b) `AMW.Cert.PC9QB4Data.PTT_ok` (the 8 point-tree subtree checks and their closure).

**Hypotheses:**
- (i) PTREE sets the peak: (b) ≈ 6.0 GB and (a) ≤ 4.5 GB.
- (ii) The 784-leaf walk or the 33-kbit limbs set it: (a) ≈ 6.0 GB.
- (iii) The peak is cumulative over the closure: both (a) and (b) ≤ 5 GB.

**Predicted outcome:** (i), because am-cert's PC9LP walk-only nanoda peaked at 9.4 GB with PTREE 3.

**Decision rule:**
- (i): regenerate with PTREE 5 or 6 (32–64 subtree checks, a few hundred bytes each) and re-measure.
- (ii): compare LB 16384 on the same walk.
- (iii): neither lever applies; report it.

### jj restricted to the global top 63 (lead 10-11 ~16:25), subset check

**Set:** the global top 63 of the 67 jj values in PC9QB4 (`jtop63_PC9QB4.json`).
- It excludes jj 64, 94, 95, 96, the fine-grid j = 0, 30, 31, 32, with 133 of 223,016 uses.
- Coverage is 99.9404%, identical to window-scope's top63.log.

**Run:** size9pr.py + `JALLOW=jtop63_PC9QB4.json`: tangent candidates only at the allowed jj, everything else as PZ32R1
(RCUT 1:51168). Subset: old roots 2/5/9, i.e. PZ32 roots 2, 5, 9, 18, 21, 25.
- Baseline from the PZ32R1 full run, where per-root sizing is deterministic: **2,734 leaves, 875,739 walk bits**.

**Prediction:** leaves +0.0 to +0.5 %. Walk bits at the current 7-bit field: the same ± the leaf change. At a 6-bit field:
≈ −22 bits per leaf.

**Decision rule:**
- ≤ +0.5 %: adopt, pending am-cert's decode bench.
- +0.5 to +2 %: report the trade (≈ 55 KB against ≈ 127 B and 0.09 board-s per leaf).
- > +2 %: reject.
- **Amendment** (16:30, before any run; am-cert's PC9L series):
  - At PC9L the largest walk sets nanoda's peak, at ≈ 4.3 MB per leaf above a base. PTREE gave 9.41 GB against 10.32 GB without
    it, and LB 32k against 16k changed nanoda by only 0.4 %.
  - am-cert's walk-only TARGETS exclude `PTT_ok`. Mine (`PC9QB4_cert_full`) include it, and `rc10` alone would too, through
    `rcOf` → `ptS` → `PTT_ok`.
  - So the runs are (a) `rc10._proof_1` (the walk's own `decide`), (b) `PTT_ok`, and (c) `PT` (the base, am-cert's suggestion),
    via `iso9.sh`.
  - Revised prediction: (a) is 5.5–6.2 GB (am-cert's slope fit: 784 × 4.3 MB + a 2.8 GB base); (c) the base is 2.0–3.0 GB;
    (b) is ≤ 4.5 GB. That reverses my original prediction (i).

**jj top-63 result** (`cfx/t570_J63.log`, 16:24–16:40):

| PZ32 root | 2 | 5 | 9 | 18 | 21 | 25 | total |
|---|---|---|---|---|---|---|---|
| PZ32R1 | 291 | 521 | 649 | 459 | 494 | 320 | **2,734** |
| JALLOW top 63 | 286 | 524 | 659 | 457 | 493 | 329 | **2,748 (+0.51 %)** |

- Walk bits at today's 7-bit jj field: 877,171 against 875,739 (+0.16 %).
- At a 6-bit field the saving is ≈ −22 bits per leaf (22.13 jj fields per leaf in PC9QB4), so ≈ 816k bits on the subset, −6.8 %.
- The per-root changes are mixed in sign (−5 … +10), inside the ±3–4 % subset noise.
- **Prediction (≤ +0.5 %): at the edge.** +0.51 % falls in the "report the trade" band by 0.01 %.
- Full scale, +0.5 % is ≈ +50 leaves ≈ +6 KB and ≈ +5 board-s, against ≈ −55 KB from the 6-bit field. The trade favours
  the restriction if am-cert's decode bench passes.

### INT9Q4S: stripped and staged (16:32–16:53)

**Bytes:** **1,976,603 B**, 23.4 KB under the cap (unstripped 2,177,497; the strip removed 372 declarations). All three scored
theorems use only the standard axioms. Candidate 166950417639218487/247859045000000000 against the MoP2 record.

| stage | time | instructions | peak footprint | max RSS | INT9Q (footprint) | PC8C5BF, board-passed (footprint) |
|---|---|---|---|---|---|---|
| build | 431.8 s | 3.164e12 | **5.46 GB** | 8.74 GB | 7.09 | 4.86 |
| module replay | 247.3 s | 1.574e12 | 4.78 GB | 9.64 GB | 6.03 | 3.79 |
| export | 45.2 s | 0.342e12 | 1.60 GB | 6.44 GB | 1.61 | 1.59 |
| nanoda | 232.0 s | 1.812e12 | **6.96 GB** | 6.96 GB | 6.45 | 3.99 |
| closure replay | 291.6 s | 2.072e12 | 3.05 GB | 3.08 GB | 4.24 | 2.07 |

**Calibrated board time ≈ 2,650 s** (`board9.py`, which reproduces INT9Q's 2,920 s). Pre-registered 2,650–2,950: at the
bottom edge.

**Scoring:**
- Bytes 1.977 MB: inside the predicted 1.96–2.00.
- Build footprint 5.46 GB, and 5.67 GB unstripped: inside 5.5–6.2 for the unstripped build.
- **Full-file nanoda 6.96 GB is above the lead's ≈ 6 GB bar** and above INT9Q's 6.45, although walk-only nanoda fell to 6.16.
  - The full file adds ≈ 0.8 GB over walk-only here, against ≈ 0.05 GB for INT9Q.
  - nanoda's footprint equals its RSS (no mmapped oleans), so this is real memory.
  - The isolation runs (`iso9.sh`, started 16:53) are the decision test.

**Isolation results** (`iso9.log`, walk-only stages, TARGETS as named):

| TARGETS | export bytes | nanoda instructions | nanoda peak | closure replay peak |
|---|---|---|---|---|
| (a) `rc10._proof_1` (784-leaf walk) | 4.8 MB | 7.53e10 | **5.13 GB** | 2.55 GB |
| (b) `PTT_ok` (8 point subtrees) | 3.8 MB | 1.81e11 | 1.39 GB | 0.86 GB |
| (c) `PT` (base) | 2.8 MB | 5.6e8 | 0.008 GB | 0.014 GB |

- **(ii) holds: the largest walk sets the peak.** I predicted (i) first, then amended to (ii) before the run.
- The base is negligible, because nanoda does not evaluate definitions until a theorem needs them. So am-cert's 2.8 GB base is
  not a base: the full-file 6.96 GB is the 5.13 GB walk plus ≈ 1.8 GB accumulated over the rest of the closure (walk-only
  `cert_full`: +1.0 GB).
- **Per leaf:** PC9QB4's walk costs 5.13 GB / 784 ≈ 6.5 MB per leaf with 32,768-bit limbs. PC9QB's largest walk (1,170 leaves,
  16,384-bit limbs) fits inside a 6.40 GB walk-only peak, so ≤ ≈ 5.1 MB per leaf. This points at the limb width: each window
  read shifts a 33-kbit literal.
- **Next, pre-registered:**
  - `iso9b.sh`, per-walk peaks for roots of 37, 53, 521, 649 and 654 leaves, fitting peak = b + s·leaves. Prediction: s ≈ 6 MB
    per leaf, b ≤ 0.5 GB.
  - Then the same 784-leaf walk with LB 16384. Prediction: peak 3.0–4.0 GB.
  - Decision: if LB 16k cuts s by ≥ 30 %, revert to LB 16384 (+≈ 25 KB). Otherwise cap the largest walk.

### Per-walk nanoda peaks (LB 32768, `iso9b.log`) and the second-cut problem

| root | leaves | nanoda instructions | nanoda peak | MB per leaf |
|---|---|---|---|---|
| 31 | 37 | 4.96e9 | 0.30 GB | 8.0 |
| 0 | 53 | 6.29e9 | 0.35 GB | 6.6 |
| 5 | 521 | 5.16e10 | 2.84 GB | 5.4 |
| 9 | 649 | 6.62e10 | 4.66 GB | 7.2 |
| 4 | 654 | 6.84e10 | 4.67 GB | 7.1 |
| 10 | 784 | 7.53e10 | 5.13 GB | 6.5 |

- The fit through the ends is peak ≈ 0.06 GB + 6.5 MB × leaves, with scatter of ±0.4 GB (521 is low; 649 and 654 are high).
  Predicted s ≈ 6 MB per leaf and b ≤ 0.5: held.
- **To reach full-file nanoda ≤ 5.5 GB:** the walk must stay ≤ 5.5 − 1.8 = 3.7 GB, i.e. ≤ ≈ 560 leaves. That means cutting roots
  4, 9 and 10, not two roots.

**Boundaries needed** (PZ32R1 trees; the greedy subtree cut at cap C):

| cap C | 650 | 600 | 550 | 520 | 500 |
|---|---|---|---|---|---|
| boundaries | 14 | 29 | 30 | 31 | 37 |

- Roots 4/9/10 at C = 550 need 8/12/10 boundaries.
- **The 2–4 boundary estimate does not hold.** Each large root starts with a peel chain: root 10 is 783/1, 782/1, … (9 one-leaf
  peels), then 741 → 420 | 321; root 4 is 4 peels then 609 → 367 | 242.
- **Cost of the cheapest boundary layout:** a literal state at the bottom of each peel chain, compact one-leaf peels.
  - ≈ 170 chain closures ≈ +1.1e11 build instructions (≈ +3.5 %) plus similar on the kernel stages, ≈ +50–60 board-s.
  - ≈ 20–25 KB of state defs and piece theorems.

**Alternative (B): a second gap-1 cut, 48 roots, no boundaries.**
- `RCUT=1:51168,1:39936` splits the lower gap-1 interval [28672, 51168] at its midpoint.
- That doubles only the 16 lower-gap-1 roots, which hold every large root. The upper roots are unchanged, since sizing is
  deterministic.
- Overhead: 16 roots × ≈ 0.8 KB ≈ 13 KB, and 16 × 0.12 kernel-s.

**Subset test, running now:** roots 4/9/10 split (ROOTSEL 4,20,9,25,10,26; with 3 gap-1 intervals, index = 16·i1 + r).
- Baseline: 654 + 649 + 784 = **2,087**.
- **Prediction:** combined 1,900–2,200 (−9 … +5 %); largest ≤ 520.
- **Decision rule:**
  - Combined ≤ +3 % and every piece ≤ 560: (B) is viable. Re-size the 32 new lower roots (≈ 35 min) and emit.
  - Otherwise: the hybrid boundary layout above, or LB 16384 if its test shows the limb width drives the per-leaf peak.

**LB 16384 test (PC9QB4L, the same tree, Data +20.5 KB):**
- Data build: 1.4526e12 instructions, 3.68 GB peak, std axioms.
- The 784-leaf walk alone (`rc10._proof_1`): nanoda **5.135 GB** (7.46e10 instructions) against 5.134 GB with LB 32768; closure
  replay 2.55 GB against 2.55 GB.
- **Limb width does NOT drive the per-leaf peak.** My prediction (3.0–4.0 GB) is REFUTED; am-cert's 0.4 % holds. The limbs stay
  at 32768.
- The PC9QB/PC9QB4 per-leaf difference (≤ 5.1 against 6.5 MB) is therefore something else, plausibly the leaf mix. The fix is
  walk size: (B) or boundaries.

**Second gap-1 cut, result** (`cfx/t570_RCUT2.log`, RCUT 1:51168,1:39936):

| root | PZ32R1 | lower [28672, 39936] | upper [39936, 51168] | total |
|---|---|---|---|---|
| 4 | 654 | 400 | 2 | 402 (−38.5 %) |
| 9 | 649 | 615 | 1 | 616 (−5.1 %) |
| 10 | 784 | 650 | 2 | 652 (−16.8 %) |
| **all** | **2,087** | | | **1,670 (−20.0 %)** |

- **Rule outcome: the leaf part passes, the per-piece cap fails.** The prediction for the combined total (1,900–2,200) is
  REFUTED in the favourable direction: −20 %. The prediction for the largest piece (≤ 520) is REFUTED: 650 and 615.
- The [39936, 51168] slice costs 1–2 leaves per root. The gap-1 cut keeps acting as a LEAF lever: narrower root boxes in gap 1
  give much smaller trees.
- **Next test, pre-registered:** a third gap-1 cut at 34304 (RCUT 1:51168,1:39936,1:34304; 64 roots). Subset: the low pieces of
  roots 4, 9, 10, with ROOTSEL 4,9,10,20,25,26 (index 16·i1 + r; i1 = 0 is [28672, 34304], i1 = 1 is [34304, 39936]).
  - Baseline: 1,665 (the RCUT2 low pieces).
  - **Prediction:** combined 1,450–1,800; largest ≤ 450.
  - **Decision rule:** largest ≤ 560 and combined ≤ 1.03 × 1,665 → re-size the 16 lower roots under the 3 cuts (64 roots),
    emit, and measure. Otherwise the 48-root tree (2 cuts) plus the hybrid boundary layout on the ≥ 600 roots.

**Third cut (34304), partial result** (`cfx/t570_RCUT3.log`):
- Root 4: [28672, 34304] has 485 leaves and [34304, 39936] has 326, i.e. 811 against 400 with two cuts. Roots 9 and 10 low
  pieces: 432 and 590.
- **The third cut is WORSE.** The leaf cost is not additive over gap-1 slices: [34304, 39936] alone costs 326, but costs ≈ 0
  extra inside [28672, 39936]. The prediction (1,450–1,800, largest ≤ 450) is refuted. Per the rule, I go to the 48-root
  tree (2 cuts) plus the hybrid boundary layout on the roots ≥ 600.

### PZ48 re-size (17:46): the lower 32 roots under RCUT 1:51168,1:39936

- **Runs:** two processes, `full9s.sh`.
  - ROOTSEL 0–15, [28672, 39936]: dump `dump_full_t570_qz32r2lo.pkl`.
  - ROOTSEL 16–31, [39936, 51168]: dump `dump_full_t570_qz32r2sl.pkl`.
- **Merge:** `mergedump9.py` adds PZ32R1's 16 upper trees (its indices 16–31) as indices 32–47. emit9qr's replay checks every
  root cell.
- **Prediction:**
  - Lower roots 4,700–5,200 (PZ32R1: 5,828; the subset gave −20 %, which won't hold uniformly).
  - Slice roots 16–120 in total.
  - Whole tree 9,000–9,600 (PZ32R1: 10,077).
  - Roots > 560: roots 9 and 10, and possibly 1–2 more.

**Upper-interval cut, leaf-lever probe** (17:48, CPU only, pre-registered):
- In PZ32R1's upper roots the leaves' gap-1 extents lie in [51168, ≈ 200000]: hi at 10/50/90 % ≈ 73k/95k/≈ 200k.
- By analogy with the 39936 cut, try 229376 (7.0): RCUT 1:51168,1:39936,1:229376. Subset: PZ32R1 upper roots 18 and 21
  (459 + 494 = **953**) give ROOTSEL 34,50,37,53.
- **Prediction:** combined 800–1,000; the [229376, 557056] slices ≤ 20 leaves in total.
- **Decision rule:** combined ≤ 0.95 × 953 → propose a 64-root tree (both halves sliced); otherwise drop it.

### nanoda peak spread (lead and am-cert 17:48: the peak is ±0.9 GB run to run; the gate is the worst of ≥ 5 runs ≤ 6.0 GB)

- Every single-draw peak above (iso9/iso9b, the LB test, INT9Q4S 6.96) is one draw. That includes my LB 16k = 32k conclusion
  (5.135 against 5.134). am-cert's corrected PC9L series has LB 32k at +0.9 GB (+10 %) over 16k.
- **Re-measure** (`rep9.sh`, queued on the lock): one export of `rc10._proof_1` each for PC9QB4 (LB 32k) and PC9QB4L (LB 16k),
  then nanoda × 5 on each.
- **Decision rule, pre-registered:**
  - The mean difference of the two sets exceeds the larger of their ranges → limb width matters, and the cap is computed from
    the worse slope.
  - Otherwise → equal within noise. The walk cap is set from the worst draw per leaf, aiming at a largest walk ≈ 450 (the
    lead's headroom).
- **Lead 17:49:** T2 is not in PC9QB5. PC9QB5 = the 48-root tree (+ the upper slice if the 229376 probe passes) + L3 + L6 +
  RSPL on roots above the cap, with the cap from the worst-of-5 slope, aiming ≈ 450.
- **Lock order:** nanoda runs are sequential. am-cert's INT9Q4S × 5 goes first, then rep9.sh (which waits on `.leanlock`).

**Upper-cut probe result** (`cfx/t570_RCUT4.log`):
- [51168, 229376] pieces: root 18 → 512, root 21 → 558. Slices: 8 and 1.
- Combined **1,079 against 953 (+13 %)**. The prediction (800–1,000) is REFUTED and the rule says drop. The upper interval does
  NOT behave like the lower one, so there is no 64-root slicing.

**rep9 (rc10._proof_1, one export each, nanoda × 5):**

| variant | runs | peak range | instructions |
|---|---|---|---|
| LB 32k | 5 | 5.1350–5.1365 GB | 7.53–7.56e10 |
| LB 16k | 3 so far | 5.1342–5.1360 GB | 7.46–7.49e10 |

- **For a single walk theorem the peak is deterministic** (spread < 2 MB), and **LB 16k = LB 32k** for this walk. The ±0.9 GB
  variability is a property of multi-theorem exports (am-cert's {4 walks + PTT_ok}; INT9Q4S full file 5.51–5.95, and my single
  6.96 draw).
- So the per-walk slope is a stable quantity (≈ 6.5 MB per leaf on PC9QB4), and the full-file excess over the largest walk is
  the variable part: 5.95 − 5.13 = 0.82 GB at worst-of-5, with 6.96 − 5.13 = 1.83 GB as a single tail draw.

### PZ48 merged tree and PC9QB5 (no walk cut yet), 18:17–18:22

**Tree** `dump_full_t570_qz32r2.pkl` (`mergedump9.py`):
- Lower 16 roots: **5,432** against 5,828 (−6.8 %). Root 5 rose 521 → 666; roots 4/9/10 fell 654/649/784 → 400/615/650.
- Slice 16 roots: **31**.
- Upper 16 (PZ32R1 indices 16–31): **4,249**.
- **Total 9,712 (−3.6 % against 10,077).** Predicted 9,000–9,600 (lower 4,700–5,200): REFUTED on the high side. The −20 % of the
  4/9/10 subset did not carry to the other lower roots.
- Largest 666 (root 5).

**Emission** (emit9qr, RCUT 1:51168,1:39936):
- QB 13 FAILED: a multiplier with Yq = 8812 ≥ 2¹³ (`emit_PC9QB5_QB13fail.log`). Re-emitted at **QB 14** (+1 bit per multiplier,
  ≈ +2.3 KB hex).
- 0 verification failures; 3,048,398 walk bits (−3.4 %); 3,205 points, all with an interval.
- dprune: 145 of 496 blocks, all hulls pass.
- Longest leaf word ≤ 454 bits (WIN 480 OK).

**Split structure above 450 leaves** (`splitstruct9.py`, peel = side < 32 leaves), for am-cert's walkCut:

| root | leaves | structure |
|---|---|---|
| 5 | 666 | 7 peels → 609 \| 50; then 3 peels → **291 \| 303** |
| 9 | 615 | 10 peels → 563 \| 34; then → **374 \| 189** |
| 10 | 650 | 10 peels → **359 \| 243** |
| 34 | 459 | 11 peels → **389** \| 52 |
| 37 | 494 | 12 peels → **389** \| 91 |

Cutting the bold subtrees (8 cuts) leaves the largest walk at 389, with the root remainders ≈ 48–105.

**PC9QB5 modules without walkCut** (make9qIR: RCOMP, LIMB 32768, WIN 480, PTREE 3, PTD 1; genpcellQI GSPL 1, QB 14):

| | PC9QB5 | against PC9QB4 |
|---|---|---|
| Data | **1,071,837 B** | −37.5 KB |
| Inst | **122,601 B** | −23.3 KB (L6) |

INT9Q5S then projects to ≈ 1,976.6 − 60.8 ≈ **1,915.8 KB**, plus walkCut (≈ 8 × 0.9 ≈ 7 KB) ≈ 1.923 MB.

**Build of the walkCut-free PC9QB5** (queued), to validate L3 + L6 + QB 14 + 48 roots in Lean before walkCut is added.
Pre-registered:
- standard axioms;
- Data build instructions 1.36–1.50e12 (PC9QB4 1.454e12; −3.6 % leaves, +≈ 1.5 % L6);
- Data build peak 3.2–3.8 GB;
- walk-only nanoda (`cert_full`, one draw) 4.6–6.0 GB (largest walk 666 ≈ 4.3–4.7 GB alone).

### Walk cuts (am-cert's RSPLIT, lead 18:00) folded into make9qIR, giving PC9QB5C

**Port:**
- am-cert's make9pcI RSPLIT block (18:14) is ported verbatim, with cut selection as `cut_roots`.
- New: an RCOMP form for cut roots. `rcOfC` is `walkCutR` on `ofCl (RC …) 0` plus `covered_of_walkCutR`, so a cut root writes no
  root-state literal. With am-cert's root path (box literal ×3) the 5 cuts cost +15.8 KB; with `rcOfC` they cost **+5.1 KB
  (≈ 1.0 KB per cut)**.
- Instance: genpcellQI `RSPLIT=1` (am-cert's cutAt / kEqE / CutsOk / walkCut / walkCutR lemmas) + `GSPL=1`, QB 14.

**Cuts at cap 450** (greedy largest subtree ≤ 450):

| root | 5 | 9 | 10 | 34 | 37 |
|---|---|---|---|---|---|
| leaves | 666 | 615 | 650 | 459 | 494 |
| root part + cut | 363 + 303 | 241 + 374 | 291 + 359 | 13 + 446 | 105 + 389 |

Largest walk: **446**.

**Bytes:**

| | PC9QB5C | against PC9QB4 |
|---|---|---|
| Data | 1,076,888 B | |
| Inst | 126,432 B | (+3.8 KB for the walkCut lemmas over PC9QB5's 122,601) |
| total | | **−51.9 KB** |

INT9Q5S projects to ≈ 1,976.6 − 51.9 ≈ **1,924.7 KB**.

**Build pre-registration (PC9QB5C):**
- Standard axioms.
- Data build instructions 1.38–1.52e12 (PC9QB5 uncut + ≈ 1e9 per cut).
- Data build peak 2.6–3.4 GB (largest walk 446).
- Walk-only nanoda (`cert_full`, one draw) 3.5–5.0 GB.

### INT9Q5 assembly (18:30) and pre-registration

**Assembly:** `arun/int9q5.sh` builds INT9Q5_noIns from PC9QB5C (swap_cert9 into MOPX9), checks that outside the certificate
region it differs from INT9Q4_noIns in the change-notice weights line ONLY (measured: 1 line), and splices its certificate region
into INT9Q4.lean, which keeps the hand-made MoP2 window edits; the final instantiation is valid for the same W9 / B / c.
- INT9Q5_pre is 2,129,569 B. INT9Q5.lean is 2,129,597 B after one Edit of the header's certificate description.
- PTr and PTrD each occur once.

**Pipeline** (`int9q5b.sh` = int9q4b with the Q5 names): waits for PC9QB5C's build; unstripped check, reach (strip5/ReachQ5),
strip (keep.txt), stripped check, stages, then **4 more nanoda runs on the same export** (the lead's worst-of-≥ 5 gate).

**Pre-registration:**
- Standard axioms ×3.
- Stripped bytes 1.920–1.940 MB.
- Build footprint 4.4–5.2 GB.
- Full-file nanoda worst of 5 within 3.5–5.0 GB: largest walk 446 × 6.5 MB ≈ 2.9 GB, plus the 0.8–1.8 GB excess.
- Board time (board9) 2,600–2,720 s.
- **Balanced cut rule** (am-cert 18:3x, folded in before PC9QB5C started building): when one cut suffices, take the subtree
  minimising max(cut, root part).
  - Root 34 becomes 276 + 183, root 37 250 + 244, root 10 322 + 328; roots 5 and 9 are unchanged.
  - **Largest walk 446 → 426** (root 36, uncut). Data 1,076,894 B (+6 B).
  - INT9Q5 was re-assembled (the greedy assembly is kept as INT9Q5*_greedy, root9q5_greedy; its Data as
    PC9QB5CData.lean.greedy). INT9Q5.lean is 2,129,603 B.
  - Gate prediction (am-cert's law 1.8 GB + 6.43 MB × largest): ≈ 4.54 GB, inside my pre-registered 3.5–5.0.

### PC9QB5 / PC9QB5C module builds (18:21–18:50)

| | PC9QB4 | PC9QB5 (48 roots, no cuts) | PC9QB5C (5 balanced cuts at 450) |
|---|---|---|---|
| Inst instructions / peak | 4.10e11 / 1.68 | 4.21e11 / 1.71 | 4.37e11 / 1.70 GB |
| Data instructions | 1.454e12 | 1.437e12 | **1.451e12** |
| Data build peak | 3.67 GB | 3.32 GB | **2.60 GB** |
| walk-only nanoda (one draw) | 1.490e12 / 6.16 GB | 1.477e12 / 5.14 GB | **1.478e12 / 4.67 GB** |
| walk-only replay | 1.578e12 / 2.79 GB | 1.569e12 / 2.43 GB | 1.568e12 / 1.69 GB |
| axioms | std | std | **std** (first GSPL = 1 + RSPLIT = 1 compile: they combine) |

**Scores:**
- PC9QB5: 1.437e12 is inside 1.36–1.50; 3.32 GB is inside 3.2–3.8; std axioms.
- PC9QB5C: 1.451e12 is inside 1.38–1.52. The build peak (2.599 GB) is 1 MB under the pre-registered 2.6–3.4 GB, i.e. below the
  range, in the favourable direction. Walk-only nanoda 4.67 is inside 3.5–5.0.
- The cuts cost +1.4e10 Data-build instructions (≈ 2.8e9 per cut) and ≈ +1e9 nanoda in total.

### INT9Q5S: the result (18:47–20:21)

**Bytes:** **1,928,580 B** (sha256 01128ffe…3749f60), 71.4 KB under the cap. The unstripped 2,129,603 B lost 379 declarations
(201,023 B) to the strip. Pre-registered 1.920–1.940 MB: held.

**Axioms:** standard ×3 on the unstripped file, the stripped file, and the stripped file against the **attempt-020 record**
167025220139218487/247978200000000000 (`specroot_int9q5s_r20`: BUILD EXIT 0, REPLAY EXIT 0).

| stage | time | instructions | peak footprint | max RSS |
|---|---|---|---|---|
| build | 545.2 s | 3.171e12 | **4.36 GB** | 5.82 GB |
| module replay | 367.6 s | 1.591e12 | 3.69 GB | 7.66 GB |
| export | 59.2 s | 0.344e12 | 1.61 GB | 6.41 GB |
| nanoda run 1 | 272.3 s | 1.798e12 | 4.63 GB | 4.62 GB |
| closure replay | 376.3 s | 2.072e12 | 1.95 GB | 1.92 GB |

The wall times are inflated by machine load (build 545 s real against 438 s user). The board model uses instructions.

**Full-file nanoda, 5 runs on one export:**

| run | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| peak (GB) | 4.63 | 3.55 | 4.66 | 4.41 | **5.14** |
| instructions | 1.798e12 | 1.820e12 | 1.818e12 | 1.815e12 | 1.889e12 |

- **Worst of 5 = 5.14 GB ≤ 6.0 GB: the gate PASSES.**
- The pre-registered band (3.5–5.0) is exceeded by run 5; am-cert's law (≈ 4.54) is exceeded by 0.6 GB. Run 5 also retired
  +4 % instructions, so it is the noisy tail.

**Calibrated board time ≈ 2,648 s** (board9). Pre-registered 2,600–2,720: held.

**Scoring against the lead's gates:** bytes ≤ 2.0 MB ✓ (1.929); time ≤ 3,000 s ✓ (≈ 2,648); every footprint ≤ ≈ 5.5 GB ✓
(build 4.36, nanoda worst 5.14).
