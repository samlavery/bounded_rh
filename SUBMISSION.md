# riemannzeta.fun upload — what to enter

**File:** `~/work/riemann-submission/Solution.lean` (one UTF-8 Lean file, 1.86 MB; limit 2,000,000 bytes).

**Score (exact rational, the form supplies it, NOT the file):**
- numerator: `3363691`
- denominator: `5000000`
  (= 0.6727382; record 2 − 1/cMT = 0.6725007037; proved constant 0.67273822…)

**Method (≤ 200 chars):**
Three-point simple-zero refinement of the Montgomery–Taylor rank-trace certificate, kernel-checked finite certificate

**Summary (20–1000 chars):**
Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development, at n = 3, made
unconditional by a finite certificate proved inside Lean (368 interval cell lemmas, 487 leaves of a
two-dimensional bisection), assembled with window-count pressure bookkeeping. Constant
(447000000·H − 297200)/446400399 = 0.6727382… with H = 3/2 − (1/√2)cot(1/√2); H is enclosed to 1.1e-8
by a twelve-term Taylor argument, which places 3363691/5000000 strictly between the record and the
proved constant. Simple on-line zeros are counted among the distinct on-line zeros (N0simple ≤ N0star).
No new axioms.

**Model / harness (optional):** Claude (Anthropic) / Claude Code

**What the verifier will do (54 min, 4 vCPU, 8 GB):** lake build of the file against the prebuilt
pinned Zeta23, comparator statement check, lean4export + nanoda replay. Local measurement of this
file (Mac, 4 threads): see `full_j4.log` — time and peak memory are the risk, not the mathematics.

---
# Upload 2 (2026-09-30): the FOUR-POINT rung, checker-verified

**File:** `~/work/riemann-submission/Solution4.lean` (556,997 bytes).
**Score:** numerator `269141`, denominator `400000` (= 0.6728525; proved constant (906250·H − 1080)/904171 ≥ 0.6728525442).
**Local check (pristine clone, lean -j4):** 0 errors; all three theorems `[propext, Classical.choice, Quot.sound]`;
121.8 s wall, 162 s CPU, peak RSS 16.3 GB / footprint 12.7 GB.
**Method (≤200 chars):** Four-point simple-zero refinement of the Montgomery–Taylor rank-trace certificate; finite certificate checked by a verified rational checker (decide +kernel)
**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 4, with
window-count pressure bookkeeping, made unconditional by a finite certificate (983 table cells, 64 bisection trees,
3713 leaves) verified inside Lean by a generic soundness theorem for a rational interval checker; the certificate
itself is data checked by kernel evaluation. Constant (906250·H − 1080)/904171 = 0.67285254… with
H = 3/2 − (1/√2)cot(1/√2); H is enclosed to 1.1e-8 by a twelve-term Taylor argument, which places 269141/400000
strictly between the record and the proved constant. No new axioms.

---
# Upload 2, REVISED (2026-09-30 evening): four-point, data-driven, sized for the sandbox

**File:** `~/work/riemann-submission/Solution4b.lean` (443,657 bytes). Supersedes `Solution4.lean`.
**Score:** numerator `269141`, denominator `400000` (= 0.6728525).
**Local check (pristine clone, lean -j4, synchronous elaboration):** 0 errors; standard axioms;
**277 s wall, 247 s CPU, peak footprint 3.97 GB** (RSS 8.9 GB including file-backed oleans).
**What changed vs Solution4.lean:** certificate as data checked by the kernel; bisection trees as one bit per
node (`bits : ℕ`), cells found by value in a search tree, chunks of ≤ 250 leaves per kernel theorem,
`set_option Elab.async false` (kernel checks are serial anyway; async held every chunk's memory → 9.4 GB).
**Why the first upload failed:** comparator timeout (3200 s) during `Solution.Candidate` after 294 s for
`ChallengeDeps`; the sandbox is ~4× slower per core than this machine and 8 GB. Expect this file at ≈ 20 min there.

---
# Candidate 3 (2026-10-01): the SIX-POINT WEIGHTED rung — proven; needs the limits raised

**File:** `~/work/riemann-submission/SolutionSixW35HD.lean` (5,039,906 bytes; board limit 2,000,000 → a limits PR
is required: size ≥ 6 MB would do; time see below).
**Score:** numerator `6730187`, denominator `10000000` (= 0.6730187; proved constant
Φ_w'(6, c, m, B) with c = 345747/10⁸ is (9800000000·H − 17339711)/9766693039 = 0.67301873…; H enclosed to 1.1e-8).
**Local check (pristine clone, lean -j4, synchronous):** stamped twin of this file: 0 errors, all three theorems
`[propext, Classical.choice, Quot.sound]`, **1869 s wall (31.2 min), peak footprint 6.35 GB** (RSS 11.9 GB with
file-backed oleans). **Exact file as-is (final bytes): 0 errors, standard axioms, 1285 s wall (21.4 min), peak footprint 4.94 GB** (`sixw35rk_final3.log`; sha256 8df210a9bac7d251842f5fc5…).
**Cost breakdown (stamps):** 124,274 leaf checks 1306 s (10.5 ms each), 105,565 cell checks 347 s (3.3 ms each),
table elaboration 64 s, box defs 21 s, bit literal 10 s, everything else < 3 s.
**Method (≤200 chars):** Six-point weighted simple-zero refinement of the Montgomery–Taylor rank-trace certificate
(pair weights, window-count pressure); finite certificate checked by a verified integer checker (decide +kernel)
**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 6 with
pair weights a_{ij} and per-gap pressures b_r (the lab's AMTOPA family at the Montgomery–Taylor window), made
unconditional by a finite certificate (105,565 table cells, 108 bisection trees with 124,274 leaves, split axes
stored in the tree's bit string) verified inside Lean by a generic soundness theorem for an integer interval checker
(Taylor enclosures of cos/sin at scale 10¹⁵, cells keyed by packed endpoints); the certificate is data evaluated by
the kernel. Constant (9800000000·H − 17339711)/9766693039 = 0.67301873… with H = 3/2 − (1/√2)cot(1/√2), enclosed
to 1.1e-8, which places 6730187/10000000 strictly between the record and the proved constant. No new axioms.
**Alternatives on disk:** δ = 3% greedy certificate would give 0.6730305 at ~172k leaves (≈ 42 min here, not built);
widest-axis δ = 3.5% (`SolutionSixW35C`, 233,844 leaves) proved in 3517 s / 7.8 GB.
**Unknowns for the sandbox:** its per-core speed relative to this Mac (the accepted four-point's verifier time
would calibrate it: 277 s here); whether 6.35 GB footprint fits the 8 GB VM (the four-point ran at 3.97 GB).

---
# Candidate 4 (2026-10-01): the SIX-POINT rung UNDER THE 2 MB LIMIT — proven

**File:** `~/work/riemann-submission/SolutionSixW35RK.lean` (**1,158,852 bytes**; board limit 2,000,000; header docstring describes this certificate). Supersedes
Candidate 3 for size; same constant.
**Score:** numerator `6730187`, denominator `10000000` (= 0.6730187; proved constant (9800000000·H − 17339711)/9766693039
= 0.67301873…; H enclosed to 1.1e-8).
**Local check (pristine clone, lean -j4, synchronous):** stamped twin: 0 errors, all three theorems
`[propext, Classical.choice, Quot.sound]`, **1278 s wall (21.3 min), peak footprint 5.09 GB** (RSS 11.0 GB with
file-backed oleans). **Exact file as-is: 0 errors, standard axioms, 1240 s wall (20.7 min), peak footprint 4.94 GB** (`sixw35rk_final.log`; sha256 9eac7e00f69af9404c79aade…).
**Cost breakdown (stamps):** 112,490 leaf checks 1107 s (9.8 ms each), 10,345 cell checks 25 s, bit literal 9 s,
table/box elaboration 12 s, rest < 2 s.
**What changed vs Candidate 3 (5.0 MB, 31 min):** (i) the LP pair weights symmetrised under gap reversal (free: same
level, 124,327 vs 124,274 leaves) and only the half-space g₀ ≤ g₄ certified, the rest by a reflection lemma
(`G_rev`, `cert_full` in the tail; leaf rule u₄ < l₀ in the walk); (ii) far pieces (x ≥ 3) rounded outward to a
1/256 grid inside the generator, so the table holds 10,345 cells instead of 105,565 (the leaf-specific far
end-pieces sat beside the zeros of the kernel and could not be rounded after the fact); (iii) cells keyed by one
packed number, boxes as defs chained to the parent, local notation for the tree. Leaves 83,738 → 112,490 from (ii).
**Method (≤200 chars):** Six-point weighted simple-zero refinement of the Montgomery–Taylor rank-trace certificate
(symmetric pair weights, half-space by reflection); finite certificate checked by a verified integer checker
**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 6 with
pair weights a_{ij} (symmetrised under gap reversal) and per-gap pressures b_r, made unconditional by a finite
certificate (10,345 table cells, 108 bisection trees with 112,490 leaves on the half-space g₀ ≤ g₄, the rest by the
reflection symmetry of the functional) verified inside Lean by a generic soundness theorem for an integer interval
checker (Taylor enclosures of cos/sin at scale 10¹⁵); the certificate is data evaluated by the kernel. Constant
(9800000000·H − 17339711)/9766693039 = 0.67301873… with H = 3/2 − (1/√2)cot(1/√2), enclosed to 1.1e-8, which places
6730187/10000000 strictly between the record and the proved constant. No new axioms.
**Unknowns for the sandbox:** its per-core speed relative to this Mac (21 min here; the accepted four-point's
verifier time, 277 s here, would calibrate it); 5.1 GB footprint against the 8 GB VM (the four-point ran at 3.97 GB).

# Candidate 4, REVISED (2026-10-01 afternoon): record moved, `strict` repaired, verifier budget re-read

**What happened.** The board accepted `five-point-pyramid` (typh, Claude Opus 5.5; "Builds on submission attempt-002
(Samuel Lavery)"; 39,780 leaves, 41,115 cells, 1.42 MB) at **13457757/20000000 = 0.67288785**, after `attempt-002`
(0.6728525, 01:47Z). The board regenerates `CandidateSpec.lean` with `currentRecordKappa := <rational of the last
accepted candidate>`, no longer `2 - 1/cMT`. Our old tail proved `currentRecordKappa = HD 1` by unfolding the closed
form; against the rational record that lemma leaves `13457757 / 20000000 = 2 - 1 / cMT` unsolved (the error at
`Candidate.lean:11388`), and `candidate_strict_improvement` picked up `sorryAx`. The two bound theorems passed.

**Fix (in the file, `tail_common.lean`, `gen_tail_w.py`):** the record lemma is gone; `strict` is
`unfold currentRecordKappa candidateKappa; first | (norm_num; done) | <closed-form fallback via cStar_one_eq_cMT>`.
Checked against both record forms in `comparator/Solution/StrictTest.lean` (12 s). Local `CandidateSpec.lean` now
carries the board's pair (record 13457757/20000000; candidate per file) — rebuild it when the record moves.

**File:** `~/work/riemann-submission/SolutionSixW35RK.lean`, **1,159,198 bytes**, sha256 dd3aaac5d300bacbdb199c9b….
**Score:** numerator `6730187`, denominator `10000000` (0.6730187; above the new record by 1.31e-4; proved constant
0.67301870808, margin 8.1e-9). **Exact file, pristine clone, lean -j4, synchronous, olean written:** 0 errors, all
three theorems `[propext, Classical.choice, Quot.sound]`, **1397 s wall (23.3 min; generators were running alongside),
peak footprint 5.03 GB**, log `sixw35rk_rec.log`. Method/summary text as in Candidate 4 above.

**Verifier budget, read at source (`e2b/run-verification-job.sh`, accepted `verifier.log`s, comparator README):** ONE
`timeout 3240s` wraps the whole job: ChallengeDeps build (160 s in typh's log; 294 s on our upload 1) → `lake build`
of the candidate (elaboration + kernel) → `lean4export` → **nanoda replay** → **Lean default-kernel replay** ("Replay
the Solution environment into the Lean kernel"). Every `decide +kernel` certificate check is evaluated three times.
With the build at ~1400 s here (≈ 90 % kernel) the six-point file as it stands fits only if the sandbox is faster per
core than this Mac. The Lean replay is being measured here with `comparator/Solution/ReplayHarness.lean`
(`Lean.Environment.replay`, the API the comparator uses); nanoda could not be built here (external-code permission
denied) — the calibration that settles it is the verifier duration of `attempt-002` (277 s build here) or of typh's file.

**Fallbacks, same pipeline, same weights, larger slack δ (generated; compiles in progress):**

| file | δ | κ (form fields) | above record by | cells | leaves | bytes |
|---|---|---|---|---|---|---|
| `SolutionSixW35RK.lean` | 3.5 % | 6730187 / 10000000 | 1.31e-4 | 10,345 | 112,490 | 1,159,198 |
| `SolutionSixW6.lean` | 6 % | 3364797 / 5000000 (0.6729594) | 7.2e-5 | 8,220 | 32,612 | 820,595 |
| `SolutionSixW8.lean` | 8 % | 42057 / 62500 (0.6729120) | 2.4e-5 | 6,814 | 18,058 | 703,915 |

Leaf checks cost ≈ 9.8 ms each here, cells ≈ 2.5 ms: expect ≈ 6 min (SixW6) and ≈ 3.5 min (SixW8) builds.
**Slots:** three admitted uploads per GitHub account per UTC day, failures included; today's count is at least two.

**MEASURED (2026-10-01, pristine clone, synchronous):**

| file | build (lean -j4, with olean) | Lean kernel replay of the module (`ReplayHarness`) | footprint |
|---|---|---|---|
| `SolutionSixW35RK.lean` | 1397 s, 0 errors, axioms standard | **1144 s** (4049 constants) | 5.03 GB |
| `SolutionSixW8.lean` | **344 s**, 0 errors, axioms standard | **213 s** (2003 constants) | 4.48 GB |
| `SolutionSixW6.lean` | **492 s**, 0 errors, axioms standard | **373 s** (2549 constants) | 4.85 GB |

The replay costs the full kernel time again, so the sandbox job ≈ ChallengeDeps (160–294 s) + build·σ + nanoda·σ′ +
replay·σ, with σ the sandbox's per-core slowdown against this Mac (unknown; the memory's "≈ 4×" came from a
multi-threaded elaboration comparison and is an upper bound for single-thread kernel work) and σ′ nanoda's cost
relative to Lean's kernel (unknown; it has the Nat extension). Taking σ′ = σ:
- `SixW35RK`: 294 + 3685·σ → does not fit for any σ ≥ 1. **Do not upload** until the checker is ≳ 3× cheaper.
- `SixW8`: 294 + 770·σ → fits for σ ≤ 3.8. **Recommended upload:** numerator `42057`, denominator `62500`.
- `SixW6`: 294 + 1238·σ → fits for σ ≤ 2.4 (numerator `3364797`, denominator `5000000`). Second step once a
  sandbox duration is known; its summary text is the `SixW8` one with 8,220 cells / 32,612 leaves and constant
  (3762500000·H − 6659889)/3750038770 = 0.67295943…, κ 3364797/5000000.

**ACCEPTED (2026-10-01, attempt-005): `SolutionSixW8.lean`, 42057/62500 = 0.672912, "Your solution is okay!"** —
Sam rank 1. Sandbox calibration from its log: ChallengeDeps 148 s; `Built Solution.Candidate (691s)` against 344 s
here ⇒ **σ ≈ 2.0** per core. nanoda's own time is not printed; the job's total duration on the site would pin it.
Projections at σ = 2 with nanoda ≈ Lean replay: `SixW6` ≈ 148 + 2·(492 + 373 + 373) = 2624 s (44 min, ~10 min
margin — safe only if nanoda is not slower than ~1.8× the Lean kernel); `SixW7` ≈ 1976 s (33 min, see below);
`SixW35RK` ≈ 5200 s (never, as computed).

**`SolutionSixW7.lean` (δ 7 %) — built and verified locally:** 753,278 bytes, sha256 5086141b5ef789125957f13f…;
7,486 cells, 23,519 leaves; **κ = 6729357 / 10000000 = 0.6729357** (above the record by 4.8e-5; proved constant
(305000000·H − 539991)/304000379 = 0.67293574…, margin 4.6e-8). Pristine clone: 0 errors, axioms standard on all three
theorems, **386 s build, 264 s kernel replay, 4.84 GB**. Form fields: numerator `6729357`, denominator `10000000`;
summary = the `SixW8` text with 7,486 cells / 23,519 leaves and the constant above.
**Order of preference for the next upload:** `SixW6` (0.6729594, ≈ 44 min projected) if attempt-005's total duration
shows nanoda ≲ 1.8× the Lean kernel; otherwise `SixW7` (0.6729357, ≈ 33 min projected, ≈ 20 min margin).

**Form text for `SixW8`** — Method (≤200 chars): Six-point weighted simple-zero refinement of the Montgomery–Taylor
rank-trace certificate (symmetric pair weights, half-space by reflection); finite certificate checked by a verified
integer checker. Summary: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at
n = 6 with pair weights a_{ij} (symmetrised under gap reversal) and per-gap pressures b_r, made unconditional by a
finite certificate (6,814 table cells, 108 bisection trees with 18,058 leaves on the half-space g₀ ≤ g₄, the rest by
the reflection symmetry of the functional) verified inside Lean by a generic soundness theorem for an integer interval
checker (Taylor enclosures of cos/sin at scale 10¹⁵); the certificate is data evaluated by the kernel. Constant
(30800000000·H − 54539091)/30700123625 = 0.67291202… with H = 3/2 − (1/√2)cot(1/√2), enclosed to 1.1e-8, which places
42057/62500 strictly between the record and the proved constant. No new axioms.

---
# Response to five-point-pyramid-2 (typh, 67291431/100000000 = 0.67291431, accepted 2026-10-01 23:26Z)

New UTC day as of 2026-10-02 00:00Z, so three upload slots are fresh. Both rungs below were built locally: 0 errors,
all three theorems `[propext, Classical.choice, Quot.sound]`. Their `strict` decides the board's rational record
by `norm_num`, so it is unaffected by the new record.
- 0.6729357 − 0.67291431 = +2.14e−5.
- 0.6729594 − 0.67291431 = +4.51e−5.

## Option A — larger lead: `SolutionSixW6.lean`
- 820,595 B, sha256 b28cd214…
- Numerator `3364797`, denominator `5000000` (0.6729594; proved constant (3762500000·H − 6659889)/3750038770 = 0.67295943…).
- Local timings: build 492 s, Lean kernel replay 373 s.
- Sandbox (σ ≈ 2.0, calibrated from attempt-005: 344 s here → 691 s there):
  - job ≈ 148 + 2·(492 + 373 + nanoda);
  - nanoda ≈ Lean replay ⇒ ≈ 2,620 s of 3,240 s;
  - nanoda = 1.5× replay ⇒ ≈ 3,000 s;
  - nanoda = 2× replay ⇒ over the limit.
- Certificate: 8,220 cells, 32,612 leaves.

## Option B — safe: `SolutionSixW7.lean`
- 753,278 B, sha256 5086141b…
- Numerator `6729357`, denominator `10000000` (0.6729357; proved constant (305000000·H − 539991)/304000379 = 0.67293574…).
- Local timings: build 386 s, replay 264 s.
- Sandbox ≈ 148 + 2·(386 + 264 + 264) ≈ 1,980 s. That is about 12% heavier than the accepted attempt-005; typh's file
  built in 732 s there, against a projected 772 s for this one.
- Certificate: 7,486 cells, 23,519 leaves.

**Method (both):** Six-point weighted simple-zero refinement of the Montgomery–Taylor rank-trace certificate (symmetric pair weights, half-space by reflection); finite certificate checked by a verified integer checker.

**Summary (both; substitute the counts and constant):** Ainta's n-point simple-zero refinement of Theorem D of the pinned
Zeta23 development at n = 6, with pair weights a_ij (symmetric under gap reversal) and per-gap pressures b_r, made
unconditional by a finite certificate (<cells> table cells, 108 bisection trees with <leaves> leaves on the half-space
g₀ ≤ g₄, the other half by reflection) verified inside Lean by a generic soundness theorem for an integer interval
checker. Constant <constant>, with H = 3/2 − (1/√2)cot(1/√2) enclosed to 1.1e-8, which places the submitted rational
strictly between the record and the proved constant. No new axioms.

**Suggested order:** A first. If it times out, B with the next slot. A failed upload consumes a slot, and this leaves
one spare.

---
# Candidate RKF (2026-10-02): the 0.6730187 certificate with the FORCED checker — fits the sandbox

**File:** `~/work/riemann-submission/SolutionSixW35RKF.lean` (1,200,465 bytes; sha256 0dae8e79…4a8e91).
**Score:** numerator `6730187`, denominator `10000000` (0.6730187; proved constant (9800000000·H − 17339711)/9766693039
= 0.67301870…; +1.04e-4 over typh's 0.67291431).
**Local check:** 0 errors; three scored theorems `[propext, Classical.choice, Quot.sound]`. Build 455 s (RK was
1,240–1,397 s); Lean kernel replay 298 s (RK 1,144 s); peak 3.1 GB (RK 5.0 GB).
**Same certificate as RK:** the data and checker are byte-identical apart from the forced section (`force`, plus
forced copies with proved equalities `walkF_eq` etc.) and the walk-theorem proof lines.
**Sandbox projection (σ ≈ 2):** 148 + 2·(455 + 298 + nanoda).
- nanoda ≈ replay ⇒ ≈ 2,250 s of 3,240.
- nanoda = 2× replay ⇒ ≈ 2,850 s, which still fits.

**Caveat:** it was built against the OLD local spec (record 13457757/20000000). Rebuilding the shared CandidateSpec was
denied to the agent by the permission system. `strict` decides the rational record by `norm_num`, and
`bench/StrictRecordCheck.lean` shows the same tactic proves 67291431/100000000 < 6730187/10000000.

**Method:** Six-point weighted simple-zero refinement of the Montgomery–Taylor rank-trace certificate (symmetric pair weights, half-space by reflection); finite certificate checked by a verified integer checker (decide +kernel), forced evaluation.

**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 6, with pair
weights a_ij (symmetric under gap reversal) and per-gap pressures b_r, made unconditional by a finite certificate
(10,345 table cells, 112,490 leaves of a five-dimensional bisection on the half-space g₀ ≤ g₄, the other half by
reflection), verified inside Lean by a generic soundness theorem for an integer interval checker. Constant
(9800000000·H − 17339711)/9766693039 = 0.67301870… with H = 3/2 − (1/√2)cot(1/√2) enclosed to 1.1e-8, which places
6730187/10000000 strictly between the record and the proved constant. No new axioms.

**RKF verified against the CURRENT record (2026-10-02).**
- Setup: a private spec copy (`bench/specroot/ChallengeDeps/CandidateSpec.lean`, the board template filled with
  `currentRecordKappa := (67291431 : ℝ) / 100000000` and `candidateKappa := (6730187 : ℝ) / 10000000`), resolved first on
  `LEAN_PATH`. The shared spec is untouched.
- Result: `SolutionSixW35RKF.lean` compiles with 0 errors. Both `rfl` checks confirm those spec values were in force.
  All three scored theorems are `[propext, Classical.choice, Quot.sound]`. 435 s, 3.07 GB.
- Log: `bench/specroot/rkf_newrecord.log`.
- The board's statement template (`challenge/templates/Challenge.Candidate.lean`) is byte-identical to the local
  comparator's.

**Minified RKF (2026-10-02):** `SolutionSixW35RKF_min.lean`, 787,024 bytes (65.6% of 1,200,465), sha256 7bee9bbc…2e256.
- Made by `lean_minify.py` with passes comments, tree, ns, ids, walk, hex, ws.
- Checked against the old spec: 0 errors, standard axioms, scored statements byte-identical, replay 291 s, and every
  constant equal to the original's modulo auto-generated hygiene names (`bench/olean_diff_min35rkf.log`).
- Checked against the CURRENT record (private spec): 0 errors, standard axioms, 439 s, 3.06 GB
  (`bench/specroot/rkfmin_newrecord.log`).
- Same score, 6730187/10000000.

---
# NEXT UPLOAD (2026-10-02): `SolutionSixW4F.lean` — fits the corrected budget

**Score:** numerator `1682517`, denominator `2500000` (0.6730068; +2.14e-5 over typh's 33649269/50000000 = 0.67298538).
**File:** 1,071,783 bytes, sha256 39b374299f7156d7….
**Certificate:** 9,880 cells and 80,882 leaves (δ 4%), forced checker.
**Full check against the CURRENT record** (private spec, record 33649269/50000000, candidate 1682517/2500000):
- 0 errors; three scored theorems `[propext, Classical.choice, Quot.sound]`; build 393 s, 2.97 GB;
- kernel replay 229 s, 3,634 constants;
- logs: `bench/specroot3/build4F.log`, `replay4F.log`.

**Budget (corrected after the RKF timeout):** job ≈ 148 + 2·build + 6.7·replay = 148 + 786 + 1,534 ≈ 2,470 s, i.e.
about 41 min of the 54. The same model gives 2,263 s for SixW8, and attempt-005 observed 2,260. It gives 3,055 for RKF,
which ran 3,206 and was rejected.

**Method:** Six-point weighted simple-zero refinement of the Montgomery–Taylor rank-trace certificate (symmetric pair weights, half-space by reflection); finite certificate checked by a verified integer checker (decide +kernel), forced evaluation.

**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 6, with pair
weights a_ij (symmetric under gap reversal) and per-gap pressures b_r, made unconditional by a finite certificate
(9,880 table cells, 80,882 leaves of a five-dimensional bisection on the half-space g₀ ≤ g₄, the other half by
reflection), verified inside Lean by a generic soundness theorem for an integer interval checker. Constant
(2950000000·H − 5219913)/2940025276 = 0.67300685…; the submitted rational 1682517/2500000 lies strictly between the record and the proved constant, with H = 3/2 − (1/√2)cot(1/√2)
enclosed to 1.1e-8. No new axioms.

---
# BEST UPLOAD (2026-10-02): `SolutionSixW25P.lean` — pyramid oracle, δ 2.5 %

**Score:** numerator `6730423`, denominator `10000000` (0.6730423; +5.7e-5 over typh's 0.67298538; above SixW4F).
**File:** 941,272 bytes, sha256 67d3591552b12aeb…; the header carries the attribution "Pyramid lower-bound table adapted
from five-point-pyramid-2 by typh (Apache-2.0)".
**Certificate:** 167,720 leaves (half-space); pyramid with 7,374 finest cells and 495 blocks; forced walk.
**Full check against the CURRENT record:** `bench/specroot_pyr/`, private spec with record 33649269/50000000 and
candidate 6730423/10000000. The checked file is byte-identical to the upload file plus the appended rfl/axiom checks.
- 0 errors; three scored theorems `[propext, Classical.choice, Quot.sound]`; build 311 s, 3.0 GB.
- Kernel replay 174 s, 2,683 constants.
**Budget (corrected model):** 148 + 2·311 + 6.7·174 ≈ 1,940 s, about 32 of the 54 min.
**Method:** Six-point weighted simple-zero refinement of the Montgomery–Taylor rank-trace certificate (symmetric pair weights, half-space by reflection); dyadic pyramid of lower bounds for w checked by a verified integer pipeline (decide +kernel).
**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 6, with pair
weights a_ij (symmetric under gap reversal) and per-gap pressures b_r, made unconditional by a finite certificate: a
five-dimensional bisection with 167,720 leaves on the half-space g₀ ≤ g₄ (the other half by reflection), each leaf
decided by a dyadic pyramid of lower bounds for w (495 blocks, 7,374 finest cells certified by the integer cell test;
pyramid adapted from five-point-pyramid-2 by typh, Apache-2.0). Constant (14550000000·H − 25739571)/14500045810 with
H = 3/2 − (1/√2)cot(1/√2) enclosed to 1.1e-8, which places 6730423/10000000 strictly between the record and the
proved constant. No new axioms.

---
# ACCEPTED (2026-10-02 04:20Z): attempt-009 = `SolutionSixW25P.lean`, 6730423/10000000 — record 0.6730423
Board log: ChallengeDeps 129 s, Solution.Candidate **624 s** (local 311 s → board/local build = 2.01, same as SixW8 691/344).
Job duration ≤ 38 min (upload after 03:42:47Z, verified 04:20:42Z).

**Local copy of the verifier's post-build stages (2026-10-02; tools/ at the pinned commits: lean4export b18d673,
nanoda 4183202, comparator 2732944 runKernel → tools/replayx):** for Cand25P
- lean4export 49 s (631 MB, 73,007 constants in the closure);
- nanoda 180 s (4.5 GB peak) — ≈ 1.0× the module-only Lean replay (174 s), NOT 4.7×;
- parse 14 s + Lean replay of the FULL closure 256 s (the Mathlib/Zeta23 closure is a fixed ≈ 82 s).
- Post-build local ≈ 500 s. The old law "6.7·replay" lumped closure, parse and machine speed together.
Script: `bench/nanoda/stage.sh MOD LEANPATH_PREFIX`. Calibration of the post-build board factor via a clean SixW8 rebuild
(stale Solution/Cand8.olean gives an inconsistent export: nanoda asserts at tc.rs:921) is queued.

**Next rungs assembled (`assemble_pyr.py NAME`, template = the accepted 25P file; tail differences checked):**
| file | κ | bytes | leaves |
|---|---|---|---|
| SolutionSixW22P.lean | 3365247/5000000 = 0.6730494 | 1,091,782 | 220,851 |
| SolutionSixW21P.lean | 3365259/5000000 = 0.6730518 | 1,140,043 | 244,346 |
| SolutionSixW20P.lean (agent) | 3365271/5000000 = 0.6730542 | 1,146,479 | 272,175 |

**Verified against record 6730423/10000000 (private spec roots `bench/specroot_rec`, `bench/specroot_rec20`), 0 errors,
three theorems [propext, Classical.choice, Quot.sound]; local stages via `bench/nanoda/stage.sh`:**
| file | κ | build | module replay | export | nanoda | parse | closure replay | post-build total |
|---|---|---|---|---|---|---|---|---|
| SixW25P (accepted) | 0.6730423 | 311 | 174 | 49 | 180 | 14 | 256 | 499 |
| SixW22P | 0.6730494 | 385 | 233 | 38 | 211 | 15 | 306 | 570 |
| SixW20P | 0.6730542 | 399 | 279 | 36 | 246 | 15 | 364 | 661 |
Board projection = 154 + 2.0·build + f·post-build. With f = 2: 22P ≈ 2,064 s and 20P ≈ 2,276 s (build 439 → 2,352 s).
f is calibrated by the clean SixW8 run (board 2,260 s).

**CALIBRATED BUDGET MODEL (2026-10-02, replaces "6.7·replay"):** board ≈ 157 + 2.0·build_local + f·post_local, where
post_local = export + parse + nanoda + full-closure Lean replay, measured with `bench/nanoda/stage.sh`.
- Build factor 2.0: board/local = 691/344 (SixW8) and 624/311 (25P).
- f ≤ 2.56: SixW8 is accepted at about 2,260 s on the board, and its clean local post-build is 552 s (export 36, parse 14, nanoda 221, closure 281).
  All overhead is charged to f.
- 25P: 157 + 624 + 2.56·499 = 2,058 s, consistent with the observed ≤ 2,276 s.
- **nanoda is engine-specific; measure it, never assume it.**
  - Pyramid files run nanoda at 180–246 s (≈ 0.9–1.0× the module replay).
  - The forced-CTN RKF had nanoda > 765 s (killed) against a 285 s module replay.
  - So RKF's post-build was ≥ 1,140 s, and the model gives > 3,240 s. This explains its timeout.
- **RKF's "lean-elaboration-failed at 5213:31" was a TIMEOUT, misclassified by the board.**
  - `finalize-e2b-job.ts` writes "The verifier exceeded its isolated runtime limit." for exit 124/137.
  - `verifier-feedback.ts` matches only "exceeded its runtime limit", so the timeout falls through.
  - The elaboration patterns then match "tactic failed" in the normal info line "The `ring` tactic failed to close the goal".
  - The first `Solution…lean:L:C` in the log is the push_neg warning at 5213:31.

# NEXT UPLOAD (2026-10-02): `SolutionSixW20P.lean` — 3365271/5000000 = 0.6730542
- Exact constant (7225000000·H − 12779787)/7200070409 = 0.6730542233.
- 1,146,479 bytes, sha256 35eba8f17e40bf0c…ce0a.
- Certificate: 272,175 leaves (half-space); pyramid with 495 blocks, 8,722 finest cells and 16,949 entries.
- Verified against record 6730423/10000000: 0 errors, standard axioms.
- Local timings: build 399–439 s, module replay 279 s, export 36 s, nanoda 246 s, parse 15 s, closure replay 364 s.
- Projection: 157 + 2·439 + 2.56·661 ≈ 2,730 s (16 % under 3,240).
- Conservative alternative: `SolutionSixW22P.lean`, 3365247/5000000 = 0.6730494, sha256 29c0b1c2…0df8, ≈ 2,390 s (26 % margin).
**Method:** Six-point weighted simple-zero refinement of the Montgomery–Taylor rank-trace certificate (symmetric pair weights, half-space by reflection); dyadic pyramid of lower bounds for w checked by a verified integer pipeline (decide +kernel).
**Summary (20P):** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 6, with pair
weights a_ij (symmetric under gap reversal) and per-gap pressures b_r, made unconditional by a finite certificate: a
five-dimensional bisection with 272,175 leaves on the half-space g₀ ≤ g₄ (the other half by reflection), each leaf
decided by a dyadic pyramid of lower bounds for w (495 blocks, 8,722 finest cells certified by the integer cell test;
pyramid adapted from five-point-pyramid-2 by typh, Apache-2.0). Constant (7225000000·H − 12779787)/7200070409 with
H = 3/2 − (1/√2)cot(1/√2) enclosed to 1.1e-8, which places 3365271/5000000 strictly between the record and the proved
constant. No new axioms.

---
# ⚠ SUPERSEDED (2026-10-02 08:52Z): typh "six-point-convex-basins-2" = 67311649/100000000 = 0.67311649 is the record.
**Do NOT upload** SixW20P, SixW22P, SixW003L (0.6731008) or SixW005L (0.6731004). All are below the record and would fail
`candidate_strict_improvement`.
- typh built on attempt-009, credited "Samuel Lavery, Apache-2.0". They added:
  - LP-reoptimised mirror-symmetric weights (B = 305611/10⁸, c = 548021/10⁸, m = 187);
  - convex-basin certificates at 15 near-minimal minima (w″ enclosures, PSD by exact LDLᵀ, tangent planes);
  - a 67,100-leaf bisection.
- Six-point LP ceiling at their B: 0.6731190, so that family is saturated.
**Next rung = seven-point (Q = 6).** LP ceilings: 0.6731563 (B 0.0029), 0.6731589 (B 0.0032, upper 0.6731629). Eight-point (Q = 7, B 0.003):
0.6731925. Logs are in `bench/lp/`. The mvt-engine agent is generalising our mean-value engine to Q = 6, with typh's basins (credited).

---
# UPLOAD NOW (2026-10-02 ~19:00Z): `UPLOAD_SevW30S.lean` — SEVEN-POINT, 6731541/10000000 = 0.6731541
**Form:** numerator `6731541`, denominator `10000000`. That is +3.76e-5 over typh's 0.67311649.
**File:** `UPLOAD_SevW30S.lean`, a frozen read-only copy of `SolutionSevW30S.lean`: 1,559,899 bytes, sha256 81189759403535d8…3338.
**Constant:** (14900000000·H − 57200286)/14800563663 = 0.6731541059.
**Checked against record 67311649/100000000** (`bench/specroot_sev30c`, the exact file plus rfl checks):
- 0 errors; three theorems [propext, Classical.choice, Quot.sound];
- build 523 s, replay 261 s (4,269 constants);
- stage: export 37 s, nanoda 253 s (0.97× replay), parse 15 s, closure replay 325 s.
**Projection:** 157 + 2·523 + 2.56·630 ≈ 2,816 s (13 % under 3,240) by the conservative model; ≈ 2,460 s at f = 2.
**Method:** Weighted seven-point refinement of the Montgomery–Taylor rank-trace certificate; mean-value (slope) leaf test with certified w′ bounds, convex basins at the minima, pyramid oracle elsewhere (decide +kernel).
**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 7 (six gaps), with
LP-optimised mirror-symmetric pair weights and pressures (B = 0.004), made unconditional by a kernel-checked certificate
on the half-space g₀ ≤ g₅ (the rest by the reflection symmetry): 39,046 leaves, each decided by one of three verified
tests: zero-order (a pyramid of lower bounds for w), a slope test (tangents on certified convex regions of w and
mean-value charges from an enclosed derivative pyramid for w′ = 2πNM/D³), or membership in one of 16 certified boxes around
the near-minimal local minima. Pyramid table adapted from five-point-pyramid-2 by typh, and basin boxes after
six-point-convex-basins-2 by typh (Apache-2.0). Constant (14900000000·H − 57200286)/14800563663 = 0.67315410…, H enclosed
to 1.1e-8. No new axioms.

---
# ACCEPTED (2026-10-02 19:31:51Z): attempt-010 = `UPLOAD_SevW30S.lean`, 6731541/10000000 — RECORD 0.6731541 (ours)
- Board timings: ChallengeDeps 119 s; Solution.Candidate 940 s against 523 s locally, a build factor of **1.80**.
- The job took ≤ 2,620 s (recommended at 18:48:12Z, verified at 19:31:52Z); the conservative model had said 2,816 s.
- Post-build factor ≤ 2.46.
- Both accounts were at 3/3 uploads on 10-02; the next slot is at 00:00Z on 10-03.

# NEXT UPLOAD (after 00:00Z 10-03): `SolutionSevW10D.lean` — 6731631/10000000 = 0.6731631 (+9.0e-6 over attempt-010)
- File: 1,379,099 B, sha256 cc979a958f5b49d6…bcfe.
- Constant: (7450000000·H − 28600143)/7400182089 = 0.6731631789.
- δ = 0.1 % below the rounded minimum 697452; Q=6 LP weights at B = 0.0040; m = 149.
- Leaves: 41,536 (19,274 zero-order, 19,866 slope, 94 basin in 16 basins, 2,302 reflected).
- Checked against 67311649/10⁸: 0 errors, standard axioms, build 517 s, replay 243 s.
- Stage: export 40 s, nanoda 230 s, closure replay 307 s.
- Projection: ≤ 157 + 2·517 + 2.46·577 ≈ 2,610 s.
- Re-check against the new record 6731541/10⁷ is running (`bench/specroot_sev10dr`).
- Method and summary: as for SevW30S, with δ, leaf counts and constant replaced (see the agent's report above).
**SevW10D re-checked against the NEW record 6731541/10000000** (`bench/specroot_sev10dr`):
- 0 errors; three theorems [propext, Classical.choice, Quot.sound]; build 581 s; replay 228 s (4,173 constants).
- Ready to upload at 00:00Z on 10-03.
- Seven-point LP ceiling at B 0.004: 0.6731675, so SevW10D is within 4.4e-6 of it.

---
# TARGET 0.67340 (Sam, 2026-10-02). This is above the highest claim found, 0.673316977, which is not in Lean.
- The MT window falls short. LP ceilings at B 0.004: n=7 0.6731675, n=8 0.6732021, n=9 0.6732186 (upper 0.6732280).
- AMTOPA's 17-term window ("AM") under our assembly (window-scope agent, `bench/window/am_runs.log`):
  - n=7, B 0.0040435: 0.6734131 (H_AM = 0.6721881581, m = 132);
  - n=8: 0.6734398.
  - So 0.67340 needs seven points at δ ≲ 0.25 %.
- Kernel: K_v = c0·K_MT + x·sin(πx)·Σ_j (−1)^j c_j/(x²−j²)/π.
- Two tracks:
  - (1) mvt-engine: the AM certificate (6-D, w_AM enclosures);
  - (2) window-scope: the BRIDGE, i.e. Theorem D for the AM window in one file (MT is hard-wired in `ThmD/ParamsD.lean`).
**SCOPE landed (`bench/window/SCOPE.md`): buildable, nothing infeasible encountered.**
- Plan: n = 7, AMTOPA window with 13 terms ÷ 5/4, B 0.0040, ceiling 0.6734131. κ ≥ 0.67340 needs δ ≲ 0.25 %.
- Owners and stages:
  - window-scope: A (window defs) + E (limits, H closed form);
  - bridge-port: B (AdmWindow via PV), C (zero side), D (prime side), F (bridge retarget);
  - mvt-engine: G (certificate for w = k_v²).
- Shared root: `bench/window/root/AMW/`. Estimate 1.3–1.7 MB; the agent's estimate is 10–14 agent-days, run in parallel.
- Riskiest step: G against the 3,240 s budget.

# TWO TARGETS (Sam, 2026-10-02 ~20:55Z)
**Target 1: the highest κ WITHOUT changing Theorem D** (pinned MT window, our existing bridge).
- Owner: mvt-engine, MT eight-point in `bench/eight/` (n = 8 ceiling 0.6732021; n = 9 0.6732186).
- It must beat SevW10D's 0.6731631. The sizing passes 140k leaves, so the budget is the risk.
**Target 2: ≥ 0.67340 with the AMTOPA window** (new Theorem D window inside our file).
- window-scope: A + E.
- bridge-port: B, C, D, F.
- am-cert (new): G, the 6-D certificate for w = k_v².
**Target 1, eight-point MT: measured over budget with the current certificate (mvt-engine, `bench/eight/`).**
- Q=7 LP best: B 0.0041 → 0.6732025.
- Rounded weights at B 0.004 have minimum 0.0070357725, with 387 local minima (25 within 3 %).
- Leaves: 215,075 at δ 0.6 %, and over 220k at 0.3 % before it was stopped. δ is irrelevant: the leaves are spread through the box, not at the minima.
- The 28-term instance alone takes 175 s to elaborate.
- Kernel estimate ≈ 780 s against ≈ 210 s of room (3.7× over). Data ≈ 2.3 MB, over the size limit.
- Time-boxed diagnosis is running (leaf provenance; monotone face reduction; tail dropping; box second-order).
- Go/no-go threshold: about 45k leaves. Until then the target-1 file is SevW10D (0.6731631).
**Target 2: stages A + E COMPLETE (window-scope, 2026-10-02 ~21:20Z).** Modules: AMW/{Window, Moments, Swap, Constant, Floor}, ~99 KB.
- Lead-verified axioms are standard for:
  - `tendsto_cRatio_W` (the analogue of tendsto_cRatio_concrete);
  - `swap_identity` and `JInf_eq_energy` (the riskiest obligation, closed);
  - `HW_eq` (closed form) and `HW_ge : 6721883/10^7 ≤ HW` (exact HW = 0.6721883029);
  - `eventually_aW_range` and `eventually_bW_ge_half`.
- Stages B, C and D modules from bridge-port are compiled: Adm, PV, Params, Profile, ZeroSide, Concrete, BHalf, Trig.
- Next: F split between window-scope (kernel: KfunAM closed form, |K| ≤ K(0), gram_close_of/kernel_limit) and bridge-port (tail_passage, endgame, HD 1 ↦ HW). G is am-cert.
**Target 2: stages B, C, D COMPLETE (bridge-port).** Modules: AMW/{Adm, Profile, Trig, PV, Params, ZeroSide, Concrete, BHalf}, ~108 KB.
- Lead-verified axioms are standard for: `admWindow_phiW`, `pvCheck_AM` (PV ≤ 0.0392 against the 0.0487 budget, 64 cells, ~7.5 s kernel), `eventually_blockInputsAM`, `eventually_GzGpAM`, `eventually_tailPackageAM`, `eventually_aAM_range`, `tracesBoundsAM_concrete`, `eventually_bAM_ge_half`, `integral_vAM_sq_ge`.
- **Stages A–E are done**, about 207 KB of new source. Remaining: F (split kernel/endgame), G (am-cert, budget risk), H (assembly).
**Target 2: stage F COMPILED (bridge-port, ~21:40Z).** The bridge is retargeted to the AM window: AMW/BrA (41.6 KB), BrB (32.6 KB), BrC (126.7 KB). It is a COPY of SevW10D lines 55–4583 in the Zeta23Ext namespaces, so it replaces the old bridge.
- Lead-verified:
  - standard axioms for `BridgeW.n_point_bound_w'`, `tail_passage`, `kernel_limit`, `gram_close_of`, `deleted_strips`, `endgame_defect`;
  - `Bridge.wfun = AMW.wfunAM` by rfl;
  - no HD 1 / kfun_closed / phiD / atD remnants.
- The export n_point_bound_w' gives (Phi_w' − ε)·N ≤ N0simple, with Phi_w' = (AMW.HW − B(m−q)/m)/(1 − c(m−q)/m), given the certificate hypothesis ∀ g ≥ 0, c ≤ Fw W g.
- **ONLY G (the certificate) and H (assembly) remain for target 2.**

---
# UPLOAD AFTER 00:00Z 10-03: `UPLOAD_SevW03D.lean` — 6731663/10000000 = 0.6731663 (replaces SevW10D)
**Form:** numerator `6731663`, denominator `10000000`. That is +1.22e-5 over attempt-010 (0.6731541) and +5.0e-5 over typh's 0.67311649.
**File:** read-only copy of `SolutionSevW03D.lean`, 1,389,416 bytes, sha256 7ce968bd4e3c0218…6c26c9.
**Constant:** (7450000000·H − 28600143)/7400147197 = 0.6731663529. Seven-point MT ceiling 0.6731677.
**Checks:**
- Against 6731631/10⁷ (`bench/specroot_sev03d`): 0 errors, standard axioms, build 530 s, replay 241 s (4,179 constants).
- Stage: export 41 s, nanoda 232 s, closure replay 309 s.
- Re-check against the live record 6731541/10⁷ is running (`specroot_sev03dr`).
**Projection:** 157 + 2·530 + 2.46·597 ≈ 2,685 s. Observed for SevW30S: ≤ 2,620 s, with board build factor 1.80.
**Method:** Weighted seven-point refinement of the Montgomery–Taylor rank-trace certificate; slope test with certified convex regions and w′ bounds, 16 certified basins, pyramid elsewhere (decide +kernel).
**Summary:** Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23 development at n = 7 (six gaps), with
LP-optimised mirror-symmetric pair weights and pressures (B = 0.004), made unconditional by a kernel-checked certificate
on the half-space g₀ ≤ g₅ (the rest by reflection): 42,570 leaves, each decided by a zero-order pyramid bound for w, a
slope test (tangents on 15 certified convex regions of w, mean-value charges from an enclosed derivative pyramid,
expansion at basin centres), or membership in one of 16 certified boxes around the near-minimal local minima, with
basin centres chosen to maximise the exact margin. Pyramid table adapted from five-point-pyramid-2 by typh, and basin
boxes after six-point-convex-basins-2 by typh (Apache-2.0). Constant (7450000000·H − 28600143)/7400147197 =
0.67316635…, H enclosed to 1.1e-8. No new axioms.
**SevW03D re-checked against the LIVE record 6731541/10⁷** (`bench/specroot_sev03dr`): 0 errors, standard axioms, build 503 s, replay 223 s.
READY for 00:00Z.
**Target 2, stage G sizing (am-cert, ~22:00Z): a straight port is ≈ 2.8× over the kernel budget.**
- AM n=7, rounded weights (B = 404348/10⁸). Minimum 0.0079106940 with 248 local minima: 13 within 1 %, 42 within 3 % (flat).
- κ: δ 0.1 % → 0.6734085, 0.2 % → 0.6734034, 0.25 % → 0.6734008.
- Leaves: 103,631 at δ 1 %, 125,927 at δ 0.2 %, against SevW10D's 41,536. δ barely matters; about 70k leaves sit near ~45 near-minimal minima.
- Cell enclosures are as tight as MT's, so the landscape is the cause.
- Plan:
  - am-cert: raw-Nat AM cell evaluator; lever 5 (LP weights de-equalised, trading part of the 1.3e-5 ceiling headroom); merged evaluations; index leaf words.
  - mvt-engine: Hessian-PSD basins covering ~45 minima + mirrors (typh-style, credited), monotone face reduction, tail dropping. These are engine components that also serve MT eight-point (target 1).
- bridge-port: PV certificate sped up 7.5 s → 2.8 s; all of A–F rebuilt, standard axioms.
**Target 2, stage F end state (bridge-port, ~22:15Z): AMW/AMTail.lean.**
- Lead-verified standard axioms for `am_dyadic`, `am_cumulative` and `Phi_w'_ge`.
- Given the certificate hCert (∀ g ≥ 0, c ≤ Fw W g) and κ ≤ Phi_w' 7 c m B, it proves (κ−ε)·Ncount 0 T ≤ N0star 0 T.
- Demo: c = 0.0078927 (≈ 0.9978 ε*), m = 132 ⇒ κ = 0.67340 with a margin of ~2e-6.
- Bridge pruned 201 → 141 KB.
- The ONLY missing input for 0.67340 is the certificate hCert (stage G).
**Target 2, stage H dry run (window-scope, ~22:30Z):** `bench/window/assemble_am.py` → `AMH.lean` (433 KB).
- Contents: all 17 AMW/Br modules, plus a stand-in tail that takes hCert as a hypothesis.
- Private check (`specroot_amh`): build 96.9 s, module replay 17.8 s (989 constants), export 37.7 s, nanoda 53.6 s, closure replay 82.6 s.
- **The whole analytic layer projects to 779 s** of the board job.
- **Remaining for the certificate:**
  - ≤ 1,921 s conservative, i.e. local build ≤ ~420 s and module replay ≤ ~200 s: about one SevW10D-sized certificate.
  - ≤ 2,444 s at the hard limit (f = 2.56), about 1.3× SevW10D's.
  - ≤ ~1.56 MB.
- The straight AM port is ≈ 2.8× SevW10D's certificate cost, so G needs ≈ 2.2–2.8× efficiency.
**Eight-point diagnosis (mvt-engine, ~22:45Z, Python, `bench/eight/`).**
- Parent boxes of leaves have a LARGE true margin: median +24 %, p10 +8 %, all > 1 %. So the bounds are loose; the geometry is not the cause.
- Zero-order loss: spans 1–2 carry 2/3 of it. All 7 derivative intervals straddle 0 in 85 % of parents.
- Tests:
  - (i) monotone face reduction: −3 %;
  - (ii) tail dropping: infeasible (min w over [x,∞) is 0);
  - (iii) box second order: certifies 0.7 %.
  - No-go on all three by the 45k rule.
- **Lead: per-term independent affine minorants.** Each term gets its own certified line below w on I_t; the resulting linear function is minimised over the box.
  - The LP version certifies 599/600 parents.
  - The Lean-certifiable version (lines with one-sided MVT slopes at 5/9 grid points) certifies 277–293/300.
  - Leaf count not yet measured; needs ≲ 15–20k leaves to pay for ~2–3× per-leaf cost.
- Next: size it on AM n=7 (target 2) first, then MT n=8. Target 1 stays at SevW03D until then.
**Stage G progress (am-cert, ~23:00Z):**
- More expansion centres: 16 → 125.9k leaves; 80 → 94.3k; 200 → 84.7k (Z 37.3k, S 44.4k).
- Kernel ≈ 355 s against SevW10D's ≈ 190 s, a gap of ~1.9×.
- AM cell evaluator (AMW/GCell) is bit-identical to Python on 46 cells. Cost per cell: 1.6 / 3.7 / 5.9 ms (w / w′ / w″).
- Proven (no sorry): GSinc, GMT, GTaylor, GIv, GBase, GFar.
- Remaining for the evaluator: near-pole terms, the MT part, K0/K1/K2 assembly, then the table/walk port.
- Gap levers: mvt-engine (PSD basins + per-term minorants in bench/psd); am-cert lever 5 (de-equalised weights).
**Stage H final (window-scope, ~23:10Z):**
- `AMHM.lean`: the AM layer + bridge + AMTail + SevW10D's whole certificate as a stand-in, 1.52 MB.
  - Build 536 s, module replay 226 s, export 40 s, nanoda 245 s, closure replay 345 s.
  - **Projection 2,779 s conservative** (2.9 % over 2,700); 2,842 s at f = 2.56, passing with a 398 s margin.
- Context: SevW10D alone projects to 2,610 s, so the AM layer adds ≈ +170 model-seconds.
- The SevW30S calibration (observed ≤ 2,620 s against 2,816 projected) suggests the real figure is lower.
- **G budget: ≈ 0.96× SevW10D's certificate (conservative) up to ≈ 1.2× (hard model)**; ≤ 1.63 MB.
- Current AM certificate ≈ 1.87× SevW10D's (84.7k leaves at 200 centres), so it needs ≈ 1.6–1.9× more efficiency.
**Stage G full build (am-cert, ~23:30Z): the AM n=7 certificate COMPILES and is sound, but is not uploadable.**
- `AMW.Cert.AMS02_cert_full`: δ 0.2 %, cN 789487/10⁸, κ 0.6734034, 84,720 leaves, standard axioms.
- Kernel ≈ 558 s for the data module (tables 105 s, basins 80 s, walk 335 s) against SevW10D's ≈ 190 s certificate: ~3× over.
- Size: 2.36 MB with the bridge, over 2 MB.
- The AM cell evaluator and its soundness (GIv … GCellSound, 0.15 MB) are DONE and reusable.
- Decisions:
  - (a) AM window at n = 6 now (ceiling ≈ 0.6733167, ≈ +1.5e-4 over our record) as an uploadable intermediate; bridge-port adds n = 6 AMTail instances.
  - (b) n = 7 at ≥ 0.67340 continues via mvt-engine's per-term minorant + PSD basin sizing and bridge-port's Lean levers (LeverAM), which thin AMS02.
**LEVER FOUND (mvt-engine, ~00:00Z 10-03): per-term tangent-minorant LP. AM n=7 at δ 0.2 %: 104k → 21,130 leaves** (Z 6.5k, S 1.9k, M 11.6k); integer-faithful Python.
- Each pair term gets its own minorant, combined convexly by an LP: constant pyramid min; tangents at 256-grid points in certified convex regions, extended to the whole range by derivative-table monotonicity; chords across concave ranges.
- Single-minorant rounding accepts only ~13 %, so the convex combination is essential.
- Estimated cost: 3–8 ms per M-leaf; walk ≈ 60–75 s against SevW10D's ≈ 100 s. Payload ≈ 0.6 MB.
- PSD basins add nothing over region-convex basins covering all 42 minima (−21 % either way).
- Lean split:
  - mvt-engine: (3) convex-combination test and (4) walk/encoding;
  - bridge-port: (1) extended-tangent lemma and (2) concavity check + chord lemma;
  - am-cert: integration into AMS02 after its n=6 build.
**Target 1 reopened (mvt-engine, ~00:10Z):** MT eight-point with the per-term minorant test needs 17,052 leaves at δ 0.6 % and 18,027 at δ 0.3 %, against 215,075 (12× fewer).
- κ ≈ 0.6731890 at δ 0.3 %, and ≈ 0.673198 at δ 0.1 % if the 34 basins pass.
- Data ≈ 0.75 MB.
- Order: build the shared Lean component, first instance OctM (MT n=8), then AM n=7 via am-cert.
- Lemmas (1)–(2) go to bridge-port; (3)–(4) to mvt-engine.
**AM SIX-POINT certificate BUILT (am-cert, ~00:15Z):** `AMW.Cert.AMX05_cert_full`, δ 0.05 %, cN 707843/10⁸, B 0.0036, m 146, κ ≈ 0.6733144 (+1.5e-4 over SevW03D).
- 14,106 leaves. Kernel ≈ 102 s, about half of SevW10D's certificate. ≈ 1.26 MB with the bridge.
- BLOCKER: the data build peaks at an 8.4 GB footprint. The board sandbox is 4 CPU / 8,192 MB (e2b/build-template.ts), while SevW10D passed at 4.8 GB.
- am-cert is reducing memory to ≤ 5 GB and moving to δ 0.01 % (κ ≈ 0.673316).
- window-scope assembles the full n=6 file, runs the private check and staging, and reports peak memory.
- The six-point ceiling (0.6733167) cannot beat the 0.673316977 claim; this rung is a board step only.
**Update (~00:25Z):**
- AM n=6 memory is resolved: with `set_option Elab.async false` (already in our header) the data build peaks at 1.9 GB.
- δ 0.01 % failed (3 basin margins negative), so n=6 stays at AMX05: δ 0.05 %, κ ≈ 0.6733144. window-scope is assembling and checking it.
- n=7 owners:
  - am-cert: integration on AMS02;
  - mvt-engine: convex-combination leaf and walk, first on MT8;
  - bridge-port: extended-tangent and chord modes in LineMode.
- Endpoint-line modes alone (LineMode 2/3) sized at ~99.5k leaves, i.e. no lever.

---
# UPLOAD NOW (2026-10-03 ~00:30Z): `UPLOAD_AM6.lean` — 6733143/10000000 = 0.6733143 (SKIP SevW03D)
**Form:** numerator `6733143`, denominator `10000000`. That is +1.60e-4 over attempt-010 (0.6731541) and +1.98e-4 over typh's 0.67311649.
**File:** read-only copy of `bench/window/AM6.lean`, 1,311,211 bytes, sha256 cc034e6fba00d098…28a0a5.
**Mathematics:** the weighted six-point refinement with the AMTOPA window (13 terms ÷ 5/4) in place of the MT window; Theorem D re-proved for it in-file.
- Constant: H_AM ≥ 6721883/10⁷, m = 146, Φ ≥ 0.6733143769.
**Checks** (`bench/specroot_am6`, record 6731663/10⁷; strict improvement is norm_num, so it holds against any record < 0.6733143):
- 0 errors; three theorems [propext, Classical.choice, Quot.sound];
- build 343.5 s at a 4.06 GB footprint; replay 133.5 s (4,349 constants);
- stage: export 39.7 s, nanoda 134.9 s, closure replay 207.5 s.
**Projection:** 157 + 2·343.5 + 2.46·382.1 ≈ 1,784 s (44 % under 3,240).
**Note:** typh's job c05a76b7 was active at 00:30Z (their first 10-03 upload). Ours queues behind it and is checked against whatever record holds when it runs.
**Method:** Weighted six-point refinement with the AMTOPA window (Theorem D re-proved in-file for it); pyramid/slope/basin certificate checked by a verified integer pipeline (decide +kernel).
**Summary:** Ainta's weighted n-point simple-zero refinement at n = 6, with the Montgomery–Taylor window of the pinned Zeta23
Theorem D replaced by AMTOPA's window (first 13 cosine terms of zeta-exact-pressure, scaled by 4/5). Theorem D's
window-dependent parts are re-proved in-file for this window:
- admissibility (a certified positive-variation bound);
- zero side and prime side (ported from Zeta23's XiPrime/ThmD, Apache-2.0);
- the a/b/J limits (incl. an exact integral-swap identity);
- the exact constant H_AM = H_MT − Σ c_j²(½ − 1/(4π²j²))/(2 sin²(1/√2)) ≥ 0.6721883;
- the retargeted Zeta Lab bridge (MIT).
Finite certificate: 14,106 leaves on the half-space g₀ ≤ g₄ (pyramid/slope tests with 200 expansion centres; pyramid
table adapted from five-point-pyramid-2 by typh, centres after six-point-convex-basins-2 by typh, Apache-2.0), with a
new integer enclosure of the AM pair kernel. κ = 6733143/10⁷ ≤ (H_AM − B(m−5)/m)/(1 − c(m−5)/m) at m = 146. No new axioms.

# typh LANDED (2026-10-03 00:39Z): "six-point-window" 67316747/10⁸ = 0.67316747
- Six-point weighted refinement with the single-cosine window cos(3s/2) in place of cos(√2 s): H = 0.6723988626, kernel with γ = (3/4)cot(3/4).
- B = 360551/10⁸, c = 653514/10⁸ (δ 0.01 %), m = 158; 18 basins, 77,684 leaves; board build 634 s.
- It imports Zeta23.XiPrime.* directly, so those oleans work on the board; our local copies were stale.
- It credits attempt-009.
- **SevW03D (0.6731663) would have FAILED against it. Skipping it was right.**
- **AM6 (0.6733143) beats it by +1.47e-4.** Strict improvement is `unfold; norm_num`, valid for any record < 0.6733143.
- UPLOAD AM6 NOW.
**AM n=6 at the ceiling (am-cert, ~00:45Z): AMX002, δ 0.002 %, κ = 6733166/10⁷** (Φ = 0.67331660297; ceiling 0.67331669). 14,872 leaves, 1.9 GB.
- window-scope is assembling AM6x.lean and checking it against the live record 67316747/10⁸.
- Neither n=6 file beats the 0.673316977 claim; the ceiling is 3e-7 short.

**n=7 leaf census (am-cert):** at 200 centres, δ 0.2 %, 84,720 leaves.
- 51 % have margin > 100 %; 25 % are at 50–100 %; 17 % at 20–50 %; < 1 % at < 5 %.
- 88 % of slope leaves are at ≥ 20 % margin. So the cost is the bulk, the per-term minorant's target.
- Lever 5 (de-equalised weights) is predicted ≤ ~1 % gain. It is UNTESTED and skipped in favour of the minorant integration.

---
# UPLOAD NOW (2026-10-03 ~01:08Z): `UPLOAD_AM6x.lean` — 6733166/10000000 = 0.6733166 (replaces AM6)
**Form:** numerator `6733166`, denominator `10000000`. That is +1.49e-4 over typh's live record 0.67316747.
**File:** read-only copy of `bench/window/AM6x.lean` (assemble_am.py --final6 AMX002), 1,387,024 bytes.
**Constant:** Φ = 0.67331660297 (H_AM floor 6721883/10⁷, m = 146, cN 708183/10⁸, δ 0.002 %). Six-point ceiling 0.67331669.
**Checked against the LIVE record 67316747/10⁸** (`bench/specroot_am6x`):
- 0 errors; three theorems [propext, Classical.choice, Quot.sound];
- build 383 s at a 4.08 GB footprint; replay 145 s (4,397 constants).
- Staging is running.
**Projection:** ≈ 157 + 2·383 + 2.46·≈395 ≈ 1,900 s.
**Method:** as AM6.
**Summary:** as AM6, but with δ 0.002 %, 14,872 leaves and Φ ≥ 0.6733166030 at m = 146.
**AM6x staging COMPLETE:** export 39 s (1.6 GB), nanoda 154 s (2.8 GB), parse 16 s, closure replay 228 s (74,812 constants, 1.4 GB).
- Post-build 437 s. Projection 157 + 2·383 + 2.46·437 ≈ 2,000 s (38 % under 3,240).
- Fully verified; upload-ready.
**WINDOW RE-OPTIMISATION (window-scope, ~01:20Z): the "R window".** ω₀ = √2 kept; the 12 cos(2πjs) corrections re-optimised jointly with the weights for OUR assembly.
- n=6 ceiling: 0.6733167 → **0.6733687** (B 0.0036, H_R = 0.6722203, ε* 0.0071126, m 145). That **beats the 0.673316977 claim by 5.2e-5**, with δ room up to ~0.3 %.
- n=7 ceiling: 0.6734131 → ≥ 0.6734250 so far (optimiser running).
- Single cosine cos(ω₀s): n=6 best is 0.6731746 at ω₀ = 1.5, consistent with typh's 0.67316747.
- Lean delta (ω₀ = √2): Window coefficients, Constant (PAM), Floor, the PV certificate and the certificate data. Kernel form, Moments, Swap, bridge and AMTail are unchanged.
- Build in a NEW root `bench/window/rootR/AMW/` (root/ is frozen for the AM6x upload).
- Owners: window-scope leads the n=6 R build; bridge-port re-runs PV; am-cert regenerates the n=6 certificate.
**n=7 M-test reproduced (am-cert):** AM δ 0.2 % gives 21,087 leaves (mvt-engine had 21,130).
- Chords add 0.3 %, so they can be dropped. A 10-bit λ two-line rounding costs +2.5 %; 5-bit costs +8 %.
- Basins certify 0 leaves once the M-test is on, so no basin layer is needed. Kinds: Z 7.2k, S 2.3k, M 11.1k.
- Kernel estimate 130–200 s against ~215 s of allowed module replay; the M-leaf cost is to be measured.
**UPLOADED (Sam, 2026-10-03): AM6x, 6733166/10⁷.** Board job 01dedda9 (owner a74474), enqueued 01:23:52Z and running now.
Expected to finish ≈ 01:57–02:10Z (projection ≈ 2,000 s). Sam has 2 uploads left on 10-03; typh has 2.
**Window optimisation FINAL (window-scope, ~01:30Z):**
- n=7 ceilings at B 0.004: MT 0.6731674; cos(1.5s) 0.6732217; AM13 0.6734131; **R7 (re-optimised) 0.6734250** (H 0.6721812, ε* 0.0078740, m 133).
- Three local optimisers stop near +1.2e-5, so AMTOPA is near a local optimum at n=7. No global search was run.
- For the 0.67340 build, δ room roughly doubles (≈ 0.25 % → ≈ 0.49 %).
- n=6 R window: 0.6733687 (H 0.6722203, m 145), beating the 0.673316977 claim.
- ω₀ stays √2, so only numbers change in Lean. At n=7, Σ|c_j| = 0.0681 needs Window's bound raised from 13/200 to 7/100.
- Plan: n=6 R in rootR (window-scope, bridge-port PV, am-cert data); n=7 R7 in rootR7 for the 0.67340 M-test build.
**Correction (window-scope):** computed Σ|c_j|: n=6 R 0.0545, n=7 R7 0.0645. Both fit Window.lean's 13/200 bound (with |v′| ≤ 7/2, |v″| ≤ 78), so no bound needs raising.
R7 is tight (0.0645 against 0.065), so the rational rounding must keep it at or below 13/200.

---
# ACCEPTED (2026-10-03 01:50:34Z): attempt-012 = AM6x, 6733166/10⁷ — RECORD 0.6733166 (ours; +1.49e-4 over typh)
- Board job wall time **1,601 s exactly** (enqueued 01:23:52.8Z with an empty queue; verified 01:50:33.9Z).
- ChallengeDeps 119 s; Solution build **637 s** against 383 s locally (**1.66×**). Post-build plus setup = 1,601 − 760 = 841 s against a local 437 s, so **f ≤ 1.92**.
- The conservative model (157 + 2·build + 2.46·post) projected 1,998 s, so it OVERESTIMATES by ~25 %.
- Refit from the AM6x run: board ≈ 123 + 1.7·build + 1.9·post. Keep the conservative model for go/no-go, but there is ~25 % more real headroom.
**AM n=7 M-test FULL sizing (am-cert, ~02:00Z):** δ 0.2 % (cN 789487, AM13), 200 centres, no basins or chords.
- 21,737 leaves (Z 6,977, S 2,297, M 11,371), all re-verified by an integer replica: 0 failures.
- Tables w 3,968, d 3,528, 3,145 points (n=6-sized). ≈ 1.2 MB certificate.
- Kernel ≈ 100–135 s against ~215 s allowed (projection).
- ENCODING DECISION (lead): bridge-port's compiled AMS02Min (`sleafM`, `covered_of_sleafM`) is the official M-leaf.
  - mvt-engine: confirm or send a diff.
  - bridge-port: writes the walk dispatch.
  - am-cert: matches its replica, does the R6 certificate first, then n=7 on the R7 window.
**Tail tooling (window-scope):** `assemble_am.py --npts N` (n=6 reproduces AM6x byte for byte).
- The n=7 tail was smoke-tested in `bench/window/smokeT7/` with a STUB certificate containing `sorry`. **NEVER upload anything from smokeT7.**
- R7 floor tightened to 67218115/10⁸; at δ 0.1 %, Φ = 0.6734201483 → κ 6734201/10⁷.
- n=7 R7 assembly is a single command once an n=7 certificate exists.
**Target 1: MT eight-point with M-leaves (mvt-engine, ~02:10Z): `SolutionOctM30.lean`, κ 6731889/10⁷.**
- 1.82 MB; 18,100 leaves (Z 4,449, S 882, M 11,686, basin 1, reflected 1,082); 34 basins.
- Private check running (`specroot_octm30`).
- NOT uploadable: below the live record 0.6733166 (ours). It records target 1 ("highest without changing ThmD") and calibrates M-leaf kernel cost.
- mvt-engine's own MinCore (bench/psd) is a second M-leaf implementation; bridge-port's AMS02Min is the official one for AM.
**AM n=7 M-leaf certificate AMM1 GENERATED (am-cert, ~02:15Z):** `AMW.Cert.AMM1_cert_full`, AM13 weights, δ 0.2 %, cN 789487, κ ≈ 0.6734034 (≥ 0.67340).
- 21,737 leaves (Z 6,977, S 2,297, M 11,371, reflected 1,092), all re-verified by the exact integer replica.
- ≈ 1.19 MB.
- Leaf: CMin (a port of mvt-engine's MinCore) + CMLeaf (mtrm, mcheck). Test instance compiled with standard axioms.
- Lean build queued.
- Priority: AMM1 > R7 n=7 upgrade > R6 n=6 (fallback). window-scope prepares the n=7 assembly on root/.
**AMM1 compiled standalone (am-cert, ~02:45Z):** `AMW.Cert.AMM1_cert_full`, standard axioms, Φ = 0.67340339 → κ 6734033/10⁷.
- Data 185 s at 2.69 GB (AMS02's was 587 s); Inst 202 s at 2.24 GB, dominated by elaboration of the generated soundness proofs.
- Projection ≈ 2,700–2,750 s conservative; the real board time is ≈ 0.8× that.
- AM7m.lean (window-scope, 1,828,553 B) is queued for the private check and staging. Lock contention with OctM30: asked mvt-engine to yield.

---
# NEXT UPLOAD (2026-10-03 ~03:20Z): `UPLOAD_AM7m.lean` — 6734033/10000000 = 0.6734033 (≥ 0.67340 TARGET)
**Form:** numerator `6734033`, denominator `10000000`. That is +8.67e-5 over our attempt-012 (0.6733166) and +8.6e-5 over the 0.673316977 claim.
**File:** read-only copy of `bench/window/AM7m.lean`, 1,828,553 bytes, sha256 ebef8b3e8e4ffa88…29dcde.
- AMTOPA-13 window, n=7, certificate AMM1 (21,737 leaves: Z 6,977, S 2,297, M 11,371, reflected 1,092).
- Φ ≥ 0.673403391 at m = 132, cN 789487/10⁸, B 404348/10⁸.
**Checked against the LIVE record 6733166/10⁷** (`bench/specroot_am7m`):
- 0 errors; three theorems [propext, Classical.choice, Quot.sound];
- build 520 s at a 5.02 GB footprint; replay 206 s kernel (4,653 constants).
- Staging running (export done).
**Method:** Weighted seven-point refinement with the AMTOPA window (Theorem D re-proved in-file); certificate with per-term tangent-minorant leaves (LP-mixed tangents on convex regions), pyramid elsewhere (decide +kernel).
**Summary:** Ainta's weighted n-point simple-zero refinement at n = 7, with the Montgomery–Taylor window of the pinned
Zeta23 Theorem D replaced by AMTOPA's window (first 13 cosine terms of zeta-exact-pressure, scaled by 4/5).
Theorem D's window-dependent parts are re-proved in-file:
- admissibility (a certified positive-variation bound);
- zero side and prime side (ported from Zeta23's XiPrime/ThmD, Apache-2.0);
- the a/b/J limits (incl. an exact integral-swap identity);
- the exact constant H = H_MT − Σ c_j²(½ − 1/(4π²j²))/(2 sin²(1/√2)) ≥ 0.6721883;
- the retargeted Zeta Lab bridge (MIT).
The finite certificate has 21,737 leaves on the half-space g₀ ≤ g₅. Each leaf is decided by a zero-order pyramid bound, a slope test, or a
new per-term minorant test: each pair term is bounded below by an LP-chosen convex combination of tangents at grid
points of certified convex regions of w, extended to the whole range by certified derivative bounds. Pyramid table
adapted from five-point-pyramid-2 by typh, centres after six-point-convex-basins-2 by typh (Apache-2.0).
κ = 6734033/10⁷ ≤ Φ = 0.673403391 at m = 132. No new axioms.
**AM7m staging COMPLETE:** export 44 s, nanoda 219 s (4.5 GB), parse ~16 s, closure replay 255 s (2.3 GB). Post-build ≈ 534 s.
- Projection: conservative 157 + 2·520 + 2.46·534 ≈ 2,511 s; calibrated to AM6x ≈ 123 + 1.66·520 + 1.92·534 ≈ 2,011 s. Both under 3,240.
- **FULLY VERIFIED. Upload-ready.**
- R7 follow-up at δ 0.05 % (24,374 leaves, Φ 0.6734227): build queued after AM7m.
**TARGET 1 RESULT (verified locally, ~03:40Z): `SolutionOctM30.lean`, MT eight-point with M-leaves, κ 6731889/10⁷ = 0.6731889.**
- This is the highest κ WITHOUT changing Theorem D (pinned MT window).
- Private check (`specroot_octm30`, record 6731663/10⁷): BUILD EXIT 0 in 746 s, **peak 7.27 GB footprint**; replay 207 s (4,080 constants); export 46 s; nanoda 274 s; closure replay 294 s.
- Not uploadable: below the live record 0.6733166. The 7.27 GB peak would also be risky against the board's 8 GB.
**Eight-point notes (mvt-engine):**
- OctM30 projects ≈ 3,200 s conservative (build 746 s), over budget. Moot, since it is below the live record.
- **OctZ30 recipe**: only Z + M leaves (no slope, basins or centres), direct term proofs instead of linarith.
  - 18,412 leaves (+1.5 %); point table 403 against 6,112 entries; file 1.51 MB against 1.82 MB; instance compile 72 s against 184 s.
  - Being handed to am-cert for the AM n=7 builds.
- At n=8 with the M test, leaf count is insensitive to δ (0.3 % → 0.6 %: 18.4k → 17.5k).

# typh LANDED (04:12Z): "six-point-optimised-window" 67336943/10⁸ = 0.67336943
- Built on our attempt-012 (credited): AM-form window with c_j re-optimised jointly with the six-point weights.
- H ≥ 0.6721858656, B = 379691/10⁸, c = 746194/10⁸, m = 139, 10,645 leaves; board build 851 s.

---
# UPLOAD NOW (2026-10-03 ~04:30Z): `UPLOAD_AR7.lean` — 6734227/10000000 = 0.6734227
**Form:** numerator `6734227`, denominator `10000000`. That is +5.33e-5 over typh's live record 0.67336943, and above the 0.67340 target.
**File:** read-only copy of `bench/window/AR7.lean`, 1,889,647 bytes, sha256 8770696f7a40b9de…8abaf7.
- R7 window (AMTOPA family, corrections re-optimised for n = 7), certificate AMR7, 24,374 leaves.
- Φ ≥ 0.6734227011 at m = 133, cN 787055/10⁸, B 400000/10⁸, H ≥ 67218115/10⁸.
**Checked against 6733166/10⁷** (`bench/specroot_ar7`); strict improvement is norm_num, so it holds against any record < 0.6734227:
- 0 errors; three theorems [propext, Classical.choice, Quot.sound];
- build 569 s at a 5.26 GB footprint; replay 226 s (4,383 constants);
- export 42 s, nanoda 255 s, parse 17 s, closure replay 290 s (74,787 constants).
**Projection:** conservative ≈ 2,780 s; calibrated to AM6x ≈ 2,230 s. Both under 3,240.
**Fallback:** `UPLOAD_AM7m.lean` (6734033/10⁷), fully verified, also above typh.
**Method:** Weighted seven-point refinement with a re-optimised AMTOPA-family window (Theorem D re-proved in-file); per-term tangent-minorant certificate leaves, pyramid elsewhere (decide +kernel).
**Summary:** Ainta's weighted n-point simple-zero refinement at n = 7, with the Montgomery–Taylor window of the pinned
Zeta23 Theorem D replaced by a window of AMTOPA's form, v(s) = cos(√2 s) + Σ_{j=1}^{12} c_j cos(2πjs) (scaled by 4/5). The c_j are re-optimised jointly with the seven-point weights.
Theorem D's window-dependent parts are re-proved in-file:
- admissibility (a certified positive-variation bound);
- zero side and prime side (ported from Zeta23's XiPrime/ThmD, Apache-2.0);
- the a/b/J limits (with an exact integral-swap identity);
- the exact constant H = H_MT − Σ c_j²(½ − 1/(4π²j²))/(2 sin²(1/√2)) ≥ 0.67218115;
- the retargeted Zeta Lab bridge (MIT).
The finite certificate has 24,374 leaves on the half-space g₀ ≤ g₅. Each is decided by a zero-order pyramid bound, a slope test, or a
per-term minorant test: each pair term is bounded below by an LP-chosen convex combination of tangents at grid points
of certified convex regions of w, extended to the whole range by certified derivative bounds. Window family from AMTOPA
(zeta-exact-pressure); pyramid table adapted from five-point-pyramid-2 by typh, centres after
six-point-convex-basins-2 by typh (Apache-2.0). κ = 6734227/10⁷ ≤ Φ = 0.6734227011 at m = 133. No new axioms.
**TARGET 1 in budget (mvt-engine, ~04:35Z): `SolutionOctY30.lean`, MT n=8, κ 0.6731889**, 1,423,350 B.
- Build 319 s, replay 175 s, export 43 s, nanoda 265 s, closure 256 s. Projection ≈ 2,222 s conservative.
- Recipe: Z+M leaves only; term proofs and linear_combination in place of linarith (instance 184 → 34 s); coarse tables (w 992, d 832 cells).
- OctX02 (32-unit tangent grid, δ 0.02 %, κ 0.6732016, near the MT n=8 ceiling 0.6732021) is generating.
- Not uploadable (below the live record).
**Next rung for target 2:** AM-family window at n=8 (AMTOPA-13 ceiling 0.6734398; R8 re-optimised to come), using the OctY recipe. window-scope: R8 window. mvt-engine: AM n=8 sizing.
**n=8 on the R7 window (window-scope, ~04:40Z): ceiling 0.6734508** (B 0.0040435, m 132), +1.1e-5 over AMTOPA-13 at n=8 and +2.8e-5 over AR7.
- R7 is admissible as is, so AM n=8 can be sized and built on the existing rootR7 layer (mvt-engine).
- R8 constrained re-optimisation is running (|v″| ≤ 78 is binding; K > 12 would need Lean layer changes, measuring first).

# TARGET 1 FINAL (2026-10-03 ~05:30Z): highest κ WITHOUT changing Theorem D = 0.6732016
- `TARGET1_OctX02.lean` (read-only copy of SolutionOctX02.lean): MT window n=8, M-leaves on a 32-unit tangent grid, δ 0.02 %, κ 420751/625000 = 0.6732016 (Φ 0.6732016855; n=8 MT ceiling ≈ 0.6732021).
- 1,541,998 B. 20,954 leaves (Z 4,187, M 15,575, reflected 1,192).
- Private check against 6731663/10⁷: build 377 s, replay 215 s, standard axioms. Export 44 s, nanoda 320 s, closure 329 s. Projection 2,655 s conservative (in budget).
- Not uploadable: below the live record (typh 0.67336943).
- Ladder on the MT window (all verified): SevW25P 0.6730423 (accepted) → SevW30S 0.6731541 (accepted) → SevW03D 0.6731663 → OctY30 0.6731889 → OctX02 0.6732016.
**R8 window (window-scope, ~06:00Z): n=8 ceiling 0.6734703** (robust 3-seed floor). That is +3.05e-5 over AM13 at n=8, +1.95e-5 over R7 at n=8, and +4.8e-5 over AR7.
- H = 0.67216841, eps 804628/10⁸, m = 131. Φ: δ 0.05 % → 0.6734678; δ 0.1 % → 0.6734652.
- Fits the current Lean constants: Σ|c_j| 0.064605/0.065, |v″| 77.24/78, PV 0.04406/0.045.
- K=16 and relaxed constants do not help.
- Plan:
  - rootR8 built now with try1 (window-scope);
  - evaluator stack in rootR8 (bridge-port);
  - n=8 sizing (mvt-engine) and generation and build (am-cert);
  - target κ ≈ 0.673466.
**TARGET 1 FINAL, updated: `TARGET1_OctW01.lean`, κ 6732021/10⁷ = 0.6732021** (Φ 0.6732021376), i.e. the MT n=8 ceiling.
- 1,531,312 B, sha256 ff15c890…58e4. δ 0.01 %, 19,384 leaves; two-grid tangent points (256/32-unit), 1,175 points.
- Build 398 s, replay 202 s, export 44 s, nanoda 299 s, closure 285 s. Projection 2,535 s conservative. Standard axioms (lead-verified build log).
- Supersedes OctX02 as the target-1 answer.
**AM n=8 on R8 try1 sizing (mvt-engine/am-cert, ~06:40Z): over 160k leaves, still running; ≈ 10× over budget.** MT8 (OctW01) needed 19.4k.
- δ-independent (a δ 1 % probe ran at the same pace), so the leaves are in the bulk.
- Cause: the bulk region volume ∝ (cN − 0.8Σb)⁷/∏b. R8's ratio (cN − 0.8Σb)/cN is 0.598 against MT8's 0.544, i.e. 5.3× the volume. Its median margin is also lower.
- Lever: a pressure-heavier LP (larger B). window-scope is running a B-scan (0.0044–0.0056+) for ceiling against the volume proxy; mvt-engine sizes the best points, killing at 30k.
- Build only if κ ≥ AR7 + 5e-6 and leaves ≲ 25k.
**n=8 R8 Pareto (window-scope, ~07:15Z), δ 0.1 %:**
- B 0.0044 (β 0): 3.45× MT8 proxy, Φ 0.6734546.
- B 0.0044 (β 0.75): 2.83×, Φ 0.6734481.
- **B 0.0046 (β 0.8): 2.31×, Φ 0.6734323**: the best gated point, ≈ 44k leaves predicted by the 19k×proxy rule.
- Final R8 try1 sizing (mvt-engine): 203,262 leaves (10.5× MT8; 125k of them at margin > 100 %).
- All three front points are being sized by mvt-engine. Build only if ≲ 25k leaves at κ ≥ 0.6734277; am-cert is on HOLD.
- The `--npts 8` smoke test passes in `bench/window/smokeT8/`, a STUB with `sorry`. **NEVER upload anything from smokeT7 or smokeT8.**
**n=8 B-front sized (mvt-engine, ~07:30Z): all four points > 40k leaves.** Even B 0.006 (region ≈ MT8's, κ below AR7) needs > 2× MT8's 19k, so the volume proxy was wrong.
- Kernel diagnosis: AM w is 15–20 % lower on x ∈ [2, 4], its zeros sit irregularly off the integers, and the bulk 0.1 % margin quantile is 1.04 cN against MT's 1.53 cN.
- am-cert's kernel-swap control (MT kernel at R8 weights, volume-normalised, pre-registered: ≈39k ⇒ weights, ≈20k ⇒ kernel) is running.
- Window-side lever on HOLD. mvt-engine is testing engine-side levers on two root boxes.
- Unless those show a large gain, **AR7 (0.6734227) is the top rung of the current method**.
**n=8 DIAGNOSIS CLOSED (am-cert, ~07:45Z).** Controls at R8 weights:
- MT kernel at its own δ 0.1 % (cN 703475): 13,945 leaves.
- AM kernel at the same cN 703475 (δ 12.6 %): 9,405.
- AM at cN 803824 (δ 0.1 %): 203,262.
- Ideal cells against integer AM cells on the same 8 tiles: −3 %.
- Conclusion: leaves are driven by c relative to B, not by the AM kernel or the evaluator (the first control's "×2.8 kernel" reading was an artefact of comparing each kernel at its own minimum).
- The AM window's larger minimum pushes the face Σbg = c outward: volume ×5.16 plus a thinner bulk near the face.
- The κ gate caps B ≈ 0.0047, so B alone reaches ≈ 2.4×, not the needed ~8×.
- Statement about THIS method (zero-order + per-term minorants over the simplex), not about n=8. A further rung needs a new bulk argument, e.g. a dedicated certificate for the face region where all gaps are large and only far-field w matters.
- **AR7 (0.6734227) is the top rung of the current method.**
**Corrections and final n=8 measurements (~08:05Z):**
- am-cert RETRACTS "B 0.0040 → 0.0047 shrinks the domain only 2.4×" (it omitted the 1/∏b factor; ≈ 5–7× is unchecked).
- The B-lever verdict rests on MEASUREMENT: mvt-engine sized the best gated point (B 0.0046, β 0.8) at > 40k leaves (cap). B 0.0052/0.0056/0.0060, all below the κ gate anyway, were also > 40k.
- Engine levers (mvt-engine, roots 4 and 17): finer tables −4–5.5 %; 16-bit λ −0.5 %; 17 tangent positions −24 %; 33 positions −27 %; best ≈ −27 %. Full run ≈ 148k, still ≈ 7× over.
- Leaves at margin > 100 %: 125k of 203k. Per-term minorants are weak over wide pair-sum ranges that cross w's zeros.
- Next idea (not designed): a JOINT bulk test using that several w-terms cannot all be small at once.
- AR7 stays the top rung of the current method.
**n=8 B-front FINAL (mvt-engine, ~08:10Z).** Two-root sizing (roots 4+17 = 11.45 % of try1; it reproduces try1 exactly) gives estimated totals:
- B440000 ≈ 102k (Φ 0.6734546);
- B440000_f0.75 ≈ 113k;
- B460000_f0.8 ≈ 86k (Φ 0.6734323).
- Curve: leaves halve per ~2–3e-5 of Φ, so ~25k would land near Φ 0.67342, below the gate 0.6734277.
- **No gated point fits. AR7 stays the top rung.** The window-side lever (needs ~4×) is untested and HELD.

# typh LANDED (2026-10-03 10:38Z): "seven-point-optimised-window" 67342981/10⁸ = 0.67342981, which BEATS our (unuploaded) AR7 0.6734227
- Built on our attempt-012 AM layer and our attempt-010 seven-point engine (credited), with the window re-optimised at n=7.
- H ≥ 0.6721710925, B 398386/10⁸, c 787320/10⁸ (δ 0.01 %), m 133, Φ ≥ 0.6734298129.
- "Kernel-cheaper evaluator (same values) and faster soundness proofs": 72,455 leaves in budget (board build 777 s). His per-leaf cost is several times lower than ours.
- typh is at 3/3 uploads for 10-03 (next slot 00:00Z 10-04). Sam has 2 left.
- **AR7 and AM7m are now OBSOLETE (below the record).**
- Plan:
  - port typh's cheaper evaluator (am-cert, bridge-port; credit typh);
  - re-optimise the window globally from typh's start (window-scope);
  - re-size n=8 and n=7 under the cheaper cost with our M-leaf, which typh doesn't have (mvt-engine).
  - Gate: κ ≥ 0.6734299.
**COUNTER PLAN (~15:40Z):** "AT7" = n=7 on typh's window (credit typh), our M-leaf, cN 787400 (δ 1.4e-5; m jumps to 133). κ = 6734303/10⁷ = 0.6734303, +4.9e-7 over typh.
- ≈ 25.4k leaves; ≈ 2,550 s projected with our current engine.
- Roots and owners: rootT (window-scope) → evaluator re-key (bridge-port) → certificate (am-cert) → assembly, check against 67342981/10⁸, stage (window-scope).
- In parallel: bridge-port ports typh's evaluator speedups and measures per-leaf cost. n=8 on R8 needs ≤ ~2 ms per leaf (B 0.0044 ≈ 102k leaves, κ ≈ 0.6734546).
- n=7 window search: typh's window is a local max (ridge max ≈ +2e-7); no better start found.
**INCIDENT (reported by bridge-port, ~15:45Z):** bridge-port used `bench/window/rootT` as scratch (15:02–15:28Z), overwrote am-cert's typh-port test files there, then `rm -rf rootT`. Only am-cert's test port was lost.
- Lead verified that all UPLOAD_*/TARGET1_* files are intact (hashes match) and that root/rootR/rootR7/rootR8 are intact.
- The typh-window layer is renamed to `rootTW`.
- House rule (all agents): check that names are free; never rm -rf anything not self-created; never touch UPLOAD_*/TARGET1_*.
**typh engine measured (am-cert, ~16:00Z):** his CEngine/GFar/GBase on our AMR7 data is only **8–14 % faster** (walk 208 s against 226 s; Data type-check 264 s against 308 s).
- His 72,455 leaves: Z 23,589, slope 28,254, centre-slope 18,032, basin 222, reflected 2,358. NO M-leaves. The low per-leaf average comes from the leaf mix.
- n=8 on R8 needs ≤ ~2 ms per leaf against our ~9 ms, so it stays infeasible. The rootR8f port is cancelled.
- Counter = AT7 only.
**AT7 config FINAL (mvt-engine sizing, ~16:10Z):** n=7, typh's window (rwin_typh7_n7_B398386), **cN 787380, κ 6734302/10⁷** (Φ 0.6734302017, m 133), +3.9e-7 over typh.
- 25,452 leaves (Z 5,445, M 18,170, reflected 1,837), 2,132 points (two-grid GSH 4), 0 stuck boxes.
- Projection ≈ 2,530 s (point cost is the uncertain term).
- cN 787400 (κ …303) does NOT size: the near-minimum margin of ~1e-7 is below the tangent error.
- m-jump table (lead-checked, exact): m = 133 is allowed for cN ≤ 787401; Φ(787401) = 0.6734303378; Φ(787402, m=132) = 0.6734298902.
- Owner: mvt-engine (generation + build). AM substitutions from am-cert. Layer `rootTW` (window-scope); evaluator re-key (bridge-port).
**Per-leaf kernel costs (am-cert, profiler regression on 48 AMR7 chunks):** typh engine against ours: Z 1.74/1.86 ms, S 6.38/6.98 ms, M 7.27/8.34 ms. Median ratio 0.92, so ≈ −10 %.
- typh's file walk ≈ 336 s of kernel (2.6× AR7's), still under the board limit, so the real budget is roomier than our model.
- n=8 best (≈ 86k leaves) ≈ 530 s of walk even on his engine: infeasible. Closed.
- typh's CEngine + unrolled GCell go into AT7's rootTW (credit typh). No AR7 rebuild (obsolete).
**ERRATUM (comment text only; found by window-scope, ~16:10Z):** assembler headers printed decimals with round-half-up.
- AM6x (accepted as attempt-012) says "Φ ≥ 0.673316603"; the exact Φ is 0.67331660298… (overstated in the 10th digit).
- AR7 (never uploaded) says "H_W ≥ 0.6721812"; the proved floor is 67218115/10⁸ = 0.67218115.
- No theorem, proved floor, or κ claim is affected: candidateKappa 6733166/10⁷ ≤ Φ is proved in Lean.
- assemble_am.py now prints exact or truncated decimals. AT7's header will be correct.
**rootTW state (lead-verified, ~16:35Z):** typh's GCell/GBase/GFar verbatim (his coefficients = rootTW's), plus OUR original CEngine (unported; cmp-identical to root/AMW).
- Chain GIv…CMinX rebuilt cleanly by the lead; CJ_val/fsum_CE standard axioms.
- Decision: build AT7 on this as is. The CEngine swap was skipped; AT7 projects to fit without it.
- Note: am-cert states it did NOT run port_typh.py in rootTW. The 09:26-local run's origin is unclear (bridge-port saw it during its edit window). Resolved by the lead's clean rebuild.
**AT7 header credits (~16:55Z):**
- AT7.lean's header wrongly credits "convex basins and centres after six-point-convex-basins-2" (AT7 has none), and omits typh's verbatim GCell/GBase/GFar.
- Fix: AT7c.lean, header-only diff. It adds the evaluator-module credit to typh and the MinCore/minorant leaf description.
- Upload AT7c after a build-only compile against the live record. The proof text is identical to the checked AT7.lean.
- The same basin-credit slip is in the unuploaded AR7 and AM7m; nothing on the board is affected.

---
# UPLOAD NOW (2026-10-03 ~17:15Z): `UPLOAD_AT7c.lean` — 6734302/10000000 = 0.6734302 (+3.9e-7 over typh's 0.67342981)
**Form:** numerator `6734302`, denominator `10000000`.
**File:** read-only copy of `bench/window/AT7c.lean`, 1,837,980 B, sha256 65564079527487fd…f3b7d4. The body is byte-identical to AT7.lean (fully staged); only the header credits differ.
**Math:** n=7 on typh's seven-point-optimised-window (coefficients by typh), LP weights re-solved, B 398386/10⁸, cN 787380, m 133, Φ ≥ 0.6734302018 (H ≥ 67217109258/10¹¹). Certificate AT7: 25,452 leaves (Z + per-term minorant), 2,132 tangent points.
**Checks against the live record 67342981/10⁸:**
- AT7: 0 errors, standard axioms; build 364 s at 5.64 GB; replay 198 s; export 46 s; nanoda 276 s; closure 269 s. Projection 2,378 s conservative (≈ 1,900 s calibrated).
- AT7c build-only: 0 errors, standard axioms, 362 s at 5.67 GB.
**Method:** Weighted seven-point refinement on typh's re-optimised AM-form window (Theorem D re-proved in-file); per-term tangent-minorant leaves plus pyramid zero-order leaves, decide +kernel.
**Summary:** Ainta's weighted n-point simple-zero refinement at n = 7 on the AM-form window v(s) = cos(√2 s) +
Σ_{j=1}^{12} c_j cos(2πjs), with typh's seven-point-optimised-window coefficients (Apache-2.0) and the seven-point weights
re-solved by LP (B = 398386/10⁸). Theorem D's window-dependent parts are re-proved in-file (attempt-012's layer:
admissibility, zero and prime sides, the a/b/J limits with an exact integral-swap identity, the exact constant
H ≥ 0.67217109258). The finite certificate (25,452 leaves on g₀ ≤ g₅, the rest by reflection) uses zero-order pyramid leaves and a
per-term minorant test: each pair term is bounded below by an LP-chosen convex combination of tangents at grid points of
certified convex regions of w, extended by certified derivative bounds. It sits at the m-step of the bound (m = 133, c just below
1/127). Credits: the window coefficients and the GCell/GBase/GFar evaluator modules from typh's seven-point-optimised-window; the
pyramid table from typh's five-point-pyramid-2 (Apache-2.0); the window family from AMTOPA (zeta-exact-pressure); Zeta23 (Anthropic,
Apache-2.0); the Zeta Lab bridge (MIT). κ = 6734302/10⁷ ≤ Φ = 0.6734302018. No new axioms.
**n=8 REOPENED (bridge-port, ~17:15Z): mleafC prototype.** The same leaf word, evaluated as chained per-term steps; κ=0 terms take a plain lb path.
- In-walk M cost 5.7 → 2.6 ms; all 32 AMT8 walks reach identical end positions.
- Soundness is in progress (≈ a few hours).
- Levers toward ~2.0 ms: a coarser constant-term cover (to be sized) and a leaner accumulator.
- mvt-engine is recomputing n=8 projections at 2.6 / 2.0 ms and generating if a point fits.
- Gate: ≥ AT7c + 5e-6.
**n=8 PARKED again (mvt-engine, ~17:25Z): the 2 MB file cap.**
- Walk payload ≈ 140 bits per leaf at n=8 (AT7: 117 bits per leaf at n=7). With the AM layer ≈ 0.67 MB and tables ≈ 0.25 MB, the cap allows ≈ 27–30k leaves.
- R8 B440000 ≈ 102k (3.5× over); B460000_f0.8 ≈ 86k (3×).
- Coarser constant-term cover: +4.4 % leaves (one level), +19 % (two levels).
- mleafC (2.6 ms) fixes time, not size. Unblocking needs ≈ 3× fewer leaves (a joint bulk test) or a much denser leaf encoding.
- mleafC soundness is paused; the prototype is kept (bench/window/MLEAFC.md).
- **AT7c (0.6734302) is our board move.**
**mvt-engine final n=8 table (17:21Z; it now includes the +4.4 % for the shift-4 cover):**
- B440000 ≈ 106k leaves, ≈ 4.1 MB, P ≈ 3,000 / 2,640 s at 2.6 / 2.0 ms per M leaf.
- B440000_f0.75 ≈ 118k leaves, 4.5 MB.
- B460000_f0.8 ≈ 90k leaves, 3.6 MB, below the gate.
- try2 ≈ 212k leaves, 7.4 MB.
- Time model calibrated on AT7: P ≈ 814 + 7.9·K, where K is kernel seconds. It flatters large files (assumes elaboration doesn't grow with size).
- Verdict unchanged: the 2 MB cap blocks all four. Nothing generated. AT7c stays the move.
**bridge-port M-leaf follow-up (~17:30Z):**
- mleafS (mscheck's exact accumulator form) ≈ 2.9 ms in-walk. Its soundness is mechanical (step lemmas → mscheck_sound).
- mleafC ≈ 2.6 ms in-walk; needs no-overflow lemmas.
- 2.0 ms not reached. The floor is the 22 pyramid reads, ≈ 1.6 ms.
- Shift-4 constant cover: −7 % time, 60/60 sampled leaves pass. Shift 3: 4/60 leaves fail.
- Decision: no soundness work. n=8 is size-bound (2 MB) regardless of leaf speed. bridge-port is told to write up mleafS in MLEAFC.md and go idle.

## 2026-10-03 ~18:30Z — n=8 REOPENED: polytope cells (splits on pair distances)
Diagnosis:
- Control: the MT n=8 exact-minimum oracle (bench/eight/d8_true.log) needs 32 leaves, i.e. the roots alone.
- So the leaf count measures how weak our per-box test is, not the geometry.
- Long pair terms (up to 7 gaps) must sit inside one lobe of w. Gap boxes achieve that only by narrowing every gap.

Prototype bench/eight/am8/psum8.py (floats, sizing only), B440000 roots 4+17, δ 0.1 % (production 11,693):

| variant | leaves |
|---|---|
| pair splits, 9 tangent positions | 6,000 |
| pair splits, 17 / 33 / 65 positions | 2,858 / 1,892 / 1,733 |
| dense tangents / exact convex hull | 1,434 / 1,326 |
| 33 positions, no sum rows in the LP | 7,059 |
| 33 positions, no tightening | 3,480 (1,555 empty) |

- The gain needs pair splits, about 33 positions, and multipliers on the explicit sum constraints in the leaf's dual, together.
- Projection: about 16.5k leaves on the full run, before realism penalties.
- Dispatched: mvt-engine (faithful sizer size8pz.py, go gate: 2 MB and P ≤ 2,700 s) and bridge-port (Lean design for polytope cells, PCELL.md, toy instance).
- Sam's trivial-zeros question: in this pipeline they enter only via the archimedean term of the explicit formula (Γ′/Γ = sum over the trivial zeros), which sets the zero density. That is the gap unit, a common mode already exact in every leaf.
- Not uploaded material: keep polytope cells sealed until used.
**~18:50Z follow-ups:**
- Leaf speed: mleafS is PROVED (bridge-port; ≈ 3.0 ms per M leaf in-walk, drop-in for mleafN, standard axioms).
- Real R8 M payload ≈ 200 bits per M leaf (mvt-engine). The repeat-bit code gives 1.2× (the 2.6× was an AMT8 artefact).
- Reference-point leaf (g_ref, derived tangents): ≈ 7.3k leaves against 1,892 → dropped.
- Polytope leaves need ≈ 3.5 nonzero sum multipliers each.
- Size math: 16.5k × ≈ 265 bits ≈ 1.09 MB hex + 0.92 MB ≈ 2.01 MB. At the cap, so a denser literal is needed. am-cert is measuring the kernel cost of base64 String decoding.
**~19:05Z am-cert: String/base64 walk literals NOT viable in the v4.33 kernel.**
- Literal expansion is quadratic in length: 667 chars take 25 s at 7.3 GB.
- Chunked strings cost ≈ 250 s per MB.
- Hex stays.

Byte map of AT7.lean (1.84 MB):
- AM layer 0–366 KB (incl. Zeta23Ext bridge 140 KB);
- typh evaluator modules 146 KB;
- CEngine 115 KB (incl. slope 24 KB and basins 26 KB);
- CMin 27 KB;
- AT7Inst 123 KB;
- AT7Data 1,047 KB (walks 741 KB);
- tail 12 KB;
- comments 61 KB in all.

So the n=8 walk budget is ≈ 0.8–0.9 MB hex unless the non-walk bytes are cut (am-cert auditing). At 200–265 bits per leaf that is 13–17k leaves.
**~19:20Z am-cert byte audit (bench/window/bbaudit, exact dependency closure from the compiled AT7 olean):**
- Safe cuts (dead decls 60 KB, incl. 39 KB of CEngine slope/MVT; comments ≈ 61 KB; halved indentation): walk budget ≈ 990 KB hex at n=8.
- Adding the PT3B coarse/fine split (−55 KB) and generic instance proofs (−60 KB): ≈ 1,105 KB.
- At ≈ 66 hex chars per polytope leaf (200 payload bits + multipliers) that is 15.0k / 16.7k leaves. Float projection: 15–16.5k.
- mleafS as generated costs +287 KB, so it's shelved for n=8; mleafN is fine on time at these counts.
- am-cert is building the minifier and proving it on an AT7c copy.
**~19:40Z bridge-port PCELL design (bench/window/PCELL.md):** compiles at Q=3 with standard axioms.
- Pieces: Covered′, the sum split for any q, mcheckP/mleafP with multipliers (MulOK invariant), the empty leaf, and FBBT (Jacobi; soundness fb_t_sound). Generator amg/genpcell.py also emits Q=7.
- Costs: the wide state adds +0.1 ms per node and one FBBT round +2.7 ms per node. At ≈ 17k leaves that is 40–190 s, so kernel time does not bind.
- Multiplier entry is 19 bits. Kind-7 (LP-infeasible) cells go via a multiplier/Farkas leaf.
- Waiting on mvt-engine's integer sizing for go/no-go.
**~20:00Z mvt-engine faithful pair-split sizer (size8pz.py):**
- Roots 4+17: 2,657 leaves (pf K=8, 33 positions, WMIN 8) against box-mode 11,693, i.e. 4.4×. Faithful counts run ≈ 1.4–1.6× the float prototype.
- Full projection: ≈ 23.2k leaves (18.8k M), walk ≈ 1.29 MB hex, points 6–10k (sparse ≈ 0.2 MB). File ≈ 2.45–2.55 MB, so NO GO as specified.
- Time: P ≈ 2,200–2,700 s at 2.9 ms.
- Levers ordered:
  (1) per-term prefix-coded payload: static entropy 117.5 against 238 bits per M leaf, file ≈ 1.9–2.0 MB;
  (4) lighter point (δ 0.3 % or B between 440k and 460k, Φ ≈ AT7c + 1–1.5e-5);
  (3) guarded K=16 split rule.
- Next: (1) and (4) in sizing; no Lean yet.
**~20:15Z am-cert safecut PROVED on an AT7c copy (bbaudit/safecut.py):** 1,837,980 → 1,714,106 B (−124 KB; dead decls −57 KB, comments −57 KB, indentation −9.5 KB).
- The dead set comes from the compiled olean (closure of the scored theorems), with a fixpoint for names still mentioned in the text.
- Private check: build 366 s, standard axioms, closure 74,719 constants (same as the original), projection 2,379 s (original 2,378).
- n=8 walk budget: ≈ 970 KB (≈ 14.7k polytope leaves), or ≈ 1,085 KB (≈ 16.4k) with the PT3B split and generic proofs.
**~20:30Z bridge-port PCell3I (rootR8f/AMW/PCell3I.lean):** the end-to-end decide +kernel instance compiles, 13 s, standard axioms.
- Covered: a sum split, tightening on both children, a plain leaf, and a multiplier leaf (bound 553662 → 556579 > cN 550000).
- Tables are empty, so this exercises the path, not leaf strength.
- AMT8 tables don't verify under the rootR8f window: the n=8 build must generate and check tables under the chosen window.
- Lean side is ready to generate; holding for mvt-engine's lever results.
**~20:45Z bridge-port PCELL byte cost:**
- The Q=7 polytope instance as emitted is 481 KB (splits 177, FBBT 88, multipliers 87, leaf 73, …) against 146 KB for the box instance. The cause is the 56-variable curried state restated in every lemma.
- GO given on the reducers, a precondition for any n=8: drop covered_empty_t, a cell structure in the propositions, per-(i,j) parametrized lemmas. Target ≤ 146 KB.
- AMT8 tables belong to rwin7/rootR7.
- SIG is now a per-certificate def (SIGSH 14).
- Kind-8 (Farkas) leaf designed, not built.
**~21:00Z mvt-engine size8pz under kernel semantics (Jacobi NR 2; empty cells 0 bits; 6-bit splits; multiplier list):**
- Variant A on roots 4+17 = 2,768 leaves (2,235 M, 391 Farkas, 105 refl, 33 Z, 4 emptied), 226 bits per leaf.
- Multiplier quantum 2^-14 / 12-bit is the minimum (2^-12 gives +43 %).
- ≈ 13 % of leaves are LP-infeasible cells that tightening misses, so a Farkas leaf is required.
- Full projection: ≈ 24.2k leaves, walk 1.36 MB HEX. Base64 is not available (am-cert), so it is over by ≈ 0.4 MB.
- Mandatory: lever 1 (decodable per-term code, −30–40 %). Pending: lever 4 (lighter point).
- Time at mleafN 5.5 ms: P ≈ 2,250–2,700 s (points 50–110 s are the next term).
**~21:30Z mvt-engine lever results:**
- Lever 1: joint per-term canonical Huffman over (kind, j1, j2) plus 9-bit λ gives 140.9 bits per M leaf (from 231.5); whole walk 152.6 bits per leaf (from 225.7).
- B440000 δ 0.1 % in HEX: walk 0.92 MB + non-walk ≈ 1.09 MB ≈ 2.01 MB, at the cap. Base64 is not available.
- Lever 4 does NOT help with pair cells: δ 0.3 % gives 3,480 and f0.75 gives 4,304, against 2,768. B440000 δ 0.1 % is the best κ AND the smallest certificate.
- Time at mleafN: P ≈ 2,100–2,250 s.
- Margin (60–100 KB) to come from: λ precision, Huffman-coded split/multiplier fields, guarded K=16, generic proofs/reducers.
- Full 32-root run in progress (checks the ×8.73).
- Next: mvt-engine writes HUFF.md (bit-exact spec + golden vectors); bridge-port builds the kernel decoder after the reducers.
**~21:50Z bridge-port reducers DONE:**
- Q=7 polytope layer is 136.8 KB in all (instance 104.6 KB + generic PCellCore/PCellGen 32.2 KB), from 492 KB. With the root cover ≈ 170 KB.
- Q=7 compiled (PCellT7.lean, 27 s, standard axioms). Wide state costs +0.006 ms per node; one FBBT round +2.72 ms.
- GO given on the remaining Lean pieces: Farkas leaf, degenerate/PLO/gptF details, all-constant M leaf in place of a Z leaf, root cover, generic leaf proof, Huffman decoder (against HUFF.md).
- Budget: non-walk ≈ 1.04 MB + walk ≈ 0.92 MB ≈ 1.96 MB hex, before the remaining margin cuts.
**~22:20Z bridge-port items 2–5 DONE:**
- Degenerate/PLO/gptF, no Z leaf (all-constant M), generic leaf proof PCellLeaf (16.4 KB), generic root cover PCellRoot (10.1 KB).
- Q=7 polytope layer 147.4 KB raw incl. root cover, against 146.2 KB for the box instance. Standard axioms at Q=3 and Q=7.
- Costs: mleafP 10.87 ms against mleafN 9.55 ms standalone (+14 %). FBBT +2.44 ms per node per round over all 21 constraints.
- TIME NOW BINDS through FBBT: ≈ 48k nodes × 4.77 ms (NR 2) ≈ 230 s kernel, not in mvt-engine's P.
- Fix in progress: a mask-bit loop over explicit constraints only (exact, since non-explicit constraints cannot tighten), NR=1 sizing, and possibly an mleafS-style generic step leaf.
**~22:45Z FULL 32-root run (mvt-engine), B440000 δ 0.1 %, pair cells:**
- 41,531 leaves (M 33,034, Farkas 6,040, refl 1,567, Z 860, empty 30); 41,499 splits; 4,135 points. 0 verification failures.
- 2.5× over box mode (≈ 102k), NOT 4.4×: roots 4+17 were favourable, so ×8.73 understated.
- Joint Huffman 135.5 bits per M leaf. Walk 1.56 MB HEX, file ≈ 2.6 MB → NO GO. Time at mleafN ≈ 2,800–2,900 s before FBBT → over.
- Leaves are spread over roots (top 3 = 25 %).
- Needed: ≈ 1.5× more on the walk, plus the faster leaf.
- Diagnostic dispatched: ablation of the float→faithful 2.1× leaf-test gap, and Farkas cells catchable by stronger propagation.
- AT7c remains the move.
**~23:30Z (AT7c uploaded by Sam, in verification). Split-rule finding (lead, size8pzb.py copy, BSPLIT=1 = pf may split at the convex-region boundary nearest the midpoint; +1 bit per split):**
- Root 4: 1,485 → 828; root 5: 3,452 → 1,099; root 9: 2,296 → 1,602; root 0: 294 → 123 (DLO 8/9).
- At default DLO: root 4 1,441 → 1,260, root 9 2,132 → 1,681.
- Leaf counts swing ±50 % with heuristic details (also 65 positions and larger δ came out worse). The split rule is a major lever.
- Full 32-root BSPLIT runs launched (pzbfull_c89, pzbfull_d56).
- mvt-engine asked for a per-root portfolio driver (min tree per root over kernel-computable split-rule variants).

# ~00:00Z 10-04: AT7c VERIFIED, rank 1 on the board (67.3430200000 %). New target from Sam: κ > 0.6734765075 (not on the board yet when checked).
- That is ABOVE our R8 n=8 window ceiling (try2 Φ 0.6734738 at δ 0, m 131) by 2.7e-6, and +4.6e-5 over AT7c.
- Needs a better window/weight point AND a certificate at higher pressure than B440000 (which itself doesn't fit yet).
- window-scope dispatched: relaxed layer constants (S1, |v″|, PV active), m-step, free ω₀, lower B, n=9 estimate, typh-window start.

# ~00:30Z 10-04 TARGET κ > 0.6734765075: Gebendorfer, "Compatible triples and a periodic-mixture obstruction" (7 Sep 2026; ChatGPT/Codex; Arb/C++ certificates, NOT Lean). Copy in refs/.
- Same Zeta23 clipped-Gram framework as ours.
- Its gain over our Ainta n-point bound:
  (a) AMTOPA's band profile (Lemma 3.3): tr Φ(G) ≥ G_m(E_band), τ = (q+1)/q, with a √ branch. Our bridge has the τ = 1 case (block_defect: min 1 ≤ defect), hence hA0.
  (b) Nine 7-point functionals with different pressure vectors, combined in a polyhedron.
  (c) Block m = 526.
  (d) Three overlapping windows (+3e-7).
- Class cap 0.674034 for their 25-mode affine-pressure clipped-Gram class.
- Our numbers:
  - AT7c certificate + profile (linear τ=7/6, m 154): 0.6734384; full √ profile: 0.6734389.
  - n=8 try2 + profile: 0.6734783 (no certificate yet).
  - Proportional-pressure 2-D aggregation model on our window with their ε ratios: base + 1.6B 0.6734731, all nine 0.6734750. Re-optimisation is needed.
- Track 1 (bridge-port proves the profile; am-cert integrates and re-assembles AT7 at m=154): board κ ≈ 6734383/10⁷.
- Track 2 (window-scope): optimise the window and functionals for the aggregated objective, target ≥ 0.6734780.
**~00:45Z:**
- window-scope's n=8 interim (old task): relaxing PV/|v″|/S1, a free ω₀ and the typh start all give ≤ +6e-7 over R8's 0.6734738; m-step ≤ 5e-7. The n=8 window ceiling stays ≈ 0.6734744.
- Boundary splits at full scale (c89, 17/32 roots): 1.66× fewer leaves than pzfull, which projects n=8 B440000 to ≈ 25k.
- Machine load hit 81: stopped d56, and asked window-scope and mvt-engine to stop n=8 jobs and run single-threaded.
**~01:00Z Track 1 (am-cert):**
- The τ chain is compiled against a stated `BandProfile` hypothesis (tauint/TauDev.lean): band ≥ windows, block_bound_w'_τ (hA0τ ≤ n/(n−1)), the eventually version (span threshold τ/bmin), pre_solve (3 → 2τ+1), n_point_bound_w'_τ.
- κ exact: m = 154, c·148 = 1.16532 ≤ 7/6, Φ = 0.6734383753 ≥ **6734383/10⁷**.
- AT7T is assembled (placeholder-sorry compile test only).
- Waiting on bridge-port's BandProfile proof.
- Live record = ours, 6734302/10⁷ (board, verified).
**~01:15Z mvt-engine ablation BREAKTHROUGH (roots 4+17, B440000 δ 0.1 %):**
- Faithful tchk rejects 42 % of exactly valid tangents (its derivative-extension condition). Exact validity: 2,768 → 1,079.
- All 6,040 Farkas cells are caught by one pass of pair-sum TRIPLE propagation s_ij = s_ik + s_kj.
- Lever T2 (two triple passes, all 28 pair-sum intervals per node): 1,512, with 0 Farkas leaves.
- Lever Z (zero-order extension: piecewise check of the tangent under the w pyramid where the derivative extension fails, K = 8): with T2 → **497** (5.6× under variant A).
- Full runs going: B440000 and try2 (rwin8, Φ 0.6734686 at δ 0.1 %).
- try2 + τ = 8/7 profile: **0.6734776 (δ 0.1 %, linear), 0.6734802 / 0.6734809 (δ 0.05 %, linear / full)**, i.e. BEATS 0.6734765075.
- Plan: try2 n=8 with T2 + Z (+BSPLIT?) + the profile.
- Lean needed after the profile lemma: the T pass, the Z lemma, the Huffman decoder, plus the pair-cell layer already built.
**~01:40Z bridge-port Huffman decoder DONE:**
- Golden root-15 walk decodes bit-exact (21,281); controls bite; standard axioms at Q=3 and Q=7.
- Leaf cost 1.07× the fixed width with a lookup (K=4 chosen); payload 84 against 158 bits on the AMT8 sample; +3.7 KB generic.
- bridge-port is now on the BandProfile proof (critical path for AT7T), then the T pass and the Z lemma.
- am-cert's run_at7t.sh is ready (assemble → check → safecut → check → stage → freeze UPLOAD_AT7T).
**~02:00Z n=8 GO. Full run (mvt-engine), B440000 δ 0.1 %, T2 + Z8:**
- **4,439 leaves** (from 41,531, 9.4×), 0 failures. HUFF walk **203 KB hex**. Points 1,843.
- P ≈ 1,800–2,000 s (triple-pass kernel cost to be measured).
- T1 with NR=0 suffices.
- Sizer bug (rows emitted for zero-weight pairs) voids earlier pair-mode results for B460000/B470000/try2. B440000 is unaffected. Fixed; try2 is re-running.
- Plan: try2 (rwin8) + τ = 8/7 profile at δ 0.02–0.1 % → κ 0.6734776–0.6734813 (linear), above 0.6734765075.
- Owners:
  - mvt-engine: try2 full run, TZ.md spec, certificate data;
  - bridge-port: BandProfile → T1 pass → Z lemma → Q=7 generator;
  - am-cert: AT7T pipeline, then the R8 AM layer and run_n8.sh.
**~02:20Z BandProfile PROVED (bridge-port, bench/window/bpprof/PROFILE.lean, 15.2 KB, standard axioms):** `band_profile_holds : BandProfile` (Hermitian G, injective r, τ = (q+1)/q exact; Fenchel via affine_le_Psi + Frobenius; residue-class Cauchy–Schwarz). Handed to am-cert for run_at7t.sh (AT7T, κ 6734383/10⁷). bridge-port next: generic T (triple-interval) and Z (piecewise-line) soundness, then the kernel versions per TZ.md.
**~02:35Z am-cert:**
- AT7T (1,883,659 B, real profile, PROFAX standard) is in run_at7t.sh: check → Dep → safecut → check → stage → freeze UPLOAD_AT7T.
- The R8 AM layer is already proved in rootR8 (all constants, HW_ge 67216841/10⁸); SCOPE §12 is stale.
- The τ chain is generic in n (BrTau, rootR8).
- Exact n=8 R8 linear-branch Φ: 0.6734775521 (δ 0.1 %, m 149), 0.6734801587 (δ 0.05 %), 0.6734812767 (δ 0.02 %, m 148).
- The √ branch is deferred.
- run_n8.sh is ready, waiting on bridge-port's BrProf and the pair-cell Inst/Data.
**~02:50Z GO on n=8 try2 (mvt-engine full runs, final settings T1 + Z8, bug fixed):**
- try2 δ 0.1 % = **5,525 leaves**, 11,015 nodes, 2,240 points; walk 228 KB (Huffman) / 343 KB (fixed).
- B440000 4,750; B460000 4,013.
- File ≈ 1.27–1.38 MB hex; P ≈ 1,600–2,070 s (triple-pass cost to be measured).
- Fixed-width fields chosen (no Huffman). δ 0.05 % / 0.02 % runs in progress; pick the smallest clean δ (κ 0.6734813 at δ 0.02 %).
- bridge-port: BrProf, T1 kernel, Z8, cost measurement, Q=7 generator.
- mvt-engine: TZ.md + golden vectors, emitted data, exact replay verifier.
- am-cert: run_n8.sh.
**~03:00Z window-scope κ_τ (τ = 8/7, mpmath):**
- try2 linear: 0.6734823 (δ 0) / 0.6734802 (0.05 %) / 0.6734776 (0.1 %); with the √ branch +≈ 7e-7.
- B ≈ 0.00404 stays optimal (0.0041 is −9e-7, 0.0042 is −4.6e-6); try1 is worse (−3.4e-6).
- Window re-ascent for κ_τ skipped (< 1e-6). n=9 estimate (R8 window, B 0.0044) still running.
**~03:10Z try2 δ sweep (full runs, final settings, 0 failures):**
- δ 0.1 % = 5,525 leaves; 0.05 % = 5,478; **0.02 % = 5,633** (cN 805003, 2,364 points, walk 354 KB fixed).
- **BUILD try2 δ 0.02 %**: κ_τ (linear, m 148) = 0.6734812767, +4.77e-6 over 0.6734765075.
- File ≈ 1.39 MB.
- Split: mvt-engine (TZ.md, data, replay), bridge-port (T1/Z8 kernel, generator, Inst/Data in rootR8), am-cert (run_n8.sh).
**~03:40Z mvt-engine deliverables DONE:**
- TZ.md + tz_golden.json; DATA_try2_0.0002.json (0.56 MB) — **VOID** (L0 gap, see ~04:10Z; renamed .VOID_L0GAP). Valid input: DATA_try2r_0.0002.json.
- verify8pz.py: an independent replay from DATA alone gives **0 failures**; controls (cN + 2000, bit flips) fail as they should.
- Re-sized with bridge-port's persisted T1 semantics and the Z right-side slope fix: **5,677 leaves**, 11,322 nodes, 2,274 points, walk 341.6 KB hex. File ≈ 1.35–1.4 MB.
- Next: bridge-port's Lean Inst/Data in rootR8 → am-cert run_n8.sh.
**~04:10Z T1 soundness gap fixed (found by bridge-port):**
- The leaf anchor L0 = Σl could exceed the term's L after T1: 653 nodes and 70 leaves relied on it. DATA_try2_0.0002.json is VOID.
- Fix: T1 step 5 re-clips non-adjacent intervals to the written-back gap sums.
- Re-sized DATA_try2r_0.0002.json: 5,676 leaves, 2,262 points, walk 341.2 KB.
- verify8pz: 0 failures; the L0 ≤ L assertion holds; the positive control (70) fires on the void data.
- κ unchanged at 0.6734812767.

# UPLOAD READY (2026-10-04 ~04:30Z): `UPLOAD_AT7T.lean` — 6734383/10000000 = 0.6734383 (+8.1e-6 over the record, ours AT7c 0.6734302)
**Form:** numerator `6734383`, denominator `10000000`.
**File:** 1,754,764 B, mode 444, sha256 491539f6a78ed54fc4625fad4d5a07c8012907998aa0c70cd7b5c6cf6bd1dff3 (safecut AT7TS; lead re-verified the hash, 0 sorry).
**Checks vs 6734302/10⁷:**
- unstripped: build 454 s, replay 260 s;
- stripped: build 478 s at 5.57 GB, replay 255 s, export 45 s, nanoda 327 s, closure 75,119 constants 329 s;
- axioms standard on all three theorems;
- projection 2,836 s conservative (at load ≈ 6; AT7 quiet was 2,378).
**Method:** τ = 7/6 band profile (AMTOPA Lemma, via Gebendorfer 2026 Lemma 3.3) on the AT7 seven-point certificate; band bound proved in-file, c(m−6) ≤ 7/6 at m = 154 (decide +kernel).
**Summary:** as in am-cert's 10-04 message (see bench/window/tauint); credits typh, AMTOPA (MIT), Gebendorfer Lemma 3.3, Zeta23, Zeta Lab bridge.
**~05:00Z bridge-port T1/Z built (rootR8f PCellTZ/PCellZ/PCellLeafZ/PCellT1, genpcell4):**
- Generic soundness (tri_gen, mat_gen, line_le_ends, pieces_cover, tangent_valZ, mcheckGZ_sound), standard axioms.
- Golden: all 10 T1 nodes and all 5 Z checks match.
- T1 costs +4.77 ms per node (≈ 54 s over 11.3k nodes); the Z leaf is 1.08×. Q=7 instance 118.9 KB.
- Next: T1 step 5 (re-clip) + regolden, then try2r Inst/Data in rootR8 + BrProf + CSRC → am-cert run_n8.sh (κ 6734812/10⁷).
**~05:20Z mvt-engine proposed an exact difference-constraint closure in place of T1:**
- ≈ 4× fewer ops; DATA_try2c with 5,651 leaves; verified incremental = from-scratch closure at all nodes.
- DECISION: keep T1 + step 5 (DATA_try2r) for this build, since time to upload matters more. The closure is the fallback if the measured projection is > ≈ 2,600 s, or for n=9.
**~06:00Z bridge-port PC8 BUILT in rootR8:**
- Step 5 is in the kernel T1; all 18 golden checks pass (10 T1 nodes, 3 reclip nodes, 5 Z).
- PC8Inst 113.6 KB (37 s); PC8Data 755 KB (404 s): walks 342 KB, w pyramid 43 KB, d table 84 KB, sparse points 93 KB (per-block ptl lists).
- PC8_cert_full at standard axioms. Assembler dry run: 1.71 MB pre-safecut, m 148, Φ 0.6734812767 ≥ 6734812/10⁷.
- Z costs ≈ 0.1 s in total (40 distinct sides).
- GO to am-cert run_n8.sh (rootR8; credits verified by provenance: the pyramid oracle → typh five-point-pyramid-2; GCell/GBase/GFar by diff).
**~01:20Z 10-04 PC8T pipeline FINISHED: all stages pass with standard axioms, BUT not uploadable yet.**
- PC8TS 1,549,634 B.
- Timings: build 650 s at 7.16 GB, replay 409 s, export 40 s, nanoda 422 s at **8.92 GB** (sandbox 8 GB), closure replay 488 s.
- Projection 3,794 s conservative / ≈ 3,060 s calibrated, against the 3,240 s limit.
- The certificate costs ≈ 330 s of replay against a 100–160 s projection. Suspect: sparse ptl point-list lookups (≈ 70k reads), then T1.
- bridge-port is profiling, will make point lookups O(1), may switch to the closure (trigger fired), and is chasing nanoda memory. am-cert is re-measuring nanoda quietly and holding the freeze.
- AT7T (0.6734383) remains the safe upload.
**~01:45Z bridge-port profile of PC8 (roots 4, 20, variant-drop method):**
- **Z is 36–44 %** of walk time (≈ 115 s of ≈ 310 s certificate replay); T1 ≈ 54 s; derivative reads ≈ 48 s; other leaf ≈ 47 s; decode ≈ 32 s.
- Points are negligible (0.39 s in total); my point-table suspicion was wrong.
- Z runs 6.6–9.5 times per M leaf at 8 reads each.
- Memory: a root's peak scales with its leaf work (root 4: 4.8 GB, Z +1.2 GB).
- Plan:
  - bridge-port: (1) Z fast path 1 → 2 → 8 pieces (kernel only, −55–60 s); (2) subtree split theorems for memory; (3) derivative-read first try.
  - mvt-engine in parallel: closure kernel + soundness (−40 s).
- Targets: certificate share ≤ 180 s, replay ≤ 280 s, nanoda ≤ 2.7e12 instructions.
**~02:10Z Z fast path in (bridge-port; zsideF tries 1 → 2 → 8 pieces, each alternative proved):**
- Walk time −22 %: root 4 21.8 → 17.0 s, root 20 18.3 → 14.3 s, PC8Data build 404 → 315 s, root-4 peak RSS 4.8 → 4.2 GB.
- Certificate share ≈ 310 → 242 s.
- Next: subtree split for memory (bridge-port) → typh engine in rootR8f (bridge-port + am-cert, credit typh) → closure (mvt-engine).
- Estimated share ≈ 150–170 s.
**~02:30Z bridge-port chunked walks (≤ 150 leaves per theorem; boundaries via t1_to / split_to / kEq):**
- 352 chunks, 160 boundaries. Largest-declaration memory 4.59 → **2.78 GB**; PC8Data 755 → 921 KB; raw assembly 1.88 MB.
- With the Z fast path, the certificate replay ≈ 240 s.
- am-cert re-runs as PC8Z (freeze only if the calibrated projection is ≤ 2,600 s and nanoda ≤ 6.5 GB).
- Closure: deconflicting bridge-port and mvt-engine. The other agent does the typh-engine port (rootR8f, PC8F).
**~02:50Z mvt-engine closure kernel BUILT (rootR8/AMW/PCellClose.lean 13.8 KB, standard axioms):**
- cupd one-edge update; no emptiness test needed; 12/12 goldens.
- Per node 2.12 ms against T1's 7.57 ms (≈ −62 s kernel, ≈ −490 board-s by the fit).
- Instance +80 KB (198 KB).
- Next: merge closure + chunking + Z fast path (mvt-engine, PC8 TAG c); bridge-port does the typh-engine port (PC8F) and helps merge.
- PC8b (Z + chunking, T1) is in am-cert's pipeline.
**~03:35Z PC8b (T1 + Z fast path + chunking) pipeline DONE (log run_n8_PC8b.log):**
- Standard axioms. PC8bTS 1,720,289 B.
- Build 568 s at 4.85 GB; replay 341 s (kernel 323 s); export 40 s; **nanoda 334 s at 4.92 GB** (was 8.9); closure replay 410 s.
- Projection 3,222 s conservative / **2,605 s calibrated**: memory is fixed, time is borderline at the 2,600 gate.
- PC8c (closure, ≈ −62 s kernel) is next in the pipeline.
**~03:50Z:**
- PC8b not frozen (calibrated 2,604.5 s, 4.5 s over the gate; nanoda 2.514e12 instructions at 4.92 GB, met).
- PC8c (closure, rootR8) running.
- bridge-port measured typh's engine in rootR8f at −15 % data build (311 → 263 s) and is preparing the combined closure + engine variant as TAG Fc, the fallback / margin upgrade.
**~04:00Z memory-gate definition (am-cert):**
- Lean max RSS includes ≈ 5 GB of mmapped oleans (AT7c, accepted: build footprint 5.67 GB, max RSS 10.65 GB).
- Gate: footprint ≤ 6 GB at every stage; max RSS ≤ 7.5 GB for nanoda and the closure replay; Lean-stage max RSS ≤ 10.65 GB.
- PC8b met all of it (nanoda 4.92 / 5.11 GB).
**~04:25Z PC8c (closure, unchunked, rootR8) pipeline DONE (run_n8_PC8CLc.log):**
- Standard axioms. Trimmed size 1,648,873 B.
- Stripped build 459 s at 5.49 GB; replay 255 s (kernel 240 s); export 38 s; **nanoda 237 s at 5.54 GB**; closure replay 320 s.
- Projection ≈ 2,537 s conservative / **≈ 2,060 s calibrated**: PASSES the gate (≤ 2,600 calibrated; footprints ≤ 6 GB).
- Next: header fix (comment-only diff), build-only check, axioms, freeze UPLOAD_PC8T.lean.

# UPLOAD NOW (2026-10-04 ~04:40Z): `UPLOAD_PC8T.lean` — 6734812/10000000 = 0.6734812 (+5.10e-5 over the record 0.6734302; above Gebendorfer's 0.6734765075)
**Form:** numerator `6734812`, denominator `10000000`.
**File:** 1,649,080 B, mode 444, sha256 ebcf09e9cd4262dd768af16484fd6feb4bd99cd306e9184dfd33bde27b7b593e (lead re-verified; 0 sorry).
**Checks vs 6734302/10⁷:**
- build-only of the header-corrected file: 476 s, footprint 5.50 GB, standard axioms ×3;
- code byte-identical to PC8CLcTS (full pipeline): build 459 s / 5.49 GB, replay 255 s, export 38 s, nanoda 237 s (1.934e12 instructions; footprint 5.54, max RSS 5.72 GB), closure replay 320 s;
- projection 2,537 s conservative / 2,060 s calibrated.
**Certificate:** 5,651 leaves (5,398 minorant-with-multiplier, 253 reflected, 0 Farkas), 32 root walks, closure tightening, Z8 with fast path, τ = 8/7 band profile, m = 148.
**Fallbacks on disk (same κ):** PC8CF, PC8CK, PC8F. **Safe backup:** UPLOAD_AT7T (0.6734383).
**UPLOADED (Sam, 2026-10-04 04:43:47Z):** board job d2090735 (owner a74474 = Sam), running, queue otherwise empty; 10-04 attempts: Sam 1. Expected ≈ 2,060 s calibrated → verdict ≈ 05:15–05:25Z.

# 2026-10-07: attempt-014 (PC8T, 0.6734812) was ACCEPTED on 10-04. On 10-06 "dani-ani0" took #1 with 6734824/10⁷.
- What they did: our PC8T verbatim plus a √-branch band lemma (fτ(E) = 2√(τE) − τ for E > τ, α = √(τ/E)) and a tail at m = 152 (file: /tmp/walkent/dani/Solution.lean).
- Attribution: they kept our in-file credit lines verbatim (internal agent names only). No mention of Samuel Lavery / attempt-014 in the file or metadata.
- Our gap: our headers never named Sam or carried a copyright line. FIX: every header from now on opens with "Copyright (c) 2026 Samuel Lavery (samlavery), Apache-2.0" plus the attempt lineage.
- Counter:
  - mvt-engine: new closure certificate at δ 0.005 / 0.003 / 0.002 % (κ with fτ 0.6734832 / 0.6734833 / 0.6734834).
  - bridge-port: port dani's √ chain to BrSqrt, credited.
  - am-cert: √ tail plus attribution headers.
  - window-scope: n=9 estimate.
**~20:30 local, 10-07, window-scope n=9 (rwin9_B440000.json, eps 862974/10⁸, R8 window):**
- κ_τ (τ = 9/8): linear 0.6734976 / **√ 0.6734989** at δ 0.02 %; 0.6735000 at δ 0. That is +1.65e-5 over dani and the decisive rung.
- B scan 0.0042 / 0.0046 running (hours).
- mvt-engine: n=9 Q=8 sizing port after the n=8 retake.
**10-08 ~03:30Z:**
- The port of dani's √ code was BLOCKED by the permission system ("code from external").
- Sam's decision: WRITE OUR OWN √ branch from Gebendorfer Lemma 3.3 (α = √(τ/E) on the αρ = 1 boundary). am-cert does it (hasn't read dani's file), reusing bridge-port's BrProf lemmas. Header notes dani-ani0 first used the branch on the board and that ours is an independent derivation.
- bridge-port moves to the n=9 Q=8 generator port.
**10-08 ~03:40Z correction:**
- am-cert had already read dani's tail, so the √ lemma is reassigned to window-scope as a CLEAN-ROOM author (BrSqrtLM, from Gebendorfer Lemma 3.3, reusing our BrProf).
- am-cert wires the tail from its own template and renames anything dani-derived. Credits now say "derived independently; first used on the board by dani-ani0".
- The attribution header (Sam's copyright + NOTICE + third-party notices) is implemented and enforced by the credit guard.
- A Python dry run on PC8CF with the √ tail reproduces dani's 0.6734824299 exactly (test only).
- Size watch: √ files ≈ 1.85–1.88 MB.
**10-08 ~04:10Z mvt-engine δ sweep (closure semantics):**
- δ 0.005 % CLEAN: cN 805124, 5,871 leaves, walk 358 KB, max depth 76; verify8pz 0 failures; DATA_try2c_0.00005.json.
- δ 0.003 / 0.002 % stuck at MAXD 200 near the minimum; a MAXD 400 test is optional.
- Retake build: PC8C5 (chunked, 1,025 KB) and PC8C5U (unchunked) in rootR8f. √ tail via window-scope's clean-room BrSqrtWS; κ ≈ 6734832/10⁷.
- am-cert assembles; freeze as UPLOAD_PC8S.lean.
**10-08 ~04:20Z window-scope BrSqrtWS COMPILED (clean-room, standard axioms):**
- gtau profile (mono, lip, le_self, nonneg); band_profile_sqrt (α = √(τE)/E, αρ = 1, d = 0); block_bound_w'_g, pre_solve_w'_g, n_point_bound_w'_g, Phi_g, AMW.am_dyadic_n_g / am_cumulative_n_g; two_mul_sub_le_gtau, Phi_g_ge_sqrt / lin.
- Instance test: κ 6734823 ≤ Phi_g at PC8T's c. Ships in place of am-cert's BrSqrtLM.
**10-08 ~04:30Z:**
- PC8C5U BUILT (rootR8f, unchunked, standard axioms; data 792 KB, 3.16 GB peak) → am-cert's √-tail run, κ 6734832/10⁷.
- n=9 (Q=8 port, closure): 16 roots; sampled roots 2/5/9 = 1,456/2,046/1,619 leaves at ≈ 295 bits each. Naive total ≈ 27k leaves ≈ 2.0 MB hex walk, ≈ 2× over budget.
- n=9 κ (√ branch): δ 0.1 % 0.6734945, δ 0.2 % 0.6734890, δ 0.3 % 0.6734836.
- Levers being measured: larger δ, BSPLIT, Huffman, unchunked.
**10-08 ~04:50Z n=9 full sizing (rwin9_B440000, δ 0.02 %, closure, Q=8):**
- 17,164 leaves, 16 roots clean; ≈ 306 bits/leaf, walk ≈ 1.26 MB hex fixed / ≈ 0.83 MB with Huffman.
- δ 0.1 % only −3.6 % leaves.
- Byte budget requested before emitting. Rough lead estimate ≈ 2.3 MB after safecut: non-walk data ≈ 434 KB at n=8 scales up, plus the 36-pair instance.
**10-08 ~05:00Z:**
- PC8C5U first check passed (build 579 s at 5.35 GB, replay 294 s, standard axioms, trimmed 1,704,258 B); staging is running.
- bridge-port's Q=8 generator port WORKS: a synthetic PS9 at standard axioms; split cost ×1.44; Inst 310 KB (split defs 72 %).
- Next for bridge-port: per-shape helpers to shrink Inst (target ≤ 150 KB) for the n=9 byte budget.
**10-08 ~05:20Z TIME RECALIBRATION (actual board durations, enqueue → complete):**
- AM6x 1,601 s; AT7c 2,617 (conservative 2,378, ×1.10); PC8T 2,944 (conservative 2,537, ×1.16); dani PC8T+√ **3,200 s** (40 s under the 3,240 limit; ×1.26).
- The "calibrated" model is retired. NEW GATE: conservative projection ≤ 2,500 s on a quiet machine.
- PC8C5U looks ≈ 15 % slower than PC8c (part load), so likely over the gate. Time cuts:
  - mvt-engine: BSPLIT n=8 δ 0.005 %;
  - bridge-port: derivative-read fast path + boundary-split kernel mode;
  - am-cert: quiet re-measure.
- n=9 PARKED: ≈ 17k leaves ≈ 3× kernel, cannot fit the time budget at the current per-leaf cost.
**10-08 ~05:35Z n=9 byte budget (mvt-engine):**
- ≈ 2.23 MB after safecut: base 714, instance 150–175, tables 208, points ≈ 280, covers 50, walk (Huffman + BSPLIT) 790, Huffman 35.
- Best case with every lever ≈ 1.97 MB.
- n=9 PARKED on both time and bytes.
- Retake focus: n=8 PC8S time (BSPLIT re-size, derivative fast path, quiet re-measure, instruction-ratio prediction against PC8T's actual 2,944 s).
**10-08 ~05:50Z mvt-engine BSPLIT at n=8 δ 0.005 %:**
- **4,598 leaves (−21.7 %)**, 4,566 splits (2,260 at region boundaries), 2,166 points, walk 283 KB.
- verify8pz 0 failures (DATA_try2cb_0.00005.json).
- Kernel: new PCellCloseB (cov_gsplitQ / ssplitQ at any q, bcutL from a 32-entry region list; 1-bit mode). PC8C5BInst 202 KB, PC8C5BData 717 KB unchunked; build queued.
- PC8C5B is the preferred upload candidate (≈ −20 % kernel), after PC8C5U's baseline measurements.
**10-08 ~06:10Z PC8C5U pipeline PASSED** (√ tail via BrSqrtWS, against record 6734824):
- Standard axioms; 1,704,258 B; footprints ≤ 5.25 GB; nanoda 4.06 / 4.24 GB.
- Load-inflated conservative 2,703 s.
- Instruction ratios against PC8c are 0.84–0.94 in every stage. Instruction-scaled conservative 2,338 s; **predicted board ≈ 2,713 s** (from PC8T's actual 2,944).
- GATE PASSED. Freezing as UPLOAD_PC8S.lean; PC8C5B (−21.7 % leaves) is the backup.
**10-08 ~06:30Z bridge-port per-shape closure helper (HELP=1; PCBias.lean, cuH):**
- Q=8 Inst 310 → 138 KB; Q=7 Inst 198 → 103 KB.
- Per split −8.5 / −12 %; on real PC8C5 data, data kernel −10 % (162 → 145 s).
- Standard axioms; drop-in.
- Next backup: PQ7HB = BSPLIT (PC8C5B) + HELP, for maximum time margin.

# UPLOAD NOW (2026-10-08 ~06:45Z): `UPLOAD_PC8S.lean` — 6734832/10000000 = 0.6734832 (+8e-7 over dani-ani0's 0.6734824)
**Form:** numerator `6734832`, denominator `10000000`.
**File:** 1,704,272 B, mode 444, sha256 40a6e3db12376e2dd67fd337d5d85d0ee217c74bfe8af4057ced8c1c4a29f89c (lead re-verified; 0 sorry; BrSqrtLM absent; header opens with Sam's copyright + NOTICE + full team line). v1 (5865fea5…) archived, not uploadable.
**Certificate:** PC8C5U, δ 0.005 % (cN 805124), 5,871 leaves (5,616 minorant + 255 reflected), closure + Z fast path, typh engine (rootR8f), √ branch via clean-room BrSqrtWS, m = 152, Φ ≥ 0.6734832051.
**Checks vs 6734824:**
- standard axioms ×3;
- instruction-scaled conservative 2,338 s; predicted board ≈ 2,713 s (PC8T actual 2,944 s × instruction ratio);
- footprints ≤ 5.25 GB, nanoda 4.06 / 4.24 GB.
**Backups:** PC8C5B (BSPLIT, −21.7 % leaves) running; PQ7HB (BSPLIT + helper) being built.
**10-08 ~07:00Z bridge-port DFAST (PCDF.lean; cover forcing so neighbouring leaves share kernel-cached reads; value-identical eq lemmas):**
- DFAST=1 (derivative reads) −10 to −12 %; **DFAST=2 (+ pyramid reads) −23 to −25 %** per root walk, full proofs.
- Backup PQ7HB = BSPLIT (−21.7 % leaves) + HELP (−10 %) + DFAST=2 (−24 %) in progress.
- Upload remains UPLOAD_PC8S.lean (sha 40a6e3db…).
**10-08 ~07:30Z bridge-port DFAST=3 (PCDZ.lean coarse-first tangent sides + PCDF):**
- Full PC8C5U certificate build 181.6 → 135.1 s (−25.6 %); roots 4 and 20 −35 %. Standard axioms.
- Next: PQ7HB = BSPLIT + HELP + DFAST=3.
- Board queue: nothing pending. PC8S NOT yet uploaded (Sam's step).
**10-08 ~07:45Z mvt-engine PC8C5BF = BSPLIT + DFAST=3 (rootR8f, standard axioms):**
- Data build 117.6 s against 266.8 s for PC8C5U (−56 %); peak 2.75 GB; Inst 202 KB, Data 717 KB.
- am-cert runs it next; it freezes as UPLOAD_PC8SF.lean if it passes. Same κ 6734832, much more time margin.
- PQ7HB (+HELP) is now low priority.
- PC8S (sha 40a6e3db) is still the ready upload; Sam hasn't uploaded yet.
**10-08 ~08:00Z am-cert:**
- PC8C5U quiet re-measure: conservative 2,316 s; instruction prediction stable at 2,712 s. PC8S is CONFIRMED.
- PC8C5B: passes, 1,635,530 B; instruction ratios 0.72–0.88; predicted board **≈ 2,484 s** (not frozen).
- PC8C5BF launched (raw 1,830,974 B, κ 6734832, credits incl. bridge-port's DFAST line).
**10-08 ~08:20Z PC8C5BF pipeline PASSED** (BSPLIT + DFAST=3, √ via BrSqrtWS):
- Standard axioms; stripped build 340 s at 4.86 GB, replay 146 s, export 38 s, nanoda 144 s at 3.99 GB, closure replay 206 s.
- **Conservative ≈ 1,792 s, board ≈ 2,080 s** (PC8T ratio).
- Header splice with corrected DFAST credits → build-only → freeze UPLOAD_PC8SF.lean.
- PQ7HBF (+HELP) is −2 % on data build, −96 KB Inst; an alternate.

# UPLOAD NOW — RECOMMENDED (2026-10-08 ~08:30Z): `UPLOAD_PC8SF.lean` — 6734832/10000000 = 0.6734832
**Form:** numerator `6734832`, denominator `10000000`.
**File:** 1,663,386 B, mode 444, sha256 97a12143747c8d78d3c365c8d0637454390c1b4fa846eb8fc4369886597d4cb9 (lead re-verified; 0 sorry; BrSqrtLM absent; Sam's copyright header).
**Certificate:** PC8C5BF, δ 0.005 % (cN 805124), BSPLIT + closure + DFAST=3 + Z fast path, typh engine (rootR8f); 4,598 leaves (4,419 minorant + 179 reflected), 4,566 splits (2,260 boundary); √ via BrSqrtWS; m = 152; Φ ≥ 0.6734832051.
**Checks vs 6734824:**
- standard axioms ×3; build-only of the header-fixed file 335.6 s;
- full pipeline on identical code: build 340 s, replay 146 s, nanoda 144 s (3.99 / 4.17 GB), closure 206 s;
- instruction ratios 0.63–0.84; **predicted board ≈ 2,295 s** (945 s under the limit).
**Alternative:** UPLOAD_PC8S.lean (sha 40a6e3db…, predicted 2,712 s), same κ. Board queue empty; dani-ani0 #1 at 6734824.

# 12:51Z 10-08: ATTEMPT-015 PROMOTED (UPLOAD_PC8SF, κ 6734832/10⁷).
- Enqueued 12:12:29Z, completed 12:51:08Z: 2,319 s against the 2,295 s instruction-ratio prediction (+1 %).
- Evidence: github.com/josusanmartin/riemann/tree/6b34385/submissions/attempt-015
- Jump question (Sam, 10-08): Gebendorfer Thm 1.2 caps the affine-pressure clipped-Gram class at 0.674034.
  - Our window is his cosine family (eq 5 = our H formula, line 780), so at most +0.00055 remains in-class.
  - The exits are per his §7. window-scope is running the class-cap room test (bench/window/capscan/): it reproduces his obstruction as a positive control, then recomputes r for enlarged windows.
  - Pre-registered: r ≤ 0.6741 means no room via the window exit; r ≥ 0.6750 means room.
**~13:xxZ 10-08 CLASS-CAP ROOM TEST, window exit: NO ROOM (window-scope, bench/window/capscan/, results.json).**
- Positive control: Gebendorfer txt:425 value reproduced to 28 significant digits (−9.2349008875104269582627e−7).
- Ceilings under the paper's mixture:
  - 25 modes: 0.674033065;
  - 48 modes: 0.674036462;
  - 96 modes: 0.674038143;
  - 192 modes and the general even window: 0.674038980;
  - free ω0: ≤ 0.674033092.
- The window space adds at most +6e-6. The pre-registered rule (≤ 0.6741 means no room) fires.
- Each window's own root: R8/PC8SF 0.6738160, R7 0.6737760, typh7 0.6737835. So any certificate of this class on R8 is < 0.673816.
- Caveats: floating mpmath (not interval-certified); c unconstrained (an upper bound); configurations not re-optimised (can only lower).
- Next: the transport exit (affine pressure / clipped trace, txt:449–451), dispatched to window-scope.
**10-08 TRANSPORT EXIT: CAPPED (window-scope; structural, with txt citations; no new numerics).**
- (b1) Multi-window joint: the obstruction is linear in the window, so the joint case reduces to a single window in the same convex family.
- (b2) Non-affine pressure: concave pressure is payable only by Jensen at the mean gap, and on the mixture the cost cancels exactly. Convex pressure is unpayable.
- (b3) Any spectral functional provable by a Lemma 3.1-type inequality has c ≤ 2, and Σφ(λ) ≤ ‖G−I‖²_F, which is Lemma 5.1's step (a).
- Missing inputs, named:
  - (1) an unconditional upper bound on a convex single-gap statistic, e.g. the second moment of normalised gaps between consecutive simple critical zeros;
  - (2) nonnegativity of the off-line pair terms (an RH-type positivity);
  - (3) band > 1, i.e. prime pairs past α = 1.
- Remaining in-class room: κ* ∈ [0.6734832, 0.674039]. The cap uses the paper's two FIXED configurations, so how sharp it is remains unknown. Dual-tightening test dispatched.
**10-08 DUAL TIGHTENING (window-scope, capscan/dual*.py, fam_*.py; float64, R8 confirmed in mpmath to 12 digits).**
- Controls recovered: R8 0.6738160 and 25-mode 0.6740331 with the paper's words.
- R8 re-optimised ceiling by word size:

  | word set | ceiling |
  |---|---|
  | q ≤ 3 | 0.6738158 |
  | q ≤ 5 | 0.6738103 |
  | q ≤ 7 | 0.6738085 |
  | long words, q up to 83 | **0.6738084** |

- Verdict: the rule's ≥ 0.67370 branch fires. The obstruction leaves ~3.25e-4 above PC8SF.
- 25-mode family bracket [0.6739952, 0.6739957]; the paper's cap tightens by 3.7e-5.
- Least favourable configurations: an alphabet of short gaps a ≈ 1.03–1.04 and long gaps b ≈ 1.95–1.96, with a + b ≈ 3 (at the zero of W near 3.03). Every minimiser sits at an integer period.
- At d = 1/r: weight 0.777 on [1.0382, 1.9618] (q = 3, period 3) + 0.223 on a q = 7, period-10 word.
- κ* on R8 ∈ [0.6734832, 0.6738084]. The upper end is NOT shown to be reachable.
- Next: slack attribution of PC8SF's chain on these words, plus the exact clipped-trace correction (dispatched).
**10-08 SLACK ATTRIBUTION on R8 (window-scope, capscan/slack.py, compat.py; float64).**
- (1) Step (a) is TIGHT: all eigenvalues on the dual words are in [0.904, 1.061] < 2, so Φ = (t−1)².
  - Exact m = 152 block-trace cap: **0.6737854**. The finite-block truncation accounts for 2.3e-5.
  - ROOM IS REAL: 3.02e-4 above PC8SF.
- (2) PC8SF's chain at the dual weights (sum = 3.02e-4 via r·s/(m−R)):
  - L1 (pairs at rank distance ≥ 8): 11.6 %
  - L2 (block-edge coverage 19.2 % + √ Lipschitz 2.2 %): 21.4 %
  - **L3 (local-functional excess): 67.1 %**
- Mechanism: F's floor c is attained at b-start alternating windows [1.983, 1.043, …]. a-start windows of the same dual words sit 3.8–4.6 % above c.
- k = 2 aggregation with the present weights gives only +0.021 %.
- BUILD TARGET = L3. The candidate tool is a COBOUNDARY-augmented window functional F + φ∘σ − φ: it telescopes over the block, leaving only a boundary term of osc φ. This is classical ergodic-optimisation duality: max over φ of min(F + φ∘σ − φ) = min over invariant measures of ∫F.
- First measurement: the ergodic minimum c_erg over periodic words versus c. Dispatched.
**10-08 COBOUNDARY TEST (A): NO ROOM (window-scope, capscan/ergodic.py; float64).**
- c_erg/c − 1 ≤ +0.097 %. Best word q = 7, a b b a b a b; alternating [1.9745, 1.0427] gives +0.164 %.
- A perfect coboundary gives κ ≤ 0.6734882, a gain ≤ 5e-6. My predicted ~2e-4 is REFUTED.
- Why: the dual's words (a 1.038, b 1.962) sit off F's near-tight words (a 1.043, b 1.975), and F is steep near a + b ≈ 3 (the zero of W). L3's 67 % measured that offset, not a shift imbalance.
- The per-window minimum ≈ the ergodic minimum, so PC8SF is near-optimal for ITS OWN functional F.
- Corrected next step: attribute L1/L2 at F's OWN binding words, where L3 ≈ 0. room ≤ (L1 + L2)(μ_c). Dispatched.
**10-08 BINDING-WORD ATTRIBUTION (window-scope, capscan/slack_bind.py, rankdist.py).**
- At F's own binding words (a b b a b a b q = 7, and alternating [1.9745, 1.0427]), L1 DOMINATES:
  - 0.21–0.23 per block; κ ceiling 9.3e-4 to 1.04e-3, capped by the dual's 3.0e-4;
  - L2c 3.7–4.3e-5;
  - L2l and L3 each < 1e-5.
- MECHANISM (harmonic): F binds at period a + b ≈ 3.017, just off an integer. That puts a Bragg peak at h ≈ 0.994, where qf ≈ (1−h)f(½)² ≠ 0 because f(½) ≈ 0.85.
  - Long-range energy is spread over ranks 8–60: 21 % by rank 15, 54 % by 30, 90 % by 60.
  - The dual's exact integer-period words carry 30× less.
- The band-limited chain cannot see this. It is the per-window worst case dropping one Fourier mode (rule 7's alarm).
- n = 9 is worth ≤ ~3e-5 (rank 8 = 3 % of L1), consistent with the LP estimate of ~1.5e-5.
- Cheap piece: a full-range profile, defect ≥ E_band + (2β−β²)E_out (BrProf + a Frobenius bound).
- Missing piece: a CERTIFIED lower bound on E_out, which is non-local (Bragg peak).
- Next: the reachable-κ curve versus credited rank R_max. Dispatched.
**10-08 R_max CURVE (window-scope, capscan/rmax*.py; float64, search minima = upper bounds).**
- Idealised chain κ at m = 152:

  | R_max | κ |
  |---|---|
  | 7 | 0.6735267 (+4.35e-5 over PC8SF) |
  | 10 | 0.6735866 |
  | 15 | 0.6736310 |
  | 30 | 0.6736768 |
  | 60 | 0.6736977 |
  | ∞ | 0.6737062 |

  At m = 320, κ(∞) = 0.6737319.
- κ(15) − κ(7) = 1.04e-4 (marginal); κ(60) − κ(7) = 1.71e-4.
- The binding MIGRATES to slipped integer-period words. Drift from an integer: 0.06 (q = 7) → 0.03 (b a b a b, period 8.03) → 0.0022 (a b b, period 5.002). The least favourable configuration inserts phase slips; this is a discommensuration structure.
- TWO-LEVEL proxy has teeth:
  - near-binding windows force a + b ≥ 3.0067–3.0134;
  - forced Bragg energy e(ℓ) is roughly linear in ℓ (δ 1 %: 2.63e-4 per point at ℓ = 16, 5.14e-4 at ℓ = 32).
- Open: the realistic two-level value, given run breaks and certified-form energy bounds. Dispatched together with the edge-window (L2c) scope.
**10-08 FINAL JUMP MAP (window-scope, capscan/tl_*.py, edgewin.py; float64; all gains are UPPER bounds).**
- B, two-level near-binding-run Bragg credit:
  - Without run-breaking the gain peaks at ~1.1e-4. WITH run-breaking (1974 configurations × phases) it is **≤ +3.1e-5** (best δ 3 %, binding = defect word on b a b a b, d +0.009, j = 12).
  - The least favourable configuration breaks runs cheaply with drifted slip words partly in U.
  - Exact integer periods are excluded from U for δ < 3.4 %.
  - NOT WORTH THE BUILD.
- A, edge windows (truncated k = 4–6 at both ends):
  - +1.97e-5 at m 152, +2.11e-5 at m 147. Marginal; floors for k = 5, 6 come from multistart.
- n = 9: ≤ ~1.5–3e-5 at 3× kernel.
- All levers together ≲ 5e-5, and not additive.
- STATE: the in-class room of 3.0e-4 is real (exact-trace cap 0.6737854) but lives in LONG-RANGE Bragg energy at near-integer periods. The least favourable configuration starves it with phase slips. A local (leaf) certificate cannot hold it; capturing it would need a block-level Fourier certificate (∫ qf |S_B|² over the whole block), a new architecture.
- Beyond the class, any of these three inputs would do:
  - (1) an unconditional upper bound on a convex gap statistic;
  - (2) off-line pair positivity;
  - (3) band > 1.

# ~20:00Z 10-08: NEW-BOUND BUILD, EDGE WINDOWS (Sam: "we should be attempting to prove a new bound").
- Target κ ≈ 0.6735043 (m ≈ 147, +2.1e-5 over the accepted 0.6734832).
- Mechanism: truncated windows (prefix truncations at the right end, mirror image at the left; k = 4..6 gaps, each with its own floor c_t(k)) recover the band-pair coverage lost at the block edges (L2c).
- Pressure accounting checked at source: pre_solve charges W.B·(m−q) via offset_average_w/step2, so each edge window costs B_t. Net gain is κ·c_t − B_t > 0 only for k ≥ 4.
- Assignments:
  - window-scope: design numbers and data (bench/window/edge/), plus a reversal-symmetry check of W.
  - bridge-port: Lean chain, new BrEdge*.lean: (E1) coverage generalising window_pairs_le_band; (E2) block_energy_band_edge; (E3) re-threaded Phi/n_point/final κ.
  - mvt-engine: truncated-functional certificates (generic-Q sizer for k = 4..6).
  - am-cert: assembly hooks, theorem shape (strict improvement over 6734832/10⁷), timing gate ≤ 3,000 s predicted, memory/byte gates, freeze to a NEW UPLOAD_ name.
**~20:50Z 10-08 EDGE DESIGN FINAL (window-scope, bench/window/edge/, mpmath 50 digits; matches am-cert's exact arithmetic).**
- Floors c_t:
  - k3 0.0021055119 (does not pay);
  - k4 0.0037198862;
  - k5 0.0055279045;
  - k6 0.0071449289 at [1.04284, 1.97664, 1.04473, 1.96862, 1.03949, 1.03920] (4096-start + 27⁶ grid; the first edge_k6.json eps 0.0072584 was WRONG and is now overwritten).
- W reversal-symmetric, exact in integers.
- κ:

  | edge set | m | κ |
  |---|---|---|
  | {6} | 150 | 0.6734966 |
  | {5, 6} | 148 | 0.6735034 |
  | {4, 5, 6}, δ_t 0.1 % | 147 | **0.6735042 (6735041/10⁷)** |
  | {4, 5, 6}, δ_t 0.01 % | | 6735043 |

- Main-certificate δ tightening is worth +1e-7: no.
- Status:
  - PCE4 (unrolled) and PCE5 (list-evaluated, 53.4 KB) proved.
  - PCE6 sizing at cN 713000.
  - PCE4G (list-evaluated) next.
  - Fallback {4, 5} (κ 6734905, ~1.85 MB projected) in its full pass (E4b) after the pc_spl macro-clash fix.
**~21:45Z 10-08 UPLOAD_PC8E4.lean FROZEN (am-cert; independently re-verified by the lead).**
- File: κ 6734905/10⁷ = 0.6734905 (+7.3e-6 over attempt-015); S = {4, 5}, unrolled PCE4 + list-evaluated PCE5, m 150; 1,843,996 B, mode 444; sha256 1a2f7626e3e013105cf7ca63f9a6f4be3f60a8abac9faf09b455ef67a34f44bb.
- Checks: BUILD/REPLAY exit 0, standard axioms on all 3 theorems, nanoda exit 0, closure replay OK (77,024 constants).
- Gates: predicted board 2,568 s; footprint ≤ 5.22 GB; nanoda RSS 4.73 GB.
- Calibration:
  - safecut ratio ×0.906;
  - net edge payload after safecut 180,610 B;
  - edge machinery +10.7 % instructions (+249 s board).
- STATUS: HELD (lead's recommendation: don't publish the edge method on a +7.3e-6 step). Primary {PCE5H, PCE6} in progress (κ ≈ 6735034); fallback-primary {PCE6} (≈ 6734966).
**~22:50Z 10-08 {PCE5, PCE6H} MEASURED, NOT FROZEN (am-cert).**
- Result: κ 6735034, all checks pass, BUT 1,925,544 B after safecut and predicted 3,163 s (only 77 s under 3,240). Kept as a calibration record: tauint/PC8C5BFETS.lean.
- TRUE CALIBRATION: ET − E4 = +595 s for +692e9 net cert instructions, so **0.86 s board per 1e9 NET**. Base = 2,319 s, i.e. the Lean chain and glue are free. mvt-engine's 0.557 per 1e9 build instructions understated by ~1.5×.
- Re-projections:

  | edge set | time | size |
  |---|---|---|
  | {5KP, 6KP} | 3,230 s ✗ | |
  | {5KP, 6HP} | ~3,096 s ✗ | |
  | {6H} | 2,973 s | |
  | **{5KP, 6UPC}** (unrolled k=6 + PTBASE + data cuts) | **~2,864 s** | **~1.94 MB** |

- Kind-aware generic leaf (mvt-engine, PCellGK.mcheckGXK = mcheckGX): k=6 GENI 2,445e9 → 917e9 (−62 %). The first hypothesis (forced decode) was REFUTED by measurement.
- Tracks:
  - A: PCE6UPC (primary).
  - B: generic-split profiling (switch if k=6 hybrid ≤ 550e9 at ≤ 50 KB Inst).
  - bridge-port trims as BrEdgeT/BrEdgeChainT.
- Fallback UPLOAD_PC8E4 (6734905) frozen and held.
**~23:10Z 10-08 NEXT-METHOD ROOM TEST (window-scope, bench/window/band1/; floating point, LP via column generation, values are upper bounds on each LP's min).**
- Zeta23 0.68185 law read at source (zeta-23-lean/Zeta23/PairCeiling/LawN256.lean, CeilingLaw256.lean, Signed.lean):
  - a 256-periodic MARKED law (simple + double points);
  - matches the band-1 form factor to 3e-40;
  - p₀ = 0.6818287.
- Full band-1 constrained LP: N = 8 0.686, 16 0.6832, 24 0.6830, 32 0.6831. Consistent with p₀. Window-independent.
- KEY: the single-window (R8 datum only) marked LP gives N = 16 0.67857, 24 0.67794, 32 **0.67773**.
  - The room above Gebendorfer's class (0.674) comes from CONFIGURATION-WISE integrality (doubles), not from signed band-1 directions.
  - The dual direction is ≈ the window's own qf.
- House prior map: memory cgdl-transplant-three-walls. Its open problem is a configuration-valid counting inequality on the Gram pencil with pair charge 4p.
- Next: the realisation test. Does the LP certificate survive off-line pairs of depth y in Zeta23's Hermitian frame? Dispatched.
**~23:45Z 10-08 REALISATION TEST: SURVIVES (window-scope, band1/realise*.py; prediction pre-registered and matched).**
- Off-line pairs at any depth y ≤ 3, and triples, never lower the min. Min p ≈ 0.6778 (N=32); continuum estimate 0.67746 on R8.
- Mechanism: qf = w⋆w ≥ 0, so the energy is ∫ qf |Ŝ|². An off-line pair enters as a double with amplitude 2cosh(2παy) ≥ 2, i.e. strictly worse for the adversary. The cosh factor that blocked the CGdL transplant helps here.
- TARGET D(δ): ℰ(Z) = (1/N)∫₀¹ qf |Ŝ|² ≥ δ·(N − N_s)/N − o(1), with δ = Δ₁/2N = 0.495392 (single-defect relaxation energy).
  - With ℰ = ∫₀¹ qf·α = 0.159784: N_s/N ≥ 0.67746.
  - Lemmas, measured and not proved: L1 single-defect energy; L2 superadditivity; L3 depth/multiplicity monotonicity.
- Margin: beating κ 0.6735 needs δ′ > 0.4894 (98.8 % sharp).
- CGdL (arXiv 1810.08843, read at source): a KERNEL-axis SDP with a termwise configuration step. It is RH-conditional and NOT the twin. The kernel-side twin is Zeta23's (c₀, r) class (README.md:50).
- Next:
  - window-scope: optimise the window for κ_D;
  - bridge-port: scope whether the board's Lean exposes the zero-indexed pair datum.
**~23:45Z 10-08 UPLOAD_PC8E.lean FROZEN (am-cert; lead re-verified sha, mode, forbidden tactics, header).**
- File: κ 6735015/10⁷ = 0.6735015 (+1.83e-5 over attempt-015); 1,941,363 B, mode 444; sha256 5000dfb504e4cba831b3a7976974849f7574e2d7384a14f974b4a8bb02de2945.
- Contents: PC8C5BF main certificate + edge windows S = {5, 6} at both ends: PCE5KP (cN 552735, kind-aware generic leaf) and PCE6UPC (cN 693058, δ 3 %, unrolled, shared points); m 148.
- Checks:
  - all 3 theorems on standard axioms;
  - builds and replays exit 0, nanoda exit 0, closure replay OK;
  - predicted board 2,632 s;
  - peak footprint 5.27 GB.
- Fallback UPLOAD_PC8E4.lean (6734905). AWAITING SAM'S UPLOAD.
**~23:55Z 10-08 D(δ) SCOPING (bridge-port, reading only).**
- D(δ) plugs into the board framework via FROBENIUS data:
  - ‖G̃‖²_F = Σ m m′ ⟨u,u′⟩² = the pair sum with K = (\widehat{φ²})², qf = w⋆w, w = φ²;
  - bounded by TracesBoundsD.frhat (AssemblyD.lean:71) for R8 via tracesBoundsAM_concrete (BHalf.lean:27);
  - the J term = ∫₀¹ qf·α.
- There is no zero-indexed BGST pair theorem in Zeta23, and none is needed.
- The ONLY open input is D(δ), stated on frobSq(Âz): Gabor-sampled, windowed, complex γ, multiplicities. The continuous δ must survive sampling and edges (template: kernel_limit).
- Next: bridge-port builds the CONDITIONAL skeleton DefectEnergy*.lean (D as a hypothesis → dyadic/cumulative κ = 1 − e∞/δ) and cross-checks e∞ against 0.159784.
**~00:05Z 10-09 DEFECT-ENERGY SKELETON COMPILED (bridge-port, rootR8f/AMW/DefectEnergy.lean, DefectEnergyAx.lean).**
- Standard axioms; D(δ) appears only as the hypothesis `hD : DefectEnergy zetaZeroConfig δ`.
- Theorems: AMW.dyadic_of_defectEnergy, AMW.am_dyadic_defect, AMW.am_cumulative_defect (the am_dyadic shape); datum defectEnergy_datum via frobAz_le (Gz_eq_Gp → frobSq_hat → frhat, plus the tail).
- Datum: e∞ = JInf/(2aInf²) = 0.1597839052404248 = window-scope's ∫₀¹qf·α to 2.8e-17. e₀ = qf(0) = 1.00826; 1/c∞ = e₀ + 2e∞, consistent with HW.
- Implied κ at δ = 0.4954: 0.67746487.
- OPEN: D(δ) itself, on the Gabor-sampled object.
  - Normalisation: ℰ is the ONE-SIDED (halved) excess.
  - Includes the all-simple lower side ℰ ≥ −o(1).
**~00:30Z 10-09 WINDOW OPTIMISATION FOR D (window-scope, band1/winopt*; floating point; verified = superlattices N 3–96 + clusters k 2–5 + triples).**
- κ_D, verified: R8 0.677424 (δ_true 0.495338); BEST 25-mode smooth window **0.680742** (δ_true 0.484424, ∫qα 0.154656).
- Sharpness needed to beat 0.6735: R8 98.80 %, best **97.78 %** (to reach 0.676: 99.56 % / 98.54 %).
- Single-defect κ_D up to 0.6814 FAILS L2: aggressive windows have attractive defect superlattices and pair wells (0.4–0.9 % cheaper per defect). L2 is the binding lemma.
- L1 structure: a lattice DIPOLE (double + vacancy at distance 2), very local. The bare dipole carries 99.1 % (R8); 99 % of relaxation lies within 5 neighbours per side.
- Next: (a) normalisation confirm; (b) Gabor-sampling survival; then a proof-strategy study (global auxiliary-function certificate vs local route).
**~00:50Z 10-09 D CHECKS (window-scope, band1/sampled*.py).**
- Normalisation: ONE-SIDED confirmed (κ = 1 − e∞/δ). One double raises the sampled N·ℰ_T by 0.9868 at W=200, tending to 2δ = 0.99077.
- Gabor sampling: bulk aliasing EXACTLY 0 (Poisson + supp √f ⊂ [−½, ½]). Edge deficit is O(1/W) per defect (R8 0.98274 → 0.98679 at W 100 → 200), o(N) total.
- All-simple lower side: measured ℰ_T ≥ −O(log N)/N (worst cases pile near-coincident zeros at the walls). Termwise only gives the DC debt −0.0041. NOT PROVED.
- Next: proof-strategy study (global auxiliary-function certificate vs local route).
**~01:20Z 10-09 D PROOF-STRATEGY STUDY (window-scope, band1/global_cert3*, global_joint, local_route*, offline_toll).** Pre-registered branch NOT met.
- Global band-limited 2-point certificate (K = h + g, g ≥ 0 termwise, ĥ ≥ 0): δ′ = ½ inf qf/(1−α).
  - R8 69.4 % of δ_true; best window 55.8 %; joint κ_cert = 2/3 exactly (Fejér).
  - Off-line-safe.
- With ĝ dips beyond the band (exact LP):
  - R8 at A=3: 99.04 %, κ_cert 0.67431. Joint 0.67556. Best window saturates at 95.5 %.
  - BUT off-line pairs at normalised depth 0.1–0.2 break it: g at complex arguments carries cosh(4παy) on the dip. STRIP WALL (cgdl #2) in the D frame.
- Local route: the vacancy delocalises into a uniform dilation, charged only by the band-edge Bragg peak. δ_R ≈ 82 % and falling with N. No finite R.
- Lower side: O(1) per wall, handled.
- The exact D survives off-line pairs (the PSD form, where cosh helps); only the termwise certificate part fails.
- Next: option (i), a hybrid certificate (dip termwise among on-line points only; off-line terms inside a PSD form), plus the local refutation check.
**~02:30Z 10-09 HYBRID CERTIFICATE (window-scope, band1/hybrid_cert*): pre-registered "≤ 0.6735" branch, so the D TRACK IS PAUSED.**
- PSD-only off-line treatment forces ĝ_on ≤ 0, i.e. zero charge (exact).
- The PSD + termwise LP (a relaxation, so upper bounds) needs cosh-safety on the cross terms:
  - R8 κ_cert: 0.6745 (y_max ≤ 0.02) → 0.6721 (0.05) → 0.6545 (0.1) → collapse;
  - joint window: 0.6755 at y_max = 0.05 (needs depth ≤ 0.3/log T, which nothing we've read supplies);
  - ablation: the off-off, then on-off, cross terms are the wall.
- The local-route refutation check held (δ_R 0.4066/0.4274 < 0.45).
- STATE: D(δ) holds numerically everywhere tested (κ_D 0.6774 R8 / 0.6807 best). No certificate in the PSD + termwise family proves it off-line.
- Forward inputs: a spectral off-line block (Zeta23 inertia, flat charge 4) coupled to the on-line dip certificate (= the house's August pencil problem); 3-point/SDP; or a near-line depth cap.
- Write-up: band1/D_TRACK_STATE.md.

# 01:05Z 10-09: ATTEMPT-016 PROMOTED (UPLOAD_PC8E, κ 6735015/10⁷ = 0.6735015). #1 on the board.
- Evidence: github.com/josusanmartin/riemann commit 296f7bb, submissions/attempt-016.
- Author samlavery; method as given. Nothing pending since.
**~02:45Z 10-09 D TRACK RESUMED (Sam: "lets fix this latest attempt"). New construction: on-line projection + Lemma P.**
- D(Z): replace each off-line pair by an on-line double at its real part. Exactly, E(Z) = E(D(Z)) + Δ_B, with Δ_B using only qf ≥ 0 (pair amplitude 2cosh = 2 + B_y, B_y ≥ 0).
- The dip certificate C (on-line, real arguments) applies to D(Z).
- Lemma P: E(Z) ≥ F_C(D(Z)), i.e. the dip slack pays for any negative Δ_B. The cosh never meets the dip.
- Numerical test dispatched to window-scope (pre-registered; my prediction ≥ 0).
**~03:15Z 10-09 LEMMA P: HOLDS NUMERICALLY (window-scope, band1/lemmaP*.py; pre-registered VIABLE branch; lead's prediction held).**
- Exact reduction: F_C(D(Z)) = ĥ(0)N + g(0)Σm² (counts only), so Lemma P ⟺ D(δ′), δ′ = g(0)/2, with pairs as defects.
- Worst W ≥ +0.0072 to +0.0100 × 2δ′ per defect (N = 24/32/48, R8 and joint), always at DEPTH 0. Near the line Δ_B/2 ≈ +6.8·y² × 2δ′.
- Negative Δ_B occurs only in disordered environments carrying slack ≥ 2.2 × 2δ′, a 220× gap.
- κ_cert: R8 **0.674248** (g(0) = 0.981016; +7.5e-4 over attempt-016); joint 0.675557 (Gabor-family check pending).
- Plan:
  - window-scope: an analytic proof of Lemma P (own-double split + environment cross term vs slack, explicit constants);
  - bridge-port: scope the Lean side (trig-poly certificate check, sampled counts-only bound, Lemma P plug-in, file size). No PC8 leaf certificate is needed.
**~03:40Z 10-09 D-TRACK LEAN BUILD STARTED (bridge-port's scoping; new files rootR8f/AMW/DE*.lean).**
- Plan:
  - 1 DESlack, 2 DEPInterface, 3 DEFourier, 7 DECert, 8 DEObj: bridge-port;
  - 4 DESOS (Fejér–Riesz SOS for C ≥ 0, ~9.2k rational products, < 2 s kernel): am-cert;
  - 5 DEQf, 6 DEQfCells (qf closed form; ĥ ≥ 0 by ~200–700 Taylor cells plus the edge slope): mvt-engine;
  - backed-off rational certificate (Δκ ≤ 5e-5, κ ≥ 0.67420), then the analytic Lemma P: window-scope.
- Main risk: Phase 2(b), the Gabor comparison at complex arguments (cosh(L·depth) truncation near the walls). Lemma P must be stated relative to slack.
- Projected Solution: ~0.5–0.65 MB, ~1,100–1,500 s board (no PC8 leaves). NOT submittable while LemmaPObj is a hypothesis.
**~04:00Z 10-09 LEMMA P ANALYTIC CHAIN (window-scope, band1/lemmaP_chain*, curv_slack*, gabor_check*): pre-registered "fails" branch.**
- Exact lemmas verified: L1 decomposition; L2 field form; L3 imaginary shift, 2∫qf·B·Φ = 4[Re V_D(s+iy) − V_D(s)]; L4 lattice cancellation Σ_n L_y(n+t) = 0; L5 pair block ≥ 0 (no uniform constant); L6 Δ_B = −2y²V″_D(s) + O(y⁴).
- Step (b) FAILS in both naive forms:
  - global Cauchy–Schwarz: ‖S_env^fl‖² carries every other defect's certified charge (class: pair + remote dipoles);
  - termwise: the dip certificate is lattice-tight, g(n) = 0, versus L_y(n) < 0 (class: integer-separation neighbours).
- MISSING LEMMA, the curvature–slack gap: slack(D) ≤ σ₀ ⇒ V″_D(s) ≤ −c₀ at the double.
  - Measured c₀ ≈ 3.2 at σ₀ = 2. Curvature becomes positive only at slack ≈ 3.7.
  - Not proved. It is a crystallization-stability statement (elastic coercivity with the band-edge soft mode, cluster bounds, far field via L4).
- Joint window: NOT a single Gabor family (3.6 % residual). TARGET = R8, κ_cert 0.67425.
- The backed-off certificate is still pending; requested again.
**~04:10Z 10-09 SAM: STAGED PUSH on the D attempt.**
- Finish the cheap Lean pieces: 1–3 bridge-port, DESOS am-cert, DEQf/DEQfCells mvt-engine (on backed-off data).
- HOLD steps 7–8 (DECert, DEObj).
- window-scope: backed-off certificate, then a pencil proof sketch of the curvature–slack gap lemma (pre-registered VIABLE = every step pencil-proved or reducible to a finite certified computation within the 220× margin).
- Re-decide after the sketch.
**~04:30Z 10-09 BACKED-OFF CERTIFICATE (window-scope, band1/cert_R8_backed.json, sha 9a87a6f0…). Lead re-verified g(0), ĝ(0), σ, κ, the knot signs and min C.**
- R8, Dk 1/32, A = 3, Y/2⁴⁰; margins m_C = m_h = 2e-5.
- σ = ĝ(0) − g(0) > 0 is FORCED by the margins (Poisson + C > 0) and charged per point: κ = 1 − (e∞ + σ/2)/(g(0)/2). This matches DEPInterface.
- **κ_cert = 0.6759645** (g(0) 0.99043084, σ 1.367e-3, δ′ 0.4952154 = 99.98 % of δ_true). That is +2.46e-3 over the board's 0.6735015, conditional on Lemma P.
- Lemma P re-checked against this certificate: worst +0.00319 × 2δ′ per defect (depth 0).
- Now: am-cert DESOSFin and mvt-engine DEQfCells on this data; window-scope's pencil sketch of the curvature–slack gap.
**~04:50Z 10-09 STABILITY SKETCH (window-scope, band1/stability_sketch*; computed on v2 constants, to redo on canonical v1). Verdict: VIABLE-PENDING (steps 8, 9).**
- The lead's curvature–slack gap AS POSED is FALSE: packed doubles give slack 0.42 with V″ = −0.495 (prediction REFUTED; the earlier c₀ came from single-double searches only).
- The FIELD form LP (s + ∫qf·B² + 2Σ m L_y(x − s) ≥ 0) is the right target.
- Steps:
  1. Poisson at any spacing: proved.
  2. On-lattice core, Ψ = ∫qf·B² exactly for y ≤ 1.4 (L_y(n) < 0 ∀ n ≠ 0), covers every double/vacancy arrangement on the lattice. A 2D cell check is needed. Dilation is BENIGN, so no soft-mode lemma is needed.
  3. Cluster bound: proved.
  4. Nearest-neighbour strain coercivity, g″(1) = 2.376: proved plus a 1D check.
  5. Near-lattice perturbation, margin ≥ 22×: plausible.
  6. Far field: proved.
  7. High-cost regime: proved.
  8. Global non-near-lattice: a certified chain DP, DESIGNED NOT RUN (decisive).
  9. Deep coherent clusters (y > 1.4): collective bound OPEN.
- Next (Python only): A step-8 coarse DP (pre-registered), B step-9 pencil, C size of step 2's cell check. Lean DEObj stays on hold.
**~05:20Z 10-09 STEP-8 COARSE CHAIN DP (window-scope, band1/chain_dp.py; pre-registered NEGATIVE branch at small y).**
- Certified LB/∫qf·B²:

  | y | bound |
  |---|---|
  | 0.1 | −219× |
  | 0.2 | −14× |
  | 0.3 | −2.7× |
  | **0.5** | **+0.21** |
  | 0.7 | −0.37 |
  | **1.0** | **+0.36** |
  | **1.4** | **+0.88** |

- The binding patterns are METHOD ARTEFACTS: exact LP on them is positive (+0.27 … +923). The DP missed T_g.
- Diagnosis:
  - y ≥ 0.5: finite with cluster accounting (routine).
  - y ≲ 0.3: not a coarse finite problem. The tight class (doubles on every site) has margin only Ψ ≈ 89y⁴ against O(y²) field terms, so the needed resolution is ~y².
- The shallow regime must be ANALYTIC: step 2 (exact on-lattice) + step 5 (near-lattice, ρ ≥ 22) + a field-resolved DEFECT GAP (non-near-lattice ⇒ LP ≥ c·y²). Slips of ½ are field-benign (L(n + ½) > 0) but cost little T_g.
- No counterexample found.
- Remaining: B (step 9 collective bound), C (size of step 2's check), then the shallow-regime rigidity lemma (the hard core).
**~05:40Z 10-09 D-TRACK LEAN: EVERYTHING EXCEPT LEMMA P COMPILED (bridge-port; standard axioms; LemmaPObj explicit).**
- Built ahead of the staged hold (messages crossed); the work is kept.
- Modules: DEObjA/B/C, DEObj, DEObjMain, DER8 (~133 KB of bridge-port modules in total).
- lemmaPObj_online: the interface is inhabited, conditional on the window being on the line.
- AMW.am_dyadic_R8 / am_cumulative_R8 (hP : LemmaPObj zetaZeroConfig (qf(0) − y₀) g(0)) : board shapes for κ ≤ 1 − (e∞ + σ/2)/(g(0)/2) = 0.6759645.
- With certG_R8 (am-cert) and certH_R8 (mvt-engine; 161 cells, ~760 s board) the on-line continuum part is complete.
- Next small item: qfAM_zero_ge (mvt-engine) for a rational κ ≥ 0.6759624.
- REMAINING: Phase 2, LemmaPObj for zetaZeroConfig (math: the shallow-depth defect-gap/rigidity lemma + deep coherent clusters), then its Lean proof incl. the Gabor comparison at complex arguments.
**~05:55Z 10-09 D-TRACK LEAN SIDE CLOSED (bridge-port DER8K + DE_LEAN_STATE.md; lead spot-checked).**
- `AMW.am_dyadic_R8_rat` / `am_cumulative_R8_rat`: board shape at κ = 6759644/10⁷ (exact 0.6759645). The ONE hypothesis is `LemmaPObj zetaZeroConfig (qfAM 0 − cR8.y 0) (gPL cR8 0)`.
- `kappa_R8_floor` is hypothesis-free (HW_ge + qfAM_zero_ge ≥ 1.0082637).
- Standard axioms throughout.
- State doc: rootR8f/AMW/DE_LEAN_STATE.md.
- Lean work stopped. Remaining: Phase 2 (LemmaPObj for ζ), i.e. the math (window-scope B/C, then the shallow-depth rigidity lemma), then the complex-argument Gabor comparison in Lean.
**~06:10Z 10-09 STEP 9 / STEP 2 (window-scope) + SAM: MATH PUSH ON THE DEFECT GAP (pencil + numerics, no Lean).**
- B, step 9 (deep coherent clusters): PLAUSIBLE.
  - Chain (a)–(d) is complete.
  - Measured W/R_coll ≥ 0.9987 (P ≤ 8, spacing 1.5).
  - ‖S_B‖ saturates in P, ≫ 4P + 2M_near.
  - Open: (e), a saturation/Turán lemma for large P.
- C, step 2 sign check: CORRECTION, y_s = 1.1419 (not 1.4). Beyond it Ψ ≥ 0.9995·∫qf·B², so the conclusion holds for all y. About 700 cells, split: series for y ≤ 0.1, Lipschitz cells for 0.1–0.8, magnitude check for ≥ 0.8.
- Assignments:
  - window-scope: the shallow-depth DEFECT GAP (non-near-lattice ⇒ LP ≥ c·y²), pre-registered;
  - bridge-port: the cluster SATURATION lemma (step 9e), pre-registered;
  - am-cert and mvt-engine: stand by.
**~06:40Z 10-09 SHALLOW-DEPTH DEFECT GAP (window-scope, band1/defect_gap*.py; D_TRACK_STATE.md updated).**
- CORRECTION: with P_h restored there is NO O(y⁴)-tight near-lattice class (packed-double blocks have LP = O(y)). The step-8 "y⁴" was a coarse-DP artefact.
- Claim: LP ≥ c·y² for y ≤ 0.4. Measured c ≈ 18 (min 18.1); off-lattice ≥ 27.8. NO obstruction family found.
- Chain:
  - a. Taylor with remainder: PROVED.
  - b. on-lattice Q₂ ≥ 0, R₄ ≥ 90y⁴ (Poisson): PROVED.
  - c. small displacements (ρ ≥ 22): PLAUSIBLE.
  - d. CROWDING (doubles near ±0.8 where K″ peaks; g-cost pays ~7.9×; −Q₂/s ≤ 6.2): OPEN, reducible to a finite certified branch-and-bound (≤ 4 points per side).
  - e. off-lattice R₄: PLAUSIBLE.
- Next: window-scope runs the certified branch-and-bound for d (pre-registered).
**~07:00Z 10-09 STEP 9(e) (bridge-port, bench/window/sat9/): posed criterion OBSTRUCTED; exact repair proved in part.**
- Posed "‖S_B‖ ≥ 4P + 2M_near" FAILS. Adversarial cancelling clusters make X saturate or decrease in P (y=1: P=4 → 14.35 < 16; s = (0, .5503, .7347, 1.2850)). T_g is linear in P against the needed (2P + M)². Large sieve and Ingham don't rescue it.
- REPAIR (exact): Q_pp = ‖Σ(B_p + 2)e_p‖² − ‖Σ2e_p‖² replaces the 4P Cauchy–Schwarz loss.
  - Q_pp = X² + 4Λ ≥ X² for EQUAL depths: PROVED.
  - P = 2, any depths: PROVED (pointwise).
  - Unequal depths, P ≥ 3: PLAUSIBLE (minima +23…+101).
- Corrected chain 2W ≥ 2s + Q_pp − 2‖S_on^near‖X − far is positive in all runs (≥ +18.8; the posed chain went to −1264).
- Open:
  - (1) Q_pp ≥ 0 for unequal depths, P ≥ 3;
  - (2) an explicit Λ = ∫qB|V|² lower bound for cancelling clusters, combined with the cluster slack.
**~07:30Z 10-09 SHALLOW CROWDING STEP d: CERTIFIED (window-scope, band1/crowd_dp.py; computer-assisted, double precision + EPS allowances, NOT yet interval arithmetic).**
- Certified LP/y² ≥ **1.953 for ALL real D** with a double at s, y ∈ (0, 0.4]. This subsumes the near-lattice branch (steps c, e no longer needed for a single pair).
- Crowding class 2.5–6.1; slack localised to [0, 8]: 1.379.
- Method: exact backward DP over 7,296 cells per side (1/256 → 1/32), Taylor-in-y² ψ tables, |g″| ≤ 7.73 from the ĝ knots, analytic tail beyond 128, 32 y-intervals, 324 s.
- Soundness checks passed: field form = periodic; quadrature 1.6e-12; tails ratio ≤ 0.935; heuristic minima above the bound.
- Also certified: [0.40, 0.475] gives 12.5 / 16.1 / 20.6.
- Remaining for a single pair: a cluster-aware DP on [0.475, y_deep], then the analytic deep regime.
- Then: the rigour upgrade (interval tables), multi-pair shallow slack-sharing, and bridge-port's deep Q_pp / Λ.
**~07:45Z 10-09 INTERFACE FINDING (window-scope): MULTI-PAIR GAP.**
- The single-pair bound (1.95y²) consumes ~60–67 % of the pair's own B-diagonal ∫qf·B².
- With several pairs, the joint form ∫qf|Σ B_p e_p|² has negative cross terms (K⁽⁴⁾(1) = −12.58; Poisson Σ_{n≠0}K⁽⁴⁾(n) = −K⁽⁴⁾(0), so a dense lattice of equal shallow pairs can cancel the joint B-energy).
- Shallow+shallow and shallow+deep configurations are NOT covered by step 8 or step 9(e) yet. Owner: window-scope (using bridge-port's exact Q_pp).
- Slack convention: local T_g (±8) → step 8; P_h + other T_g → 9(e).
- Step 8 is being extended to y₁ = 0.8 (cluster-aware DP).
**CORRECTION (~07:50Z 10-09, window-scope):** the coarse step-8 DP's "certified positive at y = 0.5, 1.0, 1.4" does NOT certify anything. That run dropped P_h and had errors.
- Single-pair certification now covers ONLY y ∈ (0, 0.475] (crowd_dp).
- Above 0.475: the cluster-aware DP (to 0.8) is running, plus the analytic deep regime (y ≳ 0.7–1) and step 9.
- Also open: a slack rule for a deep pair within ±8 of a shallow one (multi-pair, window-scope).
**~08:30Z 10-09 SINGLE-PAIR LEMMA P: COMPUTER-ASSISTED FOR ALL y > 0 (window-scope; double + allowances, not interval).**
- Pieces:
  - (0, 0.4]: NN DP, LP ≥ 1.953y²;
  - [0.4, 0.9375]: cluster-charged DP, ≥ 13.65y²;
  - [0.6, 12]: half-bin grid, ≥ 0.0527·self;
  - [10, ∞): analytic, ≥ 0.483·self.
- y_deep = 0.8 (coordinated with bridge-port).
- Rigour upgrade sized: closed-form K = F², ~1 day coding; mpmath.iv ~1 day compute or flint (not installed). HELD.
- Multi-pair shallow measured: dense equal-depth blocks keep LP_total ≈ 5 (an edge effect; positive). Plan: (i) separated, (ii) clusters k ≤ 3 by B&B, (iii) long blocks with analytic bulk (Poisson + bridge-port's identity) and certified edges.
- NEW GATE: am-cert is estimating the Lean kernel cost of porting these certificates (~10^5–10^6 evaluations) against the board budget. It decides board vs paper-only.
**~08:50Z 10-09 LEAN FEASIBILITY FOR LEMMA P (am-cert, analysis only) + SAM: FINISH THE MATH FIRST.**
- Calibration: 1 kernel-s ≈ 5.8 board-s; Lemma P budget ≈ 1,300 board s (≈ 1.5e12 instr) beside the base D file.
- (a) Direct port: 10⁴–10⁵+ board s (tables ~9.7k, deep grid ~87k, a replayed DP ~6e5). NO.
- (b)+(c) compressed + pencil: 600–2,100 s, borderline.
- Cheapest design: pencil for y ≥ ~3–4, tails beyond u ≈ 5, S0 and constants; kernel only for the near box with Taylor-4 cells + a certified DUAL POTENTIAL for the DP. 400–900 s, total ≈ 2.05–2.55 ks, IF the potential exists and the 20–30× compression holds. Multi-pair, deep clusters and Lean Phase 2 are NOT costed.
- Rule-10 refutation spec issued by am-cert (claim "direct port cannot fit"): time one decide +kernel interval cell check of ψ_y. Refuted if mean < 0.1 ms; supported if ≥ 1 ms; prediction 1–5 ms. FOR SAM TO ROUTE.
- DECISION (Sam): finish the Lemma P math first (multi-pair: window-scope; deep clusters: bridge-port), keeping compressibility in mind; the board decision later.
**~08:00Z (Pacific 10-09 00:00) LEMMA P ROUND: convention bug found and repaired; multi-pair status.**
- CRITICAL (bridge-port, independent code e15): the Lean LemmaPObj uses ordSq (grouping by ordinate). Under ordSq, exact LP < 0 (stable in N) on stacks of m ≥ 12 coincident deep off-line zeros + a deep chain (m=16: −207). The hypothesis AS WRITTEN is not configuration-wise provable.
- REPAIR APPROVED: per-zero weights pSq (mult² on-line, 2·mult off-line) = the numeric R convention. pSq ≤ ordSq (weaker hypothesis); pSq ≥ 2N − N₀ˢ, so κ is unchanged. Old versions are kept.
- Step 8 to y₁ = 0.8 under the convention: (0, 0.4] 1.379y², [0.4, 0.8] 13.36y² (certified, double).
- Multi-pair:
  - (i) separated (≥ 32): CLOSED (certified); extension to d₀ ≈ 4 approved;
  - (ii) the geometry B&B is infeasible (~10⁶ DPs) and the concavity reduction is lossy, so both instruments fail;
  - (iii) exact-lattice blocks POSITIVE (LP_total/y² ≥ 1.74…15.18 for P = 2…32); general compressed geometry is the OPEN CORE.
  - The per-pair split (fixed θ, c) is CLOSED as an instrument (θ ≈ 0.3–0.4 vs ~0.93 needed; failures are all compressed).
  - Route decided: full-spectrum identity LP = s₂(D) + ‖S_B‖² + 2Re⟨S_D, S_B⟩, short-range DP + long-range Fourier; P_h assigned to window-scope.
- Deep (bridge-port): Q_pp ≥ 0 is FALSE for unequal-depth stacks, but exact W > 0 (R convention). Numerics: Q_pp ≥ −0.4·T_g; Λ_min ≈ 5.0–5.9 (P ≤ 32). Open: (a) stacks paid by T_g, (b) Λ_min proof, (c) unpaid near points.
- **~13:00Z window-scope multi-pair:**
  - compressed-cluster search (N = 64, positions relaxed): min LP/Σy² = 3.06 (8 pairs, Y = 0.4); NO negative case.
  - Joint environment DP (fixed geometry): the P_h-free bound is NEGATIVE on compressed blocks (block16, Y = 0.4: −0.95 vs exact +7.20), structural (cell-independent). Cause: compression moves the V peak past α = 1, out of the qf support. Density (P_h, 0.23–1.71) pays for it.
  - Lead: P_h confirmed to window-scope; density lemma GO (pencil + small DP state), pre-registered on the 5 saved geometries.
  - Next design: pair sites in the DP alphabet, to remove the per-geometry enumeration (cost estimate first).
- **~15:00Z bridge-port step 9(e):**
  - (1) Q_pp ≥ 0 FALSE for unequal deep depths (e9_cfg_16/24/32/48: −19 … −185; exact W > 0).
  - Replacement (1′) Q_pp + T_g^pp ≥ 0, exact environment-free form ‖S_A‖²_q ≥ 4g0·P + 4Σh(s_p − s_p') (checked to 1e-14). Adversarial min total 29.6–61.8 for P = 3…24, NO negative; the minimisers are arched chains at spacing 0.62–0.76; the bulk per pair → ≈1.6 = bulk T_g.
  - Pencil: equal depths and P = 2 proved; unequal depths, P ≥ 3 NOT proved. Gram, reference-depth and Schur routes each stop (written up).
  - (2) restated: Λ ~ c/P for chains, so the P-growth comes from T_g^pp (via s(D)); (2) becomes (1′)-with-margin plus an environment-field lemma.
  - Lead: edge-mode DC-first pencil attempt on (1′) GO, pre-registered (all P ≥ 3, y ∈ [0.8, ∞), explicit margin). Ownership split: deep = bridge-port, shallow dense + P_h + DP alphabet = window-scope. pSq repair status requested.
- **bridge-port Lemma LL (pencil; lead checked line by line).**
  - Statement: for an isolated cluster of P pairs, any depths, within length L, with δ ≤ 1/(4L), P(2δ·cos(2πδL)·Q̄ − h(0)) ≥ g0 ⇒ Q_pp + T_g^pp ≥ 0.
  - Mechanism: |S_A|² − 4|V|² ≥ 0 pointwise on the low band (B_p ≥ 0, cos ≥ 0), with |V|² ≥ P²cos(2πδL).
  - Explicit: P/L ≥ 5.54 + 0.0536P; m = 32 needs L ≤ 4.4 (bridge-port wrote 4.6, which the arithmetic does not support).
  - Covers the negative-Q_pp stack families IN ISOLATION. Open: localisation (dense subclusters via LL, moderate parts via the edge mode) and the cross terms. Forwarded to window-scope as a density-lemma template.
- **pSq repair DONE (bridge-port; lead re-ran the axiom check independently, 12.5 s).**
  - New files rootR8f/AMW/DEPSq.lean and DEPSqAx.lean; no existing file modified.
  - AMW.am_dyadic_R8_ratZ / am_cumulative_R8_ratZ: κ = 6759644/10⁷ under the sole hypothesis LemmaPObjZ zetaZeroConfig (qfAM 0 − cR8.y 0) (gPL cR8 0).
  - lemmaPObjZ_of_lemmaPObj: the new hypothesis is the weaker one. lemmaPObjZ_R8_online holds.
  - All 12 theorems [propext, Classical.choice, Quot.sound]; grep finds no sorry, native_decide or axiom.
- **bridge-port (B) edge-mode attempt on (1′): NOT CLOSED.**
  - Band split (sat9/e21): the margin sits in the DC LOBE (e9 P = 16: lobe 185 of 201, edge 2.4; target 65.5), not at the edge. The lead's edge-mode endorsement was wrong; recorded.
  - LL's quarter-turn lobe loses a factor ≈ 5.6 against the ideal 4q(0)ρP; the e9 configurations (density 2.8) fall outside LL.
  - Lead proposal for (a): a Fejér positive-definite minorant φ ≤ q. The |V|² part becomes Σφ̌ ≥ 0 termwise (free localisation, ideal constant for long clusters); the cross term vanishes EXACTLY on lattices (Poisson, B(0) = 0), so it measures density variation only (shared with the P_h lemma).
  - Pre-registered cheap numeric test on e9 + arched minimisers, δ ∈ {1/16, 1/8, 1/4}.
- LL constants (exact Q̄ on the 6001-point grid; q is decreasing on [0, 1]): L ≤ 1.300 / 2.471 / 4.396 / 7.143 / 10.36 for P = 8 / 16 / 32 / 64 / 128.
- Lead: explicit CANCEL of bridge-port's localisation build until the Fejér test runs. The Fejér lower bound drops the edge band entirely (the integrand is ≥ 0), so no edge cross terms remain to bound.
- **bridge-port Lemma SL (pencil; lead checked).**
  - Statement: ‖S_A‖²_q ≥ 4κΣ_p D_p + C_B, with T = (1 − |α|/a₀)₊, κ = min q/T² (= 1.008 for a₀ ≤ 0.3, grid), D_p = Σ_{p'}FT(T²)(s_p − s_p') (local density at scale 1/a₀).
  - LL's factor-5.6 loss is removed. Tests: SL ≥ target on all e9 (P = 16…48), lattices of spacing ≤ 0.76 and e12 stacks; only density 1 fails (108–124 vs 129, paid by its in-band peak). C_B ≥ 0 in every test.
  - Free deep search: P = 32 total +90.3 (all P = 3…32 positive).
  - Open: sign of C_B (lead: exact split C_B = 4κ∫T²B_*|V|² [≥ 0] + depth-difference part); sparse parts (in-band peaks); the split. GO on the depth-spread × density architecture, pre-registered; tests to include y = 5, 10, 20.
- **Fejér lobe test (pre-registered): FAILED** on short chains.
  - Ratios 0.70 / 0.86 / 0.998 / 0.988 / 0.963 for P = 3 / 4 / 6 / 8 / 12; the |V|² lobe falls short.
  - Passes on e9, long minimisers and arches. The cross term was ≥ 0 everywhere.
- **Post-hoc variant q·Fejér** (φ = q(1 − |α|/δ)₊, positive-definite since q̌ ≥ 0 and the Fejér transform is ≥ 0): at δ = 3/8 it passes ALL tested configurations (1.30–2.87).
  - NOT a pre-registered result: δ and the form were chosen after seeing the data.
  - Lead: adopt it under a FRESH pre-registration, a new adversarial search against the bound itself, δ ∈ {1/4, 3/8, 1/2}, P = 5…32, y ∈ [0.8, 20]. Pass if min ≥ 0 for every P ≥ 5. Predicted: pass for P ≥ 6, tight at P = 5.
  - P = 3, 4 get a separate small-P design (pencil or certified box). Localisation only for the sparse/mixed regime (in-band peaks via disjoint-band minorants).
- **Depth-spread × density split (bridge-port e24/e24b): NOT CLOSED.**
  - Cell A (reverse-triangle reference depth) RETIRED as an instrument: 0.74–0.99 for P ≤ 16.
  - Cell B (exact C_B split) passes all dense cells except P = 3 (0.89), and fails on deep pairs in density gaps (Y = 5: 0.97; Y = 10: 0.93), where the dropped |S_Δ|² is what's missing (E_low passes by 10⁴–10¹⁵).
  - The sparse/short cell fails even on E_low (0.95–0.98); the energy sits in the in-band comb peaks / mid band.
  - The scale-y density requirement did NOT bite: best a₀ was 0.19–0.375 even at y = 20.
  - The full ‖S_A‖² passes every test by large factors; nothing contradicts (1′).
  - Lead: q·Fejér fresh test first (gap configurations added as held-out seeds); then the angle bound (S_Δ = O(α²) at 0 vs V(0) = P), a disjoint high-band minorant / weighted Ingham for sparse, and a small-P design.
- **Fresh pre-registered q·Fejér test (bridge-port e25): FAILED for every P ≥ 5** (min [bound − target] ≈ −1.7P). Lead prediction REFUTED.
  - The minimisers are sparse chains (spacing 1.65–1.9, depth ≈ 0.8–0.9). Their true margin is +1314 … +5.6e5, 97–99.99% in the high band (comb peak α ≈ 0.55).
  - Lead's test-design error: the lobe alone was asked to cover the sparse cell, which had already been assigned to the high band.
  - Pinned deep pairs (Y = 5, 10, 20) PASS (+2.7e3 … +1.2e6).
  - NEXT: a combined partition-of-unity bound, Q_pp + T_g^pp ≥ T_g^pp + (ii)_T + (iii)_T − 4∫q(1−T)|S_Δ|²/(c_*² − 4), pre-registered: an adversarial search for P = 3…32, PASS = min ≥ 0 everywhere. Predicted: pass, except possibly large-spread gap configurations with a global c_*.
  - Small-P design approved, build held.
- **bridge-port queue (1)–(4) (e26/e27).** Worst ratio per piece:
  - q·Fejér: 0.57, FAIL (sparse);
  - angle bound: 1.50 in pencil, 1.90 exact (|cos θ| ≤ 0.28, exact); the remaining step is a pencil bound on the low-α share;
  - high band: ≥ 48.6× numerically, but the pencil Ingham constant for w_h = q(1 − T_{1/2}) exists only for min gap ≥ 1.25 (r = 0.998 at gap 1). The lead's "½ threshold" was wrong for this weight.
  - HOLE: min gap in [1, 1.25).
  - Small P: design only.
  - Next: the combined partition-of-unity bound (needs no Ingham, no min gap), pre-registered, with hole configurations added as seeds.
- **Combined partition-of-unity bound (bridge-port e28): FAILED; lead prediction REFUTED.**
  - (A) global c_*: fails at every P (exponential loss at large depth spread, e.g. −1e101 vs truth +1e105).
  - (B) pointwise-optimal c: P = 3–6 pass thinly (+0.21 at P = 6); P ≥ 8 fails (−2.3 … −36.7) on sparse chains (truth +1.3e6 … +8.9e9).
  - Exact reason: minimising over V makes the high band ≤ 0, discarding the comb-peak energy (c² − 4)|V|² where sparse margins live. This was the lead's design error.
  - Lead tally today: 3 refuted predictions (Fejér, q·Fejér-fresh, combined) plus the edge-mode endorsement.
  - NEXT: a θ-split (Young) with an explicit c rule (depth-class split), pre-registered, no lead prediction.
  - GOVERNANCE: this is the last relaxation round. If it fails, stop and report the state; the lead decides with Sam between a computer-assisted core and pausing (1′).
- e28b hole seeds (min gap 1–1.25):
  - Flat depth passes thinly (+3.9 … +7.4; truth +2.3e3 … +5.9e4).
  - Arched depth: the primary fails; the optimal-c diagnostic passes at the seed but fails for P ≥ 8 after the adversary.
  - The combined-bound FAIL stands. θ-split GO re-sent (the third crossing).
- **window-scope DENSITY LEMMA: pre-registered PASS.**
  - Statement: P_h ≥ 2Σm_a·v(x_a) − (1/N)Σ|c_j|²/ĥ_j (pencil, exact; a DP one-body potential).
  - All 5 saved geometries are now ≥ 0 (+0.11 … +1.23), plus block32/64 (+0.17 … +0.76); double precision, line model.
  - Recovered +0.07 … +1.22 of the exact P_h 0.23 … 1.71. The earlier negatives were relaxation artefacts (exact LP of that environment is +11/+13).
  - Certified dense-block margins are thin: 0.0027–0.05 per pair.
- **Class (i)**: closed to separation 16 for depths ≤ 0.8 (+1.35y²), 8 for ≤ 0.7375, 4 for ≤ 0.1875. Mixed-depth bookkeeping pending.
- **Pairs-in-alphabet DP**: estimated INFEASIBLE by orders of magnitude (a cost estimate for that instrument).
  - Alternatives: (C) a geometry-reduction lemma ("uniform compressed block + edge profile is worst"), then a 2–3-parameter B&B of ~10⁴ DPs ≈ 4 days on one thread; (D) the geometry-free two-body certificate, which costs κ (≤ 0.6735).
  - Lead: the (C) plausibility test GO (~20 DPs, pre-registered). Reduction lemma / B&B build HELD for a decision with Sam.
- **θ-split (bridge-port e29, last relaxation round): FAIL at every P ≥ 5. STOP per governance.**
  - The within-class loss binds at large depth (P = 8, y ∈ [14.99, 15.26]: −8e78 vs truth positive). bridge-port's prediction was half refuted.
  - STATE OF (1′):
    - Complete pencil proofs: P ≤ 2; equal depths (any P); isolated dense clusters (LL).
    - Proved reductions with an open input: SL (sign of the depth-difference part), the angle bound (low-α share), Ingham at min gap ≥ 1.25 (unequal depths).
    - UNCOVERED, with true margins:
      - moderate-density arched chains (spacing 0.6–0.8, depth 0.8–1.6): min 29.6 at P = 12, ≈ 2.5/pair, bulk ≈ 1.6/pair (= T_g). THE binding regime.
      - sparse ≥ 1.3e3; hole ≥ 2.3e3; deep/large spread ≥ 1e20; stacks-mixed ≥ 135; P = 3/4: 57/42.
  - Board context: budget ≈ 2,600 s per job; the base D file ≈ 1.65 ks, leaving ≈ 1,300 board s for all Lemma P certificates. In-class headroom: edge windows +2e-5, n = 9 ≤ 3e-5.
  - Decision to Sam.
- **SAM DECISION (10-09): FOCUSED CORE PUSH on the binding regime**, time-boxed to 3 pre-registered rounds, then re-decide.
  - Scope: moderate-density chains, depths in [0.8, 3]; deep pairs (y > 3; truth ≥ 1e20) go to a separate deep-pair lemma later.
  - Round 1 (bridge-port):
    - (1) a numeric pre-registered test of lobe + θ-split with depths capped at 3;
    - (2) pencil bulk/end decomposition for dense chains: exact lattice Q_pp per pair → 0 (in-band spectrum only at α = 0, B(0) = 0), T_g ≈ 1.2–1.6/pair pays bulk + O(1) ends; lattice-with-ends computed exactly first.
  - window-scope continues the (C) plausibility test; the enumeration build stays held.
- window-scope:
  - (C) plausibility test REFUTES "uniform interior + edge spacing is the worst case", as predicted (6/8 lower by up to 3.15). Long blocks grade over ≥ 10 spacings, so a reduction would need a 3–4-parameter graded edge profile plus depth.
  - Mixed-depth class (i) CLOSED (double precision; radii 2/4/14 by depth class; the cluster-slack check 0.957 is SAMPLED).
  - Shared DV lemma recorded.
  - Round 1 (focused push): a bulk/end lemma for shallow dense blocks (pre-registered: is the end deficit bounded in P?) plus making the slack check exhaustive.
- bridge-port was re-sent Sam's outcome (it was holding); round 1 started.
- **Core push round 1 (bridge-port e30/e31):**
  - (1) numeric (depths capped at 3) FAILED at every P (θ-split loses an O(1) fraction of class energies ~1e13); bridge-port's prediction refuted.
  - (2) EXACT lattice-with-ends: equal-depth closed form; C_end(a, 0.8) = 209–769; τ(0.76) = 1.257.
    - Profiled lattices: min Q_pp ≈ +15 (stable in P, an END term; arch profile cancels ≈ 93% of C_end).
    - Irregular P ≥ 16 minimisers trade Q_pp (4.9–16) for T_g (27–85).
    - Target (E): end positivity on lattices for any profile.
  - Lead independent check (/tmp/lead_chk/endpot2.py): on lattices with a < 1, the cross term 4Re⟨S_B, V⟩ = Σ one-body END potentials (Poisson), exact to 1e-14. The one-body terms alone go to −1e5 at depth, so ‖S_B‖² must pay.
  - Round 2: a depth-free reduction via the dual test function, Q_pp ≥ 4Re⟨S_B, W⟩ − 4‖W − V‖² (equality at W = S_A/2). W depending on positions only eliminates depths pair by pair, giving a positions-only inequality D(s) ≥ 0. Pre-registered numeric test; no lead prediction.
- **window-scope round 1:**
  - Cluster-slack allocation EXHAUSTIVE (sup ≤ 0.9949), so class (i) mixed depth is closed exhaustively (double precision).
  - Bulk/end lemma REFUTED (as predicted): the deficit grows with P; minimisers' centre spacing drifts → 1 and the grading length ≈ 0.07P. m_bulk(a) by Poisson: 0.119 (a = 0.97) … 0.021 (a → 1).
  - CERTIFICATE LOOSENING: rb64 at Y = 0.4 has DP bound −0.164 vs exact LP +10.31; LB at Y = 0.4 falls 0.73 → 0.39 → −0.16 for P = 16/32/64.
  - Round 2: tighten the far field (pre-registered: LB(rb64, Y = 0.4) ≥ 0 and non-decreasing in P), then a local-density comparison LB vs Σ m_bulk(a_p).
- **Core push round 2 (bridge-port e32d, exact convex QP, two-sided certificate):** positions-only reduction D(s).
  - Lattices with a ≤ 0.8: certified PASS (P = 6…48, D ≈ T_g − O(1); decoupling loss ≈ the depth-profile end term).
  - Certified FAIL at a = 0.9 P = 12 (P = 48 undecided) and on irregular e23 P = 12…32 (−5.4 … −109; truth +29 … +90).
  - Earlier solver numbers (e32/e32b) were artefacts, disregarded.
  - Binding regime splits:
    - (A) near-lattices, gaps ≤ 0.8: reduces to geometry;
    - (B) gaps → 1 (T_g → 0) and irregular/coincident: depth coupling needed.
  - Round 3 (LAST): class-resolved D_K (K = 2/4/8, α-profile W family) on the (B) failures, pre-registered; plus near-density-1 thinness numbers and saving the (A) witnesses W*.
- **window-scope round 2:**
  - (1) PASS: signed IBP far field + XL 1024 → certified LB at Y = 0.4: +1.318 / +1.444 / +1.628 (P = 16/32/64), at Y = 0.2: +0.315 / +0.531 / +0.882. rb64 is now ≥ 0, increasing in P (double precision). An aliased-quadrature scan was caught and discarded.
  - (2) Local-density comparison (as predicted): certified LB − Σm_bulk(a_p) is unbounded (the certificate gains 0.0065/pair vs 0.046 available). EXACT LP ≥ Σm_bulk(a_p) on all six with no gradient term, the margin growing. The gap is the DP environment relaxation (no mass conservation).
  - Round 3: a far-profile max–min test (pre-registered > 0.3 gain) + a cost estimate for mass-count DP state.
- **Core push round 3 (bridge-port e33/e34):**
  - Depth-class-resolved D_K with an α-profiled W PASSES on every tested configuration already at K = 2 (lattice a = 0.9 P = 12/48, e23 P = 12…32; loss ≤ 3.8 except a = 0.9 P = 48 at 33.8 → 1.9 by K = 8). The two-sided QP certificate covers ONLY the labellings tested (L0 + greedy), not all K^P.
  - Regime (B) reduces to positions × 2 labels; a labelled chain DP is the certification route, and it needs a LOCAL W rule (asked).
  - Bulk per-pair margin = τ(a) EXACTLY (periodic identity): 0.65 (a = 0.85), 0.30 (0.9), 0.091 (0.95), 0.019 (0.99), 0.0055 (1⁻); ≫ 1 for a > 1. Thinnest at a → 1⁻.
  - Regime (A) witnesses W* saved (16 lattices, D > 0).
- **Locality of the optimal W (bridge-port e35): NOT local in a usable sense.**
  - (A) structure looks local (interior w constant, end pattern ~6 sites), but transplanting the end patterns to P = 48 gives D = −1e4 … −5e6 (optimum +42 … +123).
  - The dual is STIFF: the one-body min over y up to 3 has coefficients ~1e6, so δw = 1e-2 costs ~1e4/pair.
  - (B) the response is GLOBAL: one label flip changes w by ~1e3 at every distance; truncated updates give −7e4 … −3e10.
  - Options (untested): narrower depth range for the min (stiffness ~ e^{4πy_max}); a regularised dual; a DP carrying W coefficients in a finite basis (transfer).
- **window-scope round 3:**
  - (1) Far-profile charge SUPPORTS (+0.63 on rb64 at Y = 0.4; prediction held). Certified slope now 0.0193/pair (Y = 0.4) vs thinnest margin 0.021.
  - (2) Exact P_h of a density-2 stretch computed (low band → ĥ(0)L; cheapest compensation ≈ 0.026/L). The mass-count DP (10–15× cost) would gain only ≈ 0.002–0.005/pair, so it is NOT worth building. The hard-bin minorant is impossible for certificate v1's ĥ (ĥ ≡ 0 on several intervals).
  - FLAG: "exact LP ≥ Σm_bulk" was measured only at N = 4P (env density 2/3). A density-1 locked environment is untested; the cheap test is the exact LP at N = 16P (pre-registered: increasing in P supports).
- **END OF FOCUSED CORE PUSH (3 rounds).** State taken to Sam.
- **SAM DECISION (10-09, after the core push): COST THE PORT FIRST.** n=9 processes 88815/88816 KILLED (Sam: kill).
  - am-cert: full Lean/board cost estimate of the current Lemma P architecture vs ≈ 1,300 board-s (pre-registered: if the low estimates of the known pieces exceed 1,300, the architecture does not fit).
  - window-scope: the exact N = 16P test (pre-registered).
  - bridge-port: answers sizing questions; holds on math.
- am-cert PRE-REGISTERED PREDICTION (before reading sources): the current architecture does NOT fit (≈ 65%).
  - Piece 1 low ≈ 400 s; the interval upgrade multiplies cell pieces by 2–5×.
  - One piece-4 DP at site resolution 0.02 over XL = 1024 is likely ≥ 1,700 board-s on its own.
  - Expected exception: piece 2 cheap (≈ 10–60 s).
- **window-scope N = 16P exact test: SUPPORTS (as predicted, ~70%).**
  - LP − Σm_bulk(a_p) increases in P at both Y:
    - Y = 0.2: +0.55 / +0.89 / +1.37;
    - Y = 0.4: +2.08 / +2.26 / +2.75.
  - Environment density 0.93, locked to the block's phase.
  - Local minima from 3 start families; global minimum not certified; double precision.
  - CORRECTION to round 2: the N = 4P exact margins were single-start local minima, overstated by 0.36–1.55. Corrected values still increase.
- **am-cert LEMMA P BOARD-COST ESTIMATE (10-09, nothing built).**
  - Ported AS-IS: known-size low ≈ 7.8e6 board-s, so it DOES NOT FIT (the pre-registered branch fires).
  - COMPRESSED (Taylor cells, pencil tails, banded DP): known-size low ≈ 743 s, high ≈ 1.7e5.
  - The deep-chain witnesses (piece 3: 180–3,300 s per unit) and the dense-block DPs (piece 4: 430 s per DP) have an UNBOUNDED or UNKNOWN count. One unit of each already gives ≈ 1,353 > 1,300.
  - Binding condition: a locality/covering lemma that makes 3 + 4 ≈ one unit total, plus nine more conditions (GIv engine extended to the Lemma P functions at ≤ 5 ms/cell, which is NOT built; banded-DP lemma; cluster monotonicity; pencil tails; …).
  - The measured current cell path (0.82 kernel-s/cell) is 160× over the low assumption.
  - Cheapest refuting experiment named (not run): the W transplant (e35a) at r = 16/20/24.
  - am-cert prediction: confirmed for as-is, refuted for compressed known-size.
- **SAM DECISION: RUN THE CHEAP REFUTING TEST FIRST.**
  - bridge-port: W transplant P = 64 → 128 at r = 16/20/24, a ∈ {0.6, 0.7, 0.76, 0.8}; PASS = certified D ≥ 0 at some r ≤ 24 for all four.
  - window-scope: C2 banded DP (r ∈ {1, 2, 4}) and C3 cluster monotonicity.
  - Then: all pass ⇒ am-cert re-prices with finite counts; otherwise pause the board route and write up.
- am-cert ADDENDUM (bridge-port sizes):
  - Piece 3 per lattice chain ≈ 500 s low without the endpoint lemma, ≈ 12 s with it (min over y at 0.8 or 3; unproved, now condition 11).
  - Minimal-count total: 1,673 without vs 1,185 with (budget 1,300).
  - Endpoint check added to bridge-port's refuting round (pre-registered).
- **W TRANSPLANT (bridge-port e36): FAIL** (certified; r = 16/20/24, all four spacings, losses 1.4e4–3.5e5). The QP-optimal witness interior is NOT converged in P (degenerate interior); bridge-port's prediction refuted.
  - ⇒ Per the pre-registered rule, the **BOARD ROUTE FOR LEMMA P IS PAUSED.**
  - Write-up assigned: bench/window/LEMMAP_NOTE_{deep,shallow,cost}.md (new files) + the endpoint (C11) and C2/C3 checks to finish for the record.
- **ENDPOINT LEMMA (condition 11; bridge-port e37): REFUTED** (as bridge-port predicted).
  - 440 pairs have interior y-minima (y ≈ 2.5–2.93) below both endpoints. Dips: positions-only ≤ 0.14, D_K ≤ 0.54; checked on a 4× finer quadrature.
  - Mechanism: B_{y'}/B_y monotone in α is TRUE (pencil: x·coth(cx) increasing); g_p single sign change is FALSE (4–213).
  - ⇒ No 40× saving; the minimal-count total stays ≈ 1,673 (> 950 conservative, > 1,300 nominal).
- Budget figures: ≈ 950 (2,600 s safe rule − 1.65 ks base) conservative, ≈ 1,300 nominal (3,240 s timeout − base − margin). PC8E was accepted at a predicted 2,632 s.
- bridge-port: endpoint check done (REFUTES); LEMMAP_NOTE_deep.md written. The lead's identity check was copied to sat9/lead_endpot_check.py (+ .log, rerun, 1e-14) so the note's pointer is durable.
- am-cert: condition 11 filled REFUTED.
  - Own revision [estimated]: interior minima at slopes 10²–10⁴ need ≈ 170 subcells/pair on y ∈ [2.4, 3], so a lattice chain is ≈ 920 board-s low (was 500). Finite within one chain; the FAMILY of chains is unbounded.
  - Minimal-count total ≈ 1,673–2,093, over both budgets. The 1,185 figure (which depended on condition 11) is withdrawn.
  - Pending: conditions 2/3 (window-scope) and the shallow note.
- window-scope round 5:
  - C2 banded DP PASS (r = 2/4 lossless; r = 1 keeps all classes closed).
  - C3: W monotone in p exactly, but saturation needs up to 6 (B) / 15 (C14) levels at u < 1 (≤ 3.5% of cells). PARTIAL.
  - Passed to am-cert; shallow note requested.
- **am-cert FINAL COST NOTE (complete).** Unit correction: condition 2's band was tested in DISTANCE u (r = 1 ⇒ 256 forward cells at the 1/256 near-pair grid), not in cells.
  - Re-priced [estimated]: piece 2a ≈ 8,800 board-s low; piece 4 ≈ 4,000–7,600 per DP; compressed known-size low ≈ 9,260; min-count ≈ 14,200. DOES NOT FIT either budget.
  - Untested reversals (a cell-scale band, a coarser near-pair grid) would bring the known-size low back to ≈ 680, but condition 9 is refuted, so the cost stays unbounded.
  - Superseded figures (743, 1,673, 2,093, 1,185) are kept and marked.
- **Lemma P state note COMPLETE:** bench/window/LEMMAP_NOTE_INDEX.md (index, lead) + _deep (bridge-port) + _shallow (window-scope) + _cost (am-cert).
  - window-scope disclosed a round-2 w-cell-bound under-allowance (2β vs 2.388β; ≤ 1.3e-5 per unit environment mass). Rerun of the affected rows approved.
- window-scope rerun with the corrected w-cell bound (band1/round6_rerun_{A,B,C}.log): NO sign change; every row rose (the other round-2/3 bound improvements dominate).
  - Saved geometries: 0.121 … 1.502.
  - Graded Y = 0.2: 0.352 / 0.571 / 0.950, slope 0.0125/pair.
  - Shallow note §4 updated; open item 3 closed. **D-track record closed for this session.**
- **10-09 (Sam: "work on what Lemma P needs") — math only, no board target.**
  - Skeleton: Lemma P ⟸ single pair [DP ✓] ∧ separated y ≤ 0.8 [DP ✓] ∧ deep pair–pair (1′) [partial] ∧ deep + environment [UNTESTED] ∧ shallow dense [per-geometry, no covering] ∧ mixed shallow/deep [UNTESTED] ∧ glue [open] ∧ rigour [open].
  - STEP 1 = truth check of the two untested leaves (the inhabitant check of the full statement). Full exact LP adversarial search, cancellation-free + mpmath re-evaluation; bridge-port = deep + environment, window-scope = mixed.
  - Pre-registered: any confirmed LP < 0 ⇒ Lemma P false configuration-wise, retarget.
  - Lead prediction: SUPPORTS (~70%), thinnest < 0.01/pair in near-density-1 deep chains with environment.
- **STEP 1 deep + environment (bridge-port e38): SUPPORTS on the searched range.**
  - min LP +21.4 (P = 8); thinnest per pair 0.906 (N = 128, P = 32); total ≈ P-independent (end term ≈ 25–30 + small bulk slope). The environment did not lower the minimum below the pair–pair values.
  - Lead prediction (< 0.01/pair) NOT observed (it needs chains of ~1e3+ pairs).
  - FLAG e38b: fixed near-density-1 lattices (a = 0.95/0.99) at fixed N = 256 have LP decreasing in P (−1.4 … −17 per pair) while the environment thins.
  - N ∝ P scaling test ordered (pre-registered).
- **STEP 1 mixed shallow/deep (window-scope round 7): SUPPORTS** (670 runs; mp50 confirmation of the 132 runs with LP < 1, max |mp50 − float| = 8.5e-13).
  - Deep pair inside an rb block: min LP 2.877 (mp50 2.8767081389), thinnest 0.049/pair (s(D) 5.46, Δ_B −2.58).
  - Random mixtures: 3.529. Flanked: 18.4. Stacks under pSq: 61.7. Real limit (y → 0): LP = s(D) ≈ Nσ.
  - Deep pairs always relax to the y = 0.8 bound. Family-d design flaw reported (all pairs collapsed to y → 0); family e added before running.
- **N ∝ P scaling (bridge-port e39):**
  - FREE positions SUPPORT (slope +0.14 … +0.51/pair). FIXED a = 0.95 SUPPORTS (positive by P = 128).
  - FIXED a = 0.99: the PRE-REGISTERED RULE FIRED via its extrapolation clause (slopes −12.7, −11.3, −6.8 through P = 128; extrapolated zero at P ≈ 320). Recorded as fired.
  - Post-registration (unconverged, upper bounds): P = 256 ≈ 920 (slope ≈ −3), P = 512 ≈ 1109–1142.
  - Lead: the extrapolation clause was badly designed (it cannot tell a trend from the decay of a positive finite-size lobe term; near-pole at 1/a = 1.0101, decay for P ≳ 99).
  - DECISIVE test ordered: the exact asymptote (C_end + profile minimum, pair–pair) + a converged trust-region minimisation at P = 128/256/512. Lead prediction SUPPORTS (~75%).
- **!! LEMMA P (pSq) REFUTED CONFIGURATION-WISE (window-scope round 8; mp50 + independent e15 code, 8 digits).**
  - Configuration: an ON-LINE zero of multiplicity M ≥ 5 flanked by shallow pairs. LP = −3.198 (M = 5), −8.12 (6), −18.2 (8), −36.2 (10), −61.8 (12) at N = 256; N-stable small cases (N = 64, M = 5, P = 4: −0.288).
  - Mechanism: LP = s(D) + y²Q₂ + …, Q₂ ≈ 24 − 7M; the slack of an isolated multiplicity is only ≈ 0.0096M².
  - Round 7 scoped to M ≤ 3. Without M ≥ 4, sup R = 0.44–0.64 (growing with block size). Lead θ* prediction refuted.
  - The Lean hypothesis LemmaPObjZ is asymptotic (εN), so it is violated only by a positive density of such clusters. It is NOT provable configuration-wise as written.
  - REPAIR proposed (lead), κ-NEUTRAL: linear weights (1 simple on-line, 2M on-line M ≥ 2, 2m off-line) ⇒ pLin = 2N − N₀ˢ exactly; hypothesis h₀N + g₀(2N − N₀ˢ) − εN ≤ frobSq (weaker than LemmaPObjZ).
    - LP_lin = LP + g₀Σ(M² − 2M): the family becomes +4.5 … +57.1.
    - Adversarial validation of LP_lin pre-registered (window-scope); Lean held until it reports.
- bridge-port e39c: fixed a = 0.99, N = 4P, P = 512 at 10k iterations: 910.95 (slope 256 → 512 ≈ −0.03/pair; the earlier +0.7 withdrawn as non-convergence). The family plateaus ≈ 910–920 (unconverged upper bounds; gradient norm 6e2–4e3). Decisive converged test re-sent.
- **pLin REPAIR VALIDATED (window-scope round 9, pre-registered): SUPPORTS.**
  - min LP_lin +3.12 (M = 3); single multiplicity M = 4 … 20: +7.7 … +139.9; flanked by stacks ≥ +19.1; multiple multiplicities ≥ +6.1. LP_lin ≈ 0.30·M² at large M (R_lin saturates ≈ 0.69).
  - Collateral (mp50): pSq already FAILS at M = 4 (−0.2487; 16 pairs, N = 64); M = 3 is +0.146.
  - Lean: am-cert building DEPLin.lean (new file; LemmaPObjL with pLin = 2N − N₀ˢ; κ unchanged).
- **DEPLin COMPILED (am-cert; lead re-ran the axiom check):** rootR8f/AMW/DEPLin.lean + DEPLinAx.lean (new files).
  - pLin_add_N0s (pLin + N₀ˢ = 2N EXACT).
  - lemmaPObjL_of_lemmaPObjZ / _of_lemmaPObj.
  - am_dyadic_R8_ratL / am_cumulative_R8_ratL: κ = 6759644/10⁷ under the sole hypothesis LemmaPObjL.
  - lemmaPObjL_R8_online.
  - All 13 theorems std axioms. The index note is updated.
- **Decisive a = 0.99 test (bridge-port e40/e41): UNDECIDED.**
  - e40 negatives VOID (bug: the gradient-norm variable shadowed g(0); caught before reporting).
  - Full LP converged: P = 128 +1303.4, P = 256 +871.2 (PD Hessians). P = 512 unconverged ≤ 671.1; that descent is environment DIMERISATION far from the chain (bulk relaxation of the density-0.66 environment, unrelated to the pairs).
  - Pair–pair Q_pp profile minimum, converged: 1847.9 / 1401.7 / 946.7 (P = 64/128/256); asymptote not established. C_end(0.99, 0.8) = 2127.
  - Next (pre-registered): (i) environment-only baseline subtraction; (ii) converged end term (E) at P = 512/1024. The sign of the semi-infinite end term decides the family.
- **bridge-port e42 interim (a = 0.99 separated test):**
  - Environment baseline s_env* = 0.00138/unit (dimerised), so the environment explains ≤ 76; the earlier attribution is withdrawn.
  - LP_chain +1292 / +861 / ≤ +578 (P = 128/256/512). Q_pp at P = 256: a = 0.95 ≤ 103.7, a = 0.90 ≤ 23.0 (interior depths → 2.3–2.5).
  - CORRECTION: the e31b "end positivity ≈ +15–27 / 74–82" were NOT global minima.
  - Lead model (not a result): a power-law decaying positive arch term (≈ P^−0.58) + 0.019P, family minimum ≈ +250 at P ≈ 5000.
  - LAST round on this family: a scalable FFT evaluator on exact lattices, P up to 8192 (refute-or-trend, pre-registered).
- **Scalable round on the near-density-1 family (bridge-port e43/e43b): UNDECIDED — LAST NUMERICS ROUND (per plan).**
  - The exact-kernel evaluator is VALIDATED (closed-form K = G(u)G(−u); Gauss–Legendre; matches the double sum to 3e-11 relative). Side finding: the dense 6001-point trapezoid had ~0.1% error (948.02 vs 946.73); no verdict changes.
  - The optimiser cannot track minima beyond P ≈ 256 (stiff deep interiors). Upper bounds at P = 512–2048 are far above the dense minima. No (1′) < 0 anywhere; smallest seen +99.6 (a = 0.90, P = 256).
  - Family state: all converged values (P ≤ 256) positive; all upper bounds positive; trend unresolved.
  - Forward options: Newton continuation P → 1.1P, or a continuum/WKB end-term analysis.
- **SAM DECISION: ANALYTIC END-TERM STUDY (bridge-port, 2 rounds, pencil first).**
  - Lead reduction, exact (Abel): Q_pp = ∫ q/(4sin²(παa))·[|c_0 + ΣΔc_p z^p − c_{P−1}z^P|² − 4|1 − z^P|²]. The interior enters only via Δc.
  - Decoupled semi-infinite END FUNCTIONAL E_end[c] = ∫ q/(4sin²)(|Σ_{p≥0}Δc_p z^p|² − 4), P-free; the near-pole resonance sits at α ≈ 1 for a ≈ 1.
  - Round 1: (a) verify Abel + decoupling vs converged P ≤ 256; (b) minimise E_end (L ≤ 400, y_∞ ≤ 5); (c) a pencil lower bound. Pre-registered.
- **End-term study round 1 (bridge-port e44):**
  - Abel form VERIFIED (≤ 1.6e-9).
  - Decoupling NOT reached at P ≤ 256 (single arches).
  - min E_end positive everywhere, not certified: a = 0.99 converged 840/685/501 (L = 50/100/200), ≤ 346 (L = 400); a = 0.95 ≈ 36, a = 0.90 ≈ 10 (upper bounds); y_∞ saturates ≈ 2.3.
  - Lead's "near-pole binds" REFUTED: near-pole band positive; binding = a small low-band dip (α ≈ 0.04–0.09) against a shrinking mid-band energy.
  - Round 2 (last), pre-registered: converged a = 0.99 to L = 1600; END DEPTH FREE (shallow ends on deep chains, untested); a pencil mid-band asymptotic.
- **End-term round 2 interim (bridge-port e45):**
  - FREE end depth: E_end < 0 FOUND (a = 0.99 converged −0.044/−0.079/−0.127 at L = 50/100/200, ≈ L^0.7; a = 0.95 ≈ −0.21; a = 0.90 ≈ −0.15). (E_∞) is FALSE for shallow ends; lead prediction refuted.
  - EVERY finite mirrored chain has (1′) > 0 (min +1.423 at a = 0.99, P = 100; T_g ≈ τP pays 6–800×). NO counterexample.
  - Verdict UNDECIDED under the rule; the rule was mis-aimed (E_end's sign is not decisive; (1′) = 2E_end + τP is).
  - End depth ≥ 0.8 branch: ≤ 340 (L = 400), ≤ 307 (L = 800), unconverged.
  - Pencil: stretching → E_const(y_0) ≥ 0; the minima come from interference.
  - Last point: a = 0.999 (τ → 0.0055), then close the family.
- **End-term round 2 part (2) COMPLETE (e45_2, e45f):**
  - Free-end min E_end ∈ [−0.21, −0.04] across a = 0.90/0.95/0.99, L ≤ 400. At a = 0.99 |E_end| growth DECELERATES (×1.80, ×1.61, ×1.39 per doubling; appears to saturate ≈ 0.2–0.3).
  - ALL 72 mirrored finite chains have (1′) > 0 (min +1.423; L = 400: +14.6/+72.0/+241.5). No counterexample.
  - Candidate analytic target: sup_L |E_end| ≤ C(a) (data: C ≈ 0.15/0.21/~0.3).
  - Pending: a = 0.999 point; L = 1600 (y_0 ≥ 0.8).
- **a = 0.999 point (e45g):** E_end ≥ −0.012 (L ≤ 200; interference only at L ~ 1/(1/a − 1) ≈ 1000). Worst mirrored chain (1′) = +0.592 (P = 100).
  - **DEEP-CHAIN FAMILY CLOSED: no counterexample** (90 chains, all (1′) > 0).
  - Candidate lemma: (1′) ≥ τP − 2 sup|E_end|. The deep note and index are updated. L = 1600 (y_0 ≥ 0.8) still running.
- L = 1600 landed (a = 0.99, y_0 ≥ 0.8): min E_end ≤ +286.4 (unconverged). Sequence 840/685/501/≤340/≤307/≤286; decrements flattening (−155, −184, −160, −33, −21), consistent with a positive limit in the mid-200s (not established). Deep note §3 updated. **Lemma P session work complete; all teammates holding.**

## 2026-10-10 — BOARD: retake #1
- The board shows a new #1: R. Arun Chandru "master-of-puppets", κ = 66812491/99194876 = 0.6735478 (10-09 17:13Z; GPT-6 Astra · Codex). We are #2 (PC8E 0.6735015), gap 4.6e-5.
  - Their file is built on our attempt-016 and RETAINS Sam's notices plus our exact eight-point certificate. It removes edge-window/√ consumers and adds clipped-Gram pinching + a separated-set Gram bound (clipC 2, normS 19/10, d 17/20, 8-point frames; modules Simple673/Distinct839/Pantera/Opeth).
- SAM DECISION: build on theirs WITH full credit. Copy at bench/arun/MOP_Solution.lean (sha f7ef331e…), SOURCE.md written.
- Estimate round:
  - am-cert: κ formula F(constants) + local compile and budget;
  - window-scope: edge windows into their chain + sensitivities + cap position;
  - bridge-port: sharpness of normS = 19/10.
- **am-cert CHAIN MAP:** κ₀ = (H⁻ − B)/(1 − c) EXACTLY (AMCounting.proposedQ_identity).
  - H⁻ = 0.67216841 (OUR window), B = 0.0040435 and c = 0.00805124 (OUR PC8C5BF). Side condition c ≤ 1/64.
  - It is the m → ∞ limit of our block formula (full linear defect via matching + pinching + the separated spectral cap 1.966 < 2; boundary loss 7c).
  - ⇒ edge windows are irrelevant; normS/d are side constants. Levers: certificate (B, c) re-optimised for this objective; n-point frames; window H.
  - Redirected: window-scope = ceilings for 8/9/10-point; bridge-port = does the chain generalise in n.
- **window-scope estimate (bench/arun/est/ESTIMATE_STATE.md):**
  - Edge windows: 0 (structural). d/normS/clipC: 0 (feasibility only; d ≤ ≈ 0.97). Re-optimised 8-point weights: ≈ 0 (PC8C5BF already optimal for the same trade-off).
  - ONLY cheap gain: certified floor → true min of W8 (0.00805124 → 0.00805165) = +2.8e-7 (needs a cover re-run at a relative margin < 5e-5).
  - Larger: n = 9 ≤ +3e-5 (byte cap: MOP is 1,858,713 B of 2,000,000; ~10× leaves); rank ≥ 8 credit ≤ +3.1e-5 two-level, idealised κ(15) − κ(7) ≈ 1.0e-4. Their full defect already includes all pairs; W8 credits only rank ≤ 7.
  - Position: 2.38e-4 below the R8 dual cap 0.6737854.
  - Pending: am-cert budget, bridge-port n-generalisation.
- bridge-port e46 (separated-Gram sharpness, lateral): true Λ(17/20) ∈ [1.6588, 1.6679] vs 1.927 used. The two-sinc majorant shape is optimal (within 3e-6); only the amplitude is loose. κ effect NIL (only "≤ 2" is used). The n-point generalisation question is still pending.
- **bridge-port n-generalisation (pencil):** CONSTANT-ONLY. κ_n = (H − B_n)/(1 − c_n); one ~20-line neighbour-count lemma; c ≤ 1/64 can relax to ≤ 0.01668 in one line. Conditional structural change only if the new certificate is certified on gaps ≥ 17/20 (thread the separation through block_energy_band). Flag: a capped-spectrum Psi lever (not pursued).
  - ⇒ The race is certificate size vs budget. am-cert asked for time headroom + byte composition (dead code outside the final theorem's cone) + the largest certificate that fits.
- **window-scope frame ceilings on (H − B)/(1 − c)** (exact rank-limited Lemma 5.1, B cancels; upper bounds; n = ∞ reproduces the R8 cap to 2e-6):
  - n = 8: 0.6735638 (+1.6e-5; realistic ≈ +1e-5 after the ≈ 5e-6 coboundary loss);
  - n = 9: +5.7e-5; n = 10: +1.03e-4; n = 16: +1.88e-4; n = ∞: +2.62e-4.
  - Window re-optimisation at n = 8: no gain (R8 sits at a multi-word balance).
  - ⇒ Feasible levers: (i) a RE-OPTIMISED 8-POINT certificate (same size class as PC8C5BF, ≈ +1e-5); (ii) n = 9 (+4–5.7e-5, ~10× leaves, byte/time permitting). Awaiting am-cert's budget.
- **am-cert budget (2):** MOP compiles unchanged in private root bench/specroot_mop (build 425 s, replay 243 s / kernel 195.5 s; std axioms).
  - Instruction ratio vs PC8C5BF (actual 2,319) ⇒ MOP ≈ 2,370 s board. Headroom ≈ 230–260 s soft (≈ 2.7e11 instructions), ≈ 870 s to the 3,240 hard timeout. Bytes 1,858,713 (≈ 141 KB under the cap).
  - ⇒ Route 1 (a re-optimised 8-point cert of the same size class) should fit; route 2 (n = 9, ~10× leaves) needs the dead-code strip (pending (b)/(c)).
- am-cert refined stage model: MOP ≈ 2,336 s (≈ PC8C5BF + 17 s). Headroom ≈ 264 s (2,600 rule) / 296 s (PC8E level) / 904 s (hard timeout). Dead-code composition (b/c) pending.
- **am-cert (b)(c):**
  - The dead-code strip (MOP_S2, measurement only; notices must be restored) frees ≈ 142 KB net and ≈ 103 board-s ⇒ ≈ 2,233 s.
  - NEW TRAP: @[simp] rfl lemmas dead in terms but needed by simp; keep attributed dead declarations.
  - The certificate costs ≈ 197 B/leaf and ≈ 0.12–0.17 board-s/leaf. BYTES BIND: max ≈ 6,000 leaves (≈ 1.3× PC8C5BF).
  - ⇒ ROUTE 1 (re-optimised 8-point) FITS; ROUTE 2 (n = 9, 3–10×) does NOT at current density (needs a new encoding). The +2.8e-7 tightening fits only if leaves grow ≤ 30%.
  - DECISION: route 1, pending window-scope's concrete κ_8.
- **window-scope REAL frame optima (cutting-plane LP on the true minimum; validated):**
  - n = 8 re-optimised: κ 0.67354828 (+4.8e-7 only; PC8C5BF is already optimal) ⇒ ROUTE 1 IS DEAD (a certification margin of 2e-4 costs ≈ 1.2e-6).
  - n = 9: κ 0.67358140 (+3.36e-5; gaps ≥ 17/20 irrelevant). n = 10: +5.91e-5.
  - n = 9 binding structure ≈ PC8C5BF's (16 near basins); leaf estimate 3–6× (14k–28k leaves). Weights in bench/arun/est/lp9_lo0.json.
  - Options: (a) a tightened 8-point floor, +≈2–4e-7 (nominal retake); (b) n = 9 with a ~3–5× denser certificate encoding (engineering R&D); (c) stand down. → Sam.
- **SAM DECISION: 9-POINT CERTIFICATE + DENSE ENCODING** (target κ ≈ 0.673580, on the stripped MOP chain, full credit).
  - am-cert: split PC8C5BF's cost into fixed vs per-leaf (the memory says the walk is ≈ 140 bits/leaf; the 197 B/leaf figure likely overstates), then re-project for 9-point.
  - bridge-port: pipeline revalidation → 9-point fast sizing (lp9 weights, margin 2e-4) → the n-generalised Lean layer.
  - window-scope: rounded lp9 weights + basin list + c_cert target.
- **Prep complete:**
  - window-scope cert9_final.json (B 437542/10⁸, c_true 0.0085934887; κ_true 0.673581404; certified 0.6735811 at δ 5e-5).
  - am-cert MOPX_skel.lean (1,718,796 B, all notices verbatim + our header and §4(b) change notice; the control builds clean, predicted 2,229 s) + swap_cert.py (self-test passes).
  - bridge-port pipeline reproduces PC8C5BF EXACTLY (Inst byte-identical; 12.9 min/generation; δ knee ≈ 3e-5 ⇒ use 5e-5).
  - NEXT: n = 9 pipeline generalisation + sizing (bridge-port); Lean n-generalisation of Arun's layer (am-cert); sizer-format weights (window-scope).
- bridge-port n = 9 SIZING RUNNING (11:38; Q = 8 path from mvt-engine's port; weights cert/n9/rwin9_lp9.json; δ = 2e-4/5e-4/1e-3 + a fast subset). Independent F-check at the argmin agrees.
  - Prediction ≈ 13k leaves at 2e-4 (11k–17k). The bytes check follows (walk ≈ 246 bits/leaf at n = 8 ⇒ ≈ 800 KB hex at 13k; tight vs ≈ 1.19 MB available).
- **am-cert PC8C5BF split (measured per declaration):**
  - The WALK is the only per-leaf part: 283.7 KB (247 bits/leaf) + 83.2 kernel-s (18.1 ms/leaf ≈ 0.10–0.13 board-s/leaf). Fixed in-region ≈ 635 KB + 24 s; the evaluator + engine outside the region 295 KB + 28 s.
  - n = 9 projection (placeholders): at 14k leaves, bytes 1.41 MB vs 1.20 available (×1.18 over), walk TIME 1,750–3,360 board-s vs ≈ 760–1,020 (×1.7–3.1 over).
  - ⇒ TIME BINDS FIRST. n = 9 needs the per-leaf kernel cost ≈ 2–4× cheaper (than today's 8-point leaf even), plus ≈ 1.5× denser walk bytes. Levers on record: DFAST fast paths, BSPLIT, mleafS-style proved fast leaf evaluators (≈ 1.9× in-walk, 10-03), avoiding Huffman decode cost. Awaiting the actual leaf count.
- window-scope wrote cert/rwin9_lp9.json (true min 0.00859348873961842, oracle on 3 seeds + 2 fresh searches; mirror symmetry asserted). The lead compared it with bridge-port's cert/n9/rwin9_lp9.json: aN/bN identical; bridge-port's eps_strong is 2.2e-13 HIGHER. Flagged to bridge-port (immaterial at the 2e-4 margin unless the sizer stalls).
- **am-cert: n-GENERIC chain (OpethN) compiles, std axioms** (arun/Gen9Test.lean): card_near_le_k, band_close_n, pressure/remainder/matching_n, defect_to_dyadic (c, B parametric), actual_dyadic for any admissible WCert n with c ∈ (0, 1/64].
  - The n = 8 instantiation reproduces 66812491/99194876 exactly; the n = 9 abstract instantiation typechecks.
  - Full MOPX9_skel.lean build (1,719,833 B, notices verified) running. Profiling of the 18.1 ms/leaf is next.
- **bridge-port n = 9 interim sizing:** fast subset (roots 2/5/9) gives 5,101 leaves at δ = 2e-4, ≈ 305 bits/leaf ⇒ an estimate of ≈ 17,100 leaves (≈ 3.7× PC8C5BF; the top of the predicted range). Margin barely matters (1e-3 saves 4%), so stay at 2e-4. Full counts in ~35 min.
  - Lead projection: walk ≈ 650 KB, total ≈ 1.45–1.5 MB vs 1.20 available (≈ 1.25× over). Walk time at 24–33 ms/leaf ≈ 2,200–4,100 board-s vs ≈ 760–1,020 (2.2–5.4× over) ⇒ a per-leaf kernel ≈ 6–8 ms is needed (≈ 2.5–3× cheaper than today's 8-point leaf). Decision hinges on am-cert's profile.
- **am-cert MOPX9_skel.lean DONE** (1,719,833 B, 20 notice blocks verified; n-generic OpethN chain).
  - Control with the current 8-point certificate: BUILD/REPLAY exit 0, std axioms, κ = 66812491/99194876 exactly, predicted 2,234 s.
  - n = 9 typechecks abstractly. swap_cert9.py regenerates the final block for any n (self-test byte-identical at n = 8).
  - Remaining gate: per-leaf kernel cost (profile) + the full n = 9 leaf count.
- **am-cert PER-LEAF PROFILE (measured, ±6%):** 19.2 ms/leaf = side conditions 9.9 (tangent checks, tcheckPZC) + main inequality 3.9 + decode 3.85 (forceR/CPS re-instantiation) + navigation 1.5 + shared 0.8.
  - Levers:
    1. PRECERTIFIED POINT VALIDITY INTERVALS (TVal monotone ⇒ per-point [a, b] checked once; the per-leaf side condition becomes 2 comparisons): −9.5 ms (−50%), unbuilt;
    2. mleafS nested decode: −2 to −3 ms;
    3. kind-specialised terms: −1 to −1.5 ms;
    4. keep the fixed-width walk (Huffman adds time).
  - n = 9 projection with 1 + 2 + 3: ≈ 7.4–10 ms/leaf (central 8.5; P(≤ 10) ≈ 0.7, P(≤ 8) ≈ 0.35–0.4) ⇒ at 17.1k leaves ≈ 770–1,060 board-s, borderline vs 760–1,020.
  - BYTES also over (≈ 1.5 MB vs 1.20). Next: an offline lever-1 interval-merge check (pre-registered) + a byte-lever list.
- **LEVER 1 CLEAN (am-cert offline check):** 100% of points need ONE validity interval at n = 8 (2,166 points, +23 KB) and n = 9 (PC9L, 3,657 points, +39 KB).
- **PC9L (bridge-port, n = 9, δ 2e-4): 17,572 leaves, 3,657 points, replay verified.** Inst 141 KB, Data 1,733 KB (walk 1,258 KB fixed-width, 299 bits/leaf).
  - JOINT BUDGET: time ≈ 8.6 ms/leaf with levers 1–3 ⇒ 800–1,100 board-s vs 760–1,020 (borderline). Bytes ≈ 1.87 MB vs 1.20–1.30 (OVER 0.6–0.7 MB). Identified byte levers reach ≈ 1.33 MB, but Huffman and same-flag cost time.
  - Binding item = walk encoding (bits/leaf vs decode ms). Next: measure the in-kernel Huffman decode cost + a walk-content breakdown (structural saving: derive point indices from the precertified intervals).
- bridge-port FULL n = 9 sizing confirmed (17,572 leaves at 2e-4; 3.82× PC8C5BF; margin barely matters). Q = 8 generators emit9pz/make9pcC (regression byte-identical at Q = 7); PC9LInst compiles (51 s); PC9LData compiling.
  - Split: bridge-port = walk-content breakdown + structural point-index derivability; am-cert = in-kernel Huffman/same-flag decode bench.
  - Hex Nat is the densest kernel-cheap literal (base64 = String, quadratic) ⇒ walk bits/leaf must fall ≈ 2× at near-zero decode cost.
- am-cert PRE-REGISTERED both items:
  - (2) walk breakdown: point indices ≈ 35–40%, kinds ≈ 23%, λ ≈ 15–20%; derivable points ⇒ ≈ −70 to −80 bits/leaf; with Huffman on kinds/λ ≈ 150–180 bits/leaf (short of 140; ~60%).
  - (1) Huffman surcharge +0.6–1.2 ms/leaf (NOT viable, ~75%); same-flag +0.1–0.3.
  - bridge-port redirected to the PC9LData compile/axioms + a cross-check of the field layout.
- **am-cert MEASURED:**
  - walk = j-indices 49% / kinds 23% / λ 18% / multipliers 7% / splits 3%. DERIVABLE POINTS REFUTED (median 149 covering candidates).
  - Huffman in-kernel +5.2 ms/leaf bit-serial, +1.6 (8-bit LUT), +0.8 (10-bit LUT, +205 KB tables). Same-flag cheap (−24 bits).
  - VERDICT: n = 9 AS BUILT does NOT close bytes + time (hex walk ⇒ ≈ 8–12k leaves max at 286 bits/leaf).
  - LAST EXPERIMENT (pre-registered): trade κ for leaves (window-scope fatter-basin LPs at κ 0.673570/0.673562/0.673555; bridge-port fast sizing); buildable if est. ≤ 11k leaves at gain ≥ +1.5e-5. am-cert: lever-1 Lean design (no build) + the n = 8 fallback check (re-optimised, δ 3e-5 ⇒ κ 0.6735481, +3.0e-7).
- am-cert decode table completed: fixed + same-as-previous flag = 2.26 ms/leaf (+0.48, −13% payload). Confirms n = 9 as built does not close. Route 1 (re-optimised n = 8) fits but is worth only +1.9–3.0e-7 (window-scope's real optimum).
- **am-cert lever-1 Lean design (design only):**
  - TVal_mono (TVal antitone in range); intervals packed in the same point word (v + 2^96·(a + 2^20·b)); IVSound; one-time ptlOkI per point block; mokI leaf check replacing mokTZC.
  - Cost −9.5 ms/leaf; +30 KB (n = 8) / +45 KB (n = 9); one-time +6–14 board-s. Effort ≈ 10–16 h (the risk is selector plumbing).
- **Fallback n = 8:**
  - PC8C5BF weights at δ 3e-5 give +1.09e-7 only. The re-optimised weights (+3.0e-7 at 3e-5) need their own sizing.
  - Estimated ≈ 6.8k–8.7k leaves at 3e-5; fits bytes (≈ 1.09–1.23 MB) and tight time as is, comfortable with lever 1.
- am-cert fallback costing (re-optimised n = 8, δ 3e-5, κ 0.6735481, +3.0e-7):
  - At ≈ 6k leaves, region ≈ 1.03 MB (fits, ≈ 170 KB spare); ≈ 2,370–2,420 s predicted (fits 2,600).
  - Fits as built up to ≈ 7.4k leaves; beyond that it needs lever 1 / the precise strip. Needs a fast-size of the new n = 8 weights at δ 3e-5.
- bridge-port: PC9LData Lean build — all 16 root walks KERNEL-ACCEPTED (470 s, 12.9 GB peak RSS vs PC8C5BF 117.6 s / 2.75 GB); a root-cover KB overflow at n = 9 was fixed in size9pz.py (n = 8 regression byte-identical); re-sizing.
  - MEMORY flagged as a third budget (board sandbox 8 GB; a past acceptance at a 12.7 GB local footprint suggests local overstatement). Priority = fast-size the κ-for-leaves variants.
- **window-scope κ-for-leaves certificates (separation LP, kept palindromic basin pinned):**
  - t570: κ 0.673570002 (+2.22e-5), 2nd basin +1.91e-3, basins at 2e-4/1e-3/1e-2 = 1/1/93;
  - t562: 0.673562092 (+1.43e-5), 1/1/70;
  - t555: 0.673555097 (+0.73e-5), 1/1/67;
  - (cert9: 16/24/108).
  - Giving up 1.1e-5 of κ collapses 16 near-binding basins to 1. A first unpinned formulation was caught and discarded.
  - Fast sizing dispatched (bridge-port, parallel to the re-size). Rule: buildable if est. ≤ 11k leaves at gain ≥ +1.5e-5 (t570 is the candidate).
- **bridge-port: PC9L 9-point certificate COMPILED** (AMW.Cert.PC9L_cert_full, cN 859177/10⁸, std axioms; 17,551 leaves after the KB fix; walk 5.02 Mbit; Data 497 s / 11.6 GB peak, Inst 65 s / 6.9 GB).
  - Raw ≈ 2.67 MB with the skeleton (over the cap). Hand-off to am-cert for the integration test; the variant fast-sizing (t570/t562/t555) is the decision input — pushed.
- bridge-port:
  - Hand-off of PC9L to am-cert done (sha256s; AMW.PCBias flag).
  - eps_strong difference immaterial (cN identical).
  - VARIANT FAST SIZINGS running since 14:11 (pre-registered: subset 2.3–3.0k, est. 8–10k, t570 buildable). A wrong-window first launch was caught within a minute and relaunched.
  - Memory: PC9LData is already chunked per root; the 11.6 GB was an async build. A per-declaration RSS probe with Elab.async false is queued.
- **Variant fast sizings: NOT BUILDABLE by the pre-registered rule.**
  - t570 ≈ 13,640 est. (subset 3,966 × 3.44); t562 ≈ 13,830; t555 ≈ 13,790; all equal within 1.5%.
  - Collapsing 16 basins → 1 cut leaves only ≈ 22%; lowering κ further cut nothing. Leaves are spent in the BULK of the 8-dimensional box, not the basins. bridge-port's prediction (8–10k) refuted.
  - Calibration caveat: a full t570 sizing is running (≈ 57 min); it passes if the ratio is ≤ 2.77.
  - Lead projection at 13.6k: walk ≈ 1.04 MB hex ⇒ region ≈ 1.66 MB (≈ 1.35–1.47 MB with same-flag/PTFLAT/Huffman-LUT) vs 1.20–1.30; time ≈ borderline with lever 1 + LUT ⇒ high-risk on all three budgets.
- **bridge-port memory probe (PC9LData, Elab.async false):** RSS ACCUMULATES across the 16 root walks: import 5.9 GB → peak 11.24 GB (+5.3 GB); per-root chunking does not bound the peak.
  - Board sandbox 8 GB, and MOP + PC8C5BF is already at 6.98 GB max RSS ⇒ a 9-point certificate is a real OOM risk (unless local RSS overstates).
  - PC8C5BFData control probe queued. Full t570 sizing: roots 0–6 track the fast subset exactly; total in ~30 min.
- **FULL t570 sizing: 14,906 leaves** (calibration ratio 3.76, not 3.44; t562/t555 ≈ 15.1k) ⇒ **NOT BUILDABLE by the pre-registered rule.** The 9-point route fails at this certificate design (bulk-minorant-bound leaves; plus bytes/memory).
  - bridge-port's named refuting test (heavier pressures b_r at similar κ, fast subset) not run.
  - Decision → Sam: nominal 8-point retake (+3.0e-7) / one more cheap 9-point test / stand down.
- **SAM DECISION: CHEAP TEST, THEN DECIDE.**
  - (1) Heavier-pressure n = 9 variant (window-scope LP, κ ≥ 0.673570, maximise b_r) → bridge-port fast-size (×3.76); reopens 9-point iff est. ≤ 11k.
  - (2) In parallel, the fallback: the re-optimised n = 8 at δ 3e-5 (κ ≈ 0.6735481), full sizing → build (if ≤ 7.4k leaves); am-cert prepares the 8-point swap and private check.
- **am-cert 9-POINT INTEGRATION TEST PASSED end to end** (INT9.lean, 2,783,687 B; PC9L through the n-generic chain; BUILD/REPLAY EXIT 0, std axioms; export/nanoda/closure OK).
  - MEASURED: build 860 s, replay 521 s (kernel 485.5), nanoda 904 s (×5.61 instructions vs PC8C5BF!), closure 516 s ⇒ calibrated board ≈ 6,120 s (1.9× the hard limit).
  - Peak RSS 12.7–14.0 GB in every heavy stage (8 GB sandbox).
  - Walk ≈ 20 ms/leaf (better than the projected 25). Swap tool scope-line fix (self-test byte-identical).
  - ⇒ The n-generic chain WORKS with a real 9-point certificate. At 17.6k leaves it is over on bytes, time and memory; nanoda binds.
- **Threshold update (recorded BEFORE the heavier-pressure test result):** given the measured nanoda scaling and memory, a 9-point reopen now needs ≲ 8k estimated leaves (+ lever 1), not 11k.
- **am-cert 8-point RETAKE PATH READY:** arun/retake8.sh (assemble → swap with exact κ assert → engine_check → size gate → private check → stages → prediction). Dry run clean (1,726,114 B, 21 Copyright occurrences).
  - Target κ = 8351261/12398908 = 0.6735481060 (+3.01e-7; lead re-verified). Expected ≈ 1.83 MB at ≈ 6k leaves. Turnaround ≈ 20–25 min once bridge-port hands over the certificate.
- bridge-port memory control: PC8C5BFData +1.80 GB (peak 7.35), PC9LData +5.63 GB (peak 11.24); ≈ 0.32–0.39 MB/leaf.
  - Board extrapolation: PC9L ≈ 10.8 GB, t570 ≈ 10.0 GB, 11k ≈ 8.7–9.5 GB vs 8 GB ⇒ a 9-point certificate needs ≲ 7–8k leaves (consistent with the ≲ 8k reopen threshold).
  - window-scope's rwin8_reopt.json and rwin9_tP570.json exist; bridge-port told to run both now.
- bridge-port (15:33/15:35):
  - Heavier-pressure test RUNNING (rwin9_tP570, cN 848997; pre-registered prediction est. 12.8–15.8k, not reopened).
  - FALLBACK RUNNING (rwin8_reopt full sizing at δ 3e-5, cN 808736, name PC8R; predicted 5.5–7.0k leaves).
  - Side note: rwin9_tPs570 is not certifiable as is (b₀ < cN/32 ⇒ S₀ > KB = 2²⁰); design constraint every b_r ≥ cN/32.
- window-scope round 8: tP570 (max min b_r) shrinks the root boxes: S_max 31.6 → 23.5 (−26%), Π S −24%, B −1.1%. But 15 basins now sit at 1e-3 (t570: 1). rwin8_reopt eps_strong = 0.008087608236768. Both are being sized by bridge-port.
- **am-cert de-risk build PASSED:** retake8.sh SELFTEST output (R8_PC8C5BFDRY.lean, 1,726,129 B) BUILD EXIT 0, std axioms on all 3, REPLAY EXIT 0 (max RSS 6.73 GB). The retake path is end-to-end verified; one command on hand-off.
- **Heavier-pressure test RESULT: tP570 subset 3,914 (−1.3% vs t570) ⇒ est. ≈ 14.7k ≫ 8k ⇒ 9-POINT ROUTE CLOSED for this design** (bridge-port's prediction held).
  - Leaves at n = 9 are set by bulk-minorant reach; only an engine change (more reach per leaf) would move them.
  - → 8-point nominal retake (PC8R) proceeds; full sizing at 23/32 roots.
- **Fallback PC8R at δ 3e-5: 18,731 leaves** (knee; root 18 = 11,962) ⇒ stopped per rule.
  - δ = 5e-5 (cN 808720): κ = 8351261/12398910 = 0.67354800 (+1.92e-7, exact). GO: ROOTSEL=18 pre-check (pass ≤ ~500) → full sizing → build → retake8.sh.
- PC8R root-18 pre-check at δ 5e-5: 225 leaves — PASS (prediction held). A process slip (the first launch ran at 3e-5 due to a hard-coded δ) cost ~6 min; fixed. FULL sizing at 5e-5 running (predicted 4.6–5.6k leaves).
- **PC8R at δ 5e-5: 4,575 leaves** (≤ 7.4k ✓; 2,260 points), emit replay 0 failures. PC8RData 715,318 B, PC8RInst 201,834 B (same size class as PC8C5BF). Lean build + axioms running → hand-off to am-cert (spec 8351261/12398910).
- **PC8R COMPILED** (AMW.Cert.PC8R_cert_full: 808720/10⁸ ≤ G, std axioms; Inst 63 s, Data 142 s; 4,575 leaves). Handed to am-cert (cert/n8r/handoff/, sha256s) for retake8.sh, spec 8351261/12398910. All of bridge-port's predictions held. Standalone async Data build RSS 10.1 GB (not like-for-like; the retake run measures the real file).
- **am-cert 8-POINT RETAKE VERIFIED** (retake8.sh): arun/R8_PC8R.lean, 1,724,342 B, sha 2981f336…; κ = 8351261/12398910 (+1.923e-7 exact).
  - BUILD/REPLAY EXIT 0, std axioms on all 3; stages OK (max RSS ≤ 6.7 GB except local replay harness 8.48 mmap-inclusive; footprints ≤ 5.0 GB). Predicted board ≈ 2,220 s.
  - Lead independently checked sha/size/notices/escape hatches/κ literals; board unchanged at 18:xx local.
  - Freeze requested: header line-26 tidy → bench/arun/UPLOAD_PC8R.lean + a re-check.
- **FROZEN: bench/arun/UPLOAD_PC8R.lean** — sha256 84dc010d6167f74a512cb9fe1c07503a4629b1d6c431b874481a2ebbe27be473, 1,724,381 B.
  - κ = 8351261/12398910 = 0.67354800 (+1.92e-7 over Arun's 66812491/99194876).
  - Header-only line-26 tidy (lead diff: only line 26 differs from the verified R8_PC8R).
  - Re-check: BUILD EXIT 0, std axioms on all 3, REPLAY EXIT 0. Predicted board ≈ 2,220 s. chmod 444.
  - Board checked: Arun #1, nothing pending. UPLOAD IS SAM'S.

## 2026-10-10 late — SAM: "do the 9 pt, focus on getting that to fit"
- Baseline (INT9, PC9L 17.6k leaves): bytes 2.78 MB / 2.0; time ≈ 6.1 ks / 3.24 hard; memory 12.7–14 GB / 8. Weight levers exhausted (≤ 15%).
- Target region: ≲ 8–9k leaves AND ≈ 2× cheaper per leaf (time + memory).
- PHASE 1 (diagnosis, pre-registered, no builds):
  - bridge-port = leaf anatomy (why parents split; second-order minorants, far-field test, split axis, lever-1-enabled reach);
  - am-cert = lever-1 effect on nanoda/memory (PFBench NP vs NO through the stages), memory anatomy, budget model + feasible region;
  - window-scope = excess-volume distribution, curvature/third derivative, smoother-window estimate.
- am-cert Phase-1 PRE-REGISTRATION:
  - (1) Lever 1 on nanoda: −40 to −55% instructions, RSS −20 to −40% (rule: ≥ 40% ⇒ a nanoda lever too; < 25% ⇒ nanoda's cost is elsewhere).
  - (2) Memory: accumulation, not per-declaration (32/16/1-walk bench; RSS(16) ≈ 0.6–0.7×), ~60%.
  - (3) Budget model: at f = 1, L ≤ 4–5k (memory binds); at f = 0.5, L ≤ 8–10k.
- **am-cert PHASE 1 MEASURED:**
  - (1) Lever 1 cuts nanoda −42.5% instructions / −52% peak RSS, closure −43% / −34%, build −41% ⇒ a nanoda lever too.
  - (2) Memory: build/replay ACCUMULATES (≈ 0.39 MB/leaf n = 8, 0.89 n = 9); nanoda/closure peaks are PER-THEOREM (set by the largest walk) ⇒ CHUNKING walks (≲ 1.2k leaves each) is their lever (BSPLIT data currently forbids CH > 0 — an engineering item). Partial refutation of the "all accumulation" prediction.
  - (3) Calibrated budget model (reproduces INT9 6,108 vs 6,120, PC8R 2,217 vs 2,220): board ≈ 1,659 + 0.253·L·f s; build memory ≈ 2.6 GB + 0.89 MB·L·f_m; bytes ≈ 1.185 MB + points + 71.5 B·L.
  - FEASIBLE (10% margins): n = 9 needs L ≲ 6–7.5k leaves + lever 1 + chunked walks + the precise strip. Bytes bind first, build memory second.
- **PHASE 2a STARTED (am-cert): BUILD LEVER 1** (precertified validity intervals) — needed in every feasible scenario.
  - n = 8 control (PC8C5BFI) first; pre-registered pass: the same leaves/end positions, std axioms, walk kernel ≥ −45%, nanoda ≥ −35%. Then PC9LI.
- **window-scope Phase-1 geometry (t570, 14,906 leaves; per-leaf true minima by SLSQP):**
  - 84.7% of leaves have min excess ε > 0.1 (median 0.47); far leaves are wide (median ~4 gap units); 55% contain a long gap > 2.5.
  - A PERFECT FAR-FIELD TEST collapsing subtrees with ε > θ leaves 7,896 (θ = 0.1), 3,719 (θ = 3e-2), 1,598 (θ = 1e-2) leaves.
  - Second-order minorants: ×2.1–4.6 box enlargement (proxy ≈ 4.8k, optimistic).
  - The window lever is DEAD (smoothing costs 4e-5–1.4e-4 of ceiling).
  - Engine ideas: long-gap decoupling; a joint linear-pay cut. Prediction (25% far) refuted: 85%.
- **Phase 2b far tests (window-scope, round 10, t570 tree):** T1 interval-min −8.9% (resolution-independent; interval min of w ≈ 0 on wide pair-sum ranges); T2 long-gap with GLOBAL sub-frame minima −16.4%; T1+T2 −17.6% (12,283) against the perfect test's −47% (7,896). Combined prediction (30–45%) refuted.
- **κ trade buys no leaves:** the roots 2/5/9 subset gives t570 3,966, t562 4,020, t555 4,008 leaves. The count is set by the engine, not the margin.
- **bridge-port counterfactuals (subset, against LPACCEPT B0 = 3,143):** V −5.7%, VC −6.6%, SO −3.8%, SOVC −10.7% (NSO never passes: the curvature bound is too negative). Multiplier rounding alone: normal 3,966 → B0 3,143 (−21%). SEP still running.
- **Next (window-scope, round 11):** ceiling and net cost of box-restricted decoupling (recursive sub-certificates on ≤ 5 points). Does N_L·N_R become ≈ N_L + N_R?
- **bridge-port ANATOMY landed (cert/n9/ANATOMY.md).**
  - Leaves are in the BULK: median F/c − 1 ≈ 2.5 at the centre; 0.4% within 0.5 of a near-binding word. The leaf test keeps ≈ 11% of the true slack.
  - Parent split reasons: engine-specific 61% (t570) / 66% (PC9L); convex-envelope gap 38% / 33% (96–98% of term ranges have mixed curvature); second-order fixable ≈ 1–2%.
  - Ranked levers (subset, against the normal 3,966):
    - rank-1 quantisation (λ 10 bits, quantum 2⁻¹⁶): −17.4%;
    - V −5.7%, SO −3.8%, SEP −3.4%, C −2.0%;
    - ALL −32% (≈ 10.1k t570). The ALL run used LPACCEPT, so it is optimistic; realistic is probably ≈ −29%, ≈ 10.5k;
    - NSO 0; PF16 worse.
  - Verdict: no measured combination reaches 6–7.5k.
- **Decision (lead):**
  - BUILD rank-1 quantisation (bridge-port; first confirm whether it is generator-side only) and lever 1 (am-cert, in progress; = V). C/SO/SEP are deferred.
  - MEASURE an honest stacked baseline: full t570 tree on the q+V engine (dump_full_t570_qv.pkl). Far tests and box-restricted decoupling run on it (window-scope, round 11).
  - SIZE the lobe-case leaf test (bridge-port), costed in both bits and kernel time.
- **Lever 1 control (am-cert, PC8C5BFI):** sound, standard axioms, the same 32 walks.
  - Walk kernel −45.1% / −44.5%: BORDERLINE PASS against the ≥ −45% bar.
  - nanoda walk-only −32.5%: FAIL against the ≥ −35% bar. Full closure: nanoda −16.6%, export −9.5%, Lean replay −14.9% instructions / −31% time.
  - Lever 1 captures ~77% of the side-condition ceiling in nanoda. Walks are ~58% of the closure's nanoda, so the base is about half the budget.
  - PC9LI: built; Data replay −31.3% instructions.
- **Decision:** lever 1 stays. am-cert next:
  - (a) split the remaining 56.6e9 instructions; then (b) only where (a) points;
  - re-cost the budget model with the measured per-stage factors and give the leaf target L*;
  - break down the ≈ 1,659 board-s base by component (every −100 s ≈ +600 leaves).
- bridge-port: rank-1 quantisation is generator-side only (confirmed at source). Full t570 sizing on the q+V engine (11.0–12.2k predicted) and lobe-case subset tests are running.
- **bridge-port round 2:**
  - QV subset (rank-1 quantisation + exact validity, real engine): 3,068 leaves (−22.6%). Multipliers need QB = 13.
  - LOBE = 3 leaf test: leaves −13.3%, but walk bits +64% and kernel checks +62% (≈ 4,140 board-s against ≈ 3,190 at full scale). NOT a net lever; prediction held.
  - Full QV tree: 7 of 16 roots done, each ~30% below normal ⇒ ≈ 10.4k leaves (time ≈ 3,190 s: over the soft rule, near the hard cap).
- **Full t570 on the build engine (QV) DONE:** 10,452 leaves (−29.9%), 313.7 bits/leaf, 1.304 MB raw (+≈ 40 KB of intervals), ≈ 3,190 board-s. Over on bytes (≈ 1.1×), time (soft rule) and memory. Dump: cert/n9/dump_full_t570_qv.pkl.
  - Caveat: 40 tangent points sit at ≥ 16 units, beyond the point table's < 2¹⁹. bridge-port is measuring the cost of a cap; am-cert holds the range change.
- **window-scope round 11 interim (4 roots):** the ideal box-restricted decoupling gives −71%, carried by END gaps (r = 0/7, an 8-point sub-frame); splits with both sides ≤ 5 points give only −14%.
- **Dispatched:** bridge-port measures end-gap recursion in the real sizer (split at g*, one 8-point sub-certificate with floor cN − b_0 g*, g* ∈ {1.5, 2, 2.5, 3}).
- **Lever 1 at n = 9 (am-cert, PC9LI walk-only closure):** nanoda −10.6% (n = 8: −32.5%); Lean replay −23.1%; export −0.9%.
  - nanoda per bit at n = 9 is 3.5× n = 8's, while Lean per-declaration replay is flat. So the extra n = 9 cost is specific to nanoda, and lever 1 does not touch it.
  - The Phase-1 per-leaf scaling is REFUTED for nanoda.
  - Running: the L/S test (largest vs smallest walks, pre-registered: ≥ 1.5 ⇒ superlinear ⇒ chunking is the lever).
  - Lead's flag: nanoda alone ≈ 0.33 board-s/leaf exceeds the model's 0.253 total, so the calibration must be reconciled against INT9 before L*.
- **Chunk test SUPPORTS (am-cert):** nanoda per bit L/S = 3.91 (≥ 1.5 pre-registered; predicted 2–3).
  - S: 506k instructions/bit, 4.31 GB. L: 1.98M/bit, 11.75 GB. Cost per walk is ≈ quadratic in walk size and nanoda-specific.
  - Extrapolation, not measured: chunking to ≈ 100k bits gives ≈ −60% nanoda (≈ 2.3e12 against 5.9e12).
- **GO Phase 2b chunking (am-cert):**
  - first, reconcile the model and give L* (unchunked / chunked);
  - then build BSPLIT chunk boundaries. Pass: standard axioms, identical leaves, nanoda ≤ 0.65M/bit, peak ≤ 6 GB.
  - then the base breakdown.
- **bridge-port round 3:**
  - Tangent cap < 16: +1.7% leaves (> 1% bar) ⇒ EXTEND the point table (am-cert).
  - One-split end-gap recursion in the real sizer: NET WORSE by +12–16%.
    - The g* ≤ 2.5 sub-frame inequality is false with the global minimum F_L = 0.0077795.
    - Only 4.7% of leaves lie at g_7 ≥ 3; the long gaps are MIDDLE gaps (57.5% of leaves have a middle gap ≥ 2).
    - Retired as a lever. My earlier framing ("end-gap 8-point sub-certificate would be the fit") is REFUTED in its one-split form.
  - The ideal −71% must come from box-restricted minima deep in the tree; round 11's net-cost estimate decides.
- **Chunk test (PC9LC, am-cert):**
  - Memory PASS: nanoda peak 12.68 → 3.61 GB; closure 12.94 → 2.19 GB.
  - Instructions FAIL: nanoda 6,001e9 against 5,925e9.
  - The "quadratic in walk size" claim is RETRACTED by am-cert. The 3.91× per-bit gap is walk CONTENT, not size. Chunking is a MEMORY lever.
- **Model reconciled.** 0.86 board-s/1e9 is an all-stages multiplier on Lean-kernel instructions. The per-stage weights are 0.289 (build) and 0.356 (export/nanoda/closure) board-s per 1e9.
- **L* with lever 1 as built** (f = 0.82–0.85; nanoda is 56% of the per-leaf cost):
  - time: 4.2–4.5k at the 2,600 s soft rule, 7.1–7.6k at the 3,240 s hard limit; 10,452 leaves ≈ 3,850 board-s;
  - memory: chunked 6,980–8,200;
  - bytes: 4,320–6,560 as built; 5,620–7,900 with the precise strip.
  - The QV tree does NOT fit. Needed: ×1.4 (hard) to ×2.3 (soft) fewer leaves, or a cheaper per-leaf nanoda cost, or a smaller base.
- **Next (am-cert):**
  - (a) find nanoda's expensive per-leaf content. Hypothesis given: a Nat operation outside nanoda's accelerated set on the n = 9 hot path;
  - (c) base breakdown, interleaved;
  - (b) cheaper boundaries: deferred.
- **am-cert (a), interim:**
  - Lead's hypothesis (an unaccelerated Nat operation on the n = 9 hot path): NEGATIVE. nanoda accelerates every Lean GMP operation except log2, and log2 is in neither closure.
  - Per-walk regression: nanoda per leaf tracks the total REMAINING walk literal bits seen by each leaf (R² 0.991; leaves 0.932; multipliers 0.903). am-cert's pre-registered guess (multipliers/splits) was refuted.
  - Test 1, WIN = 512: nanoda −12.5% only. Refuted by am-cert's own rule; memory −38%.
  - Test 2 running: own literal per ≤ 100k chunk + WIN (literal sum ×0.155). Predicted 1.0–1.6e12; supports at ≤ 2.5e12, refutes at ≥ 4.5e12.
  - Base (desk): kernel replay 143.5 s, of which walks 82.9 s. Fixed kernel: tables and points 20.7 s, CellA 18.2 s, PyrD 8.0 s. The board base is dominated by build elaboration (≈ 673 board-s) and the library closure. Profiled rebuild and marginal exports are queued.
- **Tangent range: CAP, not extend (reversed after a source read by am-cert).**
  - tcheckZC needs the point inside the 16 convex regions. REG covers [0.5, 16) units, and p ≥ 507,904 (≈ 15.5 units) fails. The same limit applies to mokTZC and ivOk.
  - So the 40 far points were never Lean-certifiable. PTMAX = 2²¹ was a bytes-only generation.
  - Cap at p < 507,904: ≈ +1.7% leaves (≈ 180 leaves, ≈ 36 board-s, ≈ 14 KB).
- **PC9LL (chunk-local literals + WIN 512, am-cert): SUPPORTS literal-size.**
  - Walk-only closure: nanoda 5,925e9 → 1,803e9 (−70%), export −72%, Lean replay −8%.
  - Peaks: nanoda 3.21 GB, closure 1.32 GB.
  - Same leaves, standard axioms; generator-only changes (CHB, CHL, q-explicit boundary lemmas).
- **Re-costed per leaf ≈ 0.128 board-s** (from 0.209–0.222):
  - time: L* ≈ 7,350 at the soft rule, ≈ 12,350 at the hard limit; 10,452 leaves ≈ 3,000 board-s;
  - MEMORY binds now: build 0.77 MB/leaf, so L* ≈ 6,000–7,000;
  - bytes: boundaries +390 KB as built, and need compacting.
- **Next (am-cert):** (c) base measurements (running, plus per-declaration memory high-water) → build-memory anatomy (pre-registered) → compact boundaries and chunk-size tuning.

### 2026-10-11 — campaign PAUSED (window-scope and am-cert hit the weekly limit; resets Oct 14 8pm PT). State and resume plan.
- **Round 11 (window-scope), PARTIAL; files in bench/arun/est/r11/:**
  - (1) Ideal T2* on t570: all-r top-level 14,906 → 5,203 (−65%); r ∈ 2..5 → 11,660; r ∈ {3,4} → 12,422.
  - (2) Net with the second-order side proxy:
    - per-node best 14,285 (all r, −4%), 14,868 (r 2..5), 14,906 (r 3,4: none);
    - side-proxy sums 31.8k–129k, far above the leaves removed.
    - The proxy is poorly calibrated (calib.log: 1 vs 507 on some nodes, 1,634 vs 439 on others), so this is NOT a verdict.
  - Comparator (hull_collapse.py): the full 9-point hull-LP (valid convex minorant per pair) collapses the t570 tree 14,906 → 10,778 (−27.7%). The QV engine (10,452) is already at that level.
  - Lead's reading (not a verdict): the side sub-certificates face the same convex-envelope cap, so decoupling gains only through shared splits. The part-(2) hull-proxy driver was in progress at the pause.
- **am-cert (c) base measurements:** started at the pause (profiled CandR8PC8R rebuild + nested exports). Status unknown; check for outputs before re-running.
- **Fit arithmetic at ≈ 10.6k leaves (QV + lever 1 + chunk-local literals):**
  - time ≈ 1,659 + 0.128·10.6k ≈ 3,020 board-s (under the 3,240 hard limit, over the 2,600 safe rule);
  - build memory ≈ 2.6 + 0.77·10.6 ≈ 10.8 GB > 8 GB (binding);
  - bytes ≈ 2.3 MB + boundaries > 2 MB.
- **RESUME PLAN (in order):**
  1. am-cert: finish (c) and record per-declaration memory high-water → BUILD-MEMORY anatomy (pre-registered: caches vs fragmentation vs literal terms vs boundary rfl vs decide intermediates) → compact boundaries + chunk-size tuning.
  2. window-scope: finish round 11 (2) on the hull proxy and give a decisive net for box-restricted recursion.
  3. bridge-port: re-size the full QV tree at TCAP 507,904; emit PC9Q with lever 1 + CHB/CHL/WIN for a real integration build.
  4. Lead: assemble the 9-point candidate (swap_cert9/int9) from that emission and measure the stages. Decide fit / no-fit on measurement.
  - Fallback unchanged: UPLOAD_PC8R.lean frozen (+1.92e-7); the upload is Sam's call.
- **10-11 RESUMED (Sam: "unpause them").**
- **Lead's build-memory finding (pre-registered: /tmp/leadmem/prereg_B.txt):**
  - Command-line Lean defaults to Elab.async = true.
  - PC9LLData built with -DElab.async=false: peak footprint 2.79 GB (against 16.17 GB), instructions −4.5%, real −10%. The footprint stays flat at 2.5–2.6 GB through the walks, with NO per-leaf accumulation.
  - SUPPORTS H_async. My prediction (10–14 GB) was refuted.
  - Run C (option set in-file) in flight.
- **Dispatched:**
  - am-cert: board-time effect of async-off at threads 4 on CandR8PC8R; L* with memory no longer binding; compact boundaries.
  - window-scope: finish round 11 (2) on the hull proxy.
  - bridge-port: re-size QVT at TCAP; emit PC9Q (QV + lever 1 + CHB/CHL/WIN + async off).
- **Run C:** in-file `set_option Elab.async false` gives peak footprint 2.79 GB, instructions 2,885e9 (−5.1%), real 352 s. EQUIVALENT to -D; the board needs no flag. Prediction held.
- **CORRECTION (bridge-port, stop-the-line):** the QV tree (10,452) is NOT realizable.
  - On replay with the TABLE-based validity check (what tcheckZC / ptlOkI certify), 5,551 of 10,452 leaves fail.
  - Lever 1 checks each point's hull once with that same table check, so it is a kernel-TIME lever and does not give exact validity. The V counterfactual (−5.7%) assumed a check that does not exist.
  - Realizable engine: Q (λ 10, quantum 2⁻¹⁶, table validity), ≈ 12.3k leaves on full t570 (subset-scaled).
  - My earlier reports of "10,452 on the engine we will build" were wrong.
  - Next (bridge-port): reason split; faithful recovery via ZEXT ∈ {8, 16, 32, 64} and finer derivative tables in the once-per-point check (costed in bytes and one-time kernel time); then the real emission.
- **bridge-port steps 1–2:**
  - All exact-valid-but-table-rejected ranges fail on EXTENSION. ZN saturates by 32, leaving a 3.6% residue from table resolution.
  - In a table-faithful tree every hull passes automatically (the sides depend only on (p, U) and (p, L)), so no per-point subdivision is needed.
  - Faithful subsets: ZEXT 16 −1.6%, ZEXT 32 −2.6%; the exact-validity ceiling at the cap is −2.9%. The whole validity lever is ≤ 3%, at the ±3–4% split-order noise floor.
  - Process slip, logged: the "finer tables" runs were coarser. Rerunning.
- **Running:** full t570 on Q + ZEXT 32 (predicted 11.6–12.4k). Then real emission (QB 13, SIGSH 16, lever 1, CHB/CHL/WIN, async off) and measured stages.
- **Lead's arithmetic at ≈ 12k leaves:**
  - time ≈ 3,195 board-s (hard limit 3,240; safe rule 2,600);
  - bytes ≈ 2.4 MB (cap 2.0).
  - To fit with a 5% time margin: per-leaf ≤ 0.118 (−8%), or the base cut; bytes −0.4 MB (walk Huffman ≈ −0.28 MB, precise strip ≈ −0.1 MB, compact boundaries).
  - The 2,600 safe rule needs per-leaf ≤ 0.078 (−39%) or a ≈ 600 s cut to the base.
- **am-cert:**
  - Async ON vs OFF at threads 4 on CandR8PC8R: real S/A = 0.98, so async-off is adopted with no time penalty (user/real < 1, so no parallelism to lose).
  - BASE BREAKDOWN (board-s), sum ≈ 1,655:
    - board constant 203;
    - R8 H-window 413;
    - certificate fixed + engine 549;
    - W8 wrap 11;
    - chain + bridge + final 479.
    - Ours to shrink, about 100–200 board-s: dead-lemma strip (tangent_valZ variants), mcheckP_ok, the window equation lemmas, pvCheck_AM.
  - L* with async off: time 7,510 (soft) / 12,620 (hard) at ≈ 0.125 board-s/leaf. BYTES BIND: L* ≈ 6,100 at 2.0 MB as built, ≈ 7,400 with the precise strip.
  - Compact boundaries (CHE): 470 B each (from 1.57 KB). PC9LE is building.
- **Lead:**
  - At the realizable ≈ 12k leaves: bytes ≈ 2.55 MB (−0.55 MB needed), time ≈ 3,160 s (2.5% margin to hard).
  - Asked am-cert for a costed bytes plan to ≤ 1.95 MB.
  - Root-15 observation: normal 1,256 → QV 176 → hull 145, against 20–30% changes on every other root. The validity lever is concentrated in root 15 (≈ 8% of the tree); bridge-port is to check it under QZ32.
- **Round 11 DECISIVE (window-scope):**
  - Box-restricted recursion nets −4 to −9% leaves and −9 to −17% bytes against hull level (10,778). B_0 × B_R sharing does not appear (dedup only 1.4–4.4%). A 25% leaf cut would need sub-certificates ≈ 2.6× cheaper than measured.
  - The hull leaf test on the sizer's splits = 10,778 ≈ QV, i.e. engine level.
  - Sub-frame leaf bytes: 0.19–0.80 of a full leaf.
  - Refutation spec logged, NOT run: the real sizer on ≈ 30 all-r candidates; refuted if Σ(1 + sides) ≤ 0.75 Σ hull. Prediction ≥ 0.9.
  - Recursion is NOT pursued (days of Lean work for ≤ 9% of leaves).
  - Lead's correction: the per-node nets were hull-proxy numbers. I misread them as second-order-proxy.
- **window-scope next (round 12):** an entropy budget of the walk (per field, conditional on parent/sibling, point | range, λ | kind), giving the ideal-encoding bound for the bytes plan.
- **10-11 BOARD MOVED:**
  - shi-exact-window-refinement 0.6735478055 (11:06Z);
  - Arun's master-of-puppets2 0.67354780559 (16:15Z). Both are window-rounding refinements with the certificate unchanged.
  - Frozen PC8R (0.6735479974) still leads by +1.918e-7.
- **Lead: rebase of PC8R onto MOP2's circle enclosure → arun/R8_PC8R2.lean** (1,725,607 B; Edit-tool changes on a copy of UPLOAD_PC8R).
  - MOP2's cos_theta0_le / sin_theta0_ge (sin from sin²+cos²=1), floor_numeric, HW_ge ≥ 672168410556873948/10¹⁸; counting identity, hHW, κ literals.
  - κ = 167025220139218487/247978200000000000 = 0.6735479979 (+1.923e-7 over MOP2).
  - Notices: Arun's MOP2 circle-enclosure block prepended verbatim; change notice bullet added (MOP2 sha a99b3172…).
  - Private check (record = MOP2) + stages queued: /tmp/leadmem/check_pc8r2.sh. NO upload (Sam's call).
- **PC8R2 PASSED and FROZEN: bench/arun/UPLOAD_PC8R2.lean** (1,725,607 B; sha256 704f3b488692e4f990ffefec34b7f9f39a632594cca2bc7e55d35c3e041dce6e; chmod 444).
  - κ = 167025220139218487/247978200000000000 = 0.6735479979 (+1.923e-7 over master-of-puppets2, today's #1).
  - Private check against record = MOP2: BUILD EXIT 0 (374 s, 4.41 GB); standard axioms on all three theorems; REPLAY EXIT 0 (6,064 constants).
  - Stages: export 0.328e12, nanoda 1.295e12 (4.59 GB), closure 1.628e12. PREDICTED board ≈ 2,219 s.
  - 92 changed lines against UPLOAD_PC8R: header notice, trig enclosure, HW_ge, counting constants, κ literals. Upload is Sam's call.
- **am-cert PC9LB (limb-table walks, LB 16k, WIN 512):** nanoda 1,612e9 (−10.6% vs PC9LL), build −21.5%, −322 KB vs PC9LL, no boundaries.
  - Per-leaf ≈ 0.110 board-s ⇒ time L* 8,590 (soft) / 14,440 (hard).
  - BYTES bind: L* ≈ 6,200 (≈ 7,500 with the strip). Peaks (nanoda 10.3 GB, unchunked) pending a time series.
  - Next: the bytes plan in order (strip, point words, generic splits, limb overhead, walk encoding).
- **PC9Q BUILT (bridge-port):** t570, Q + ZEXT 32 (faithful), lever 1.
  - 11,078 leaves, 3,190 points, 310.1 bits/leaf.
  - Every walk and all 3,190 hulls verified independently (IV_PC9Q.json).
  - PC9Q_cert_full: standard axioms. Data 262 s, 2.65 GB (async off).
  - Bytes: Data 1.676 MB + Inst 0.146 MB, raw with boundary literals (233 KB) and chunk theorems (89 KB).
  - Root 15 = 166 in QZ32, so its gain was quantisation, already included. Closed.
- **Lead's estimate with limb walks:**
  - time ≈ 1,659 + 0.110 × 11,078 ≈ 2,880 board-s (hard 3,240, soft 2,600);
  - bytes ≈ 0.917 skeleton + ≈ 1.53 cert ≈ 2.45 MB, so −0.5 MB needed.
  - Next: bridge-port re-emits with LIMB (PC9QB) and runs the end-to-end INT9Q (record = MOP2) for a measured baseline.
- **am-cert: limb-walk build memory is a PER-THEOREM high-water**, not accumulation: about 1.3 GB + 3.3 MB × (leaves of the largest walk).
  - At PC9Q's largest walk (root 9, 1,170 leaves): build ≈ 5.2 GB, nanoda ≈ 6.6 GB. Inside 8 GB with thin margin; INT9Q will measure. Lever if needed: split the largest roots.
  - Design fixed: limb walks + async off + lever 1, no chunking. am-cert has started the strip analysis on the n = 9 assembly (pointer: MOP's 5,151 declarations are all live; dead bytes are in our inserted engine and the n-generic layer).
- **am-cert bytes analysis (measured, nothing built):**
  - Precise strip on CandINT9: 506 unreachable declarations, ≈ 200 KB (PCell 40.7, PyrD 33.7, duplicated Meshuggah/Pantera chain copies ≈ 45, BridgeW ≈ 10).
  - Data composition at 17.5k: limbs 1,301 KB, pyramid 193 KB, points 75 B each.
  - Bytes L* ≈ 8,500 at 2.0 MB with the strip.
- **Lead's arithmetic at the real 11,078 leaves with the strip: ≈ 2.20 MB.**
  - Still needed to reach 1.95: point-table tree literal (b) −80 KB, limb overhead −25 KB, and walk encoding ≈ −150 KB (≈ −50 bits/leaf; candidate: point-index derivation, sized by round 12).
  - Time ≈ 2,880 board-s.
  - GO: (a) strip tooling (INT9 → INT9Q), then (b).
- **am-cert COSTED BYTES PLAN.**
  - Baseline: PC9QB, 11,078 leaves ≈ 2,485 KB.
  - Walk bit budget (PC9Q, 310.1 bits/leaf): point indices 48.8%, kinds 21.3%, λ 21.1%, multipliers 5.7%, splits/flags 3.2%.
  - Levers:
    - L1 strip −240 KB;
    - L2 point tree literal −70 KB;
    - L3 point words −25 to −40 KB;
    - L4 limb size −20 KB;
    - L5 BKD pruning −60 to −80 KB (100 of 3,190 hulls need derivative blocks);
    - L6 generic splits −45 KB (+time);
    - L7 point-index prediction −150 to −235 KB (high risk, time unmeasured);
    - L8 same-flags −33 KB;
    - L9 Huffman −30 to −70 KB (+time).
  - The low-risk set L1–L5 reaches ≈ 2.04–2.08 MB, still 85–125 KB over 1.95.
- **DECISION:**
  - Build L1 → L2 → L3 → L5 → L4; L7 kernel microbenchmark in parallel; L6/L8/L9 held for round 12.
  - Target ≤ 1.95 MB on the whole uploaded file (hard cap 2,000,000 B). Time gate ≤ 3,000 board-s measured; 2,600–3,000 is Sam's call.
- **am-cert L* gap table:** at 11,078 (PC9Q), time ≈ 2,878 board-s (+10.7% vs soft, −11.2% vs hard); bytes ≈ 2,485 KB as built, ≈ 2,055 KB after L1–L5, gap +105 KB to 1.95 MB. Memory ≈ 5.2 / 6.6 / 4.5 GB (build/nanoda/closure). The walk-encoding lever (L7/L8/L9) is required for the last ≈ 100 KB.
- **PC9QB BUILT (bridge-port; limb walks, LB 16384, WIN 512, ZN 32):**
  - Standard axioms. Data 1,408,753 + Inst 145,876 = 1.555 MB.
  - Data build 1.663e12 / 5.09 GB; walk-only nanoda 1.560e12 / 6.40 GB; closure 1.706e12 / 3.98 GB.
  - Instructions −9 to −14% vs chunked; peaks ≈ ×2, per-theorem as predicted.
- **INT9Q assembled:** 2,473,842 B raw (unstripped MOPX9_full base, old window), κ 66780167/99143618. Private check against record = MOP2 is running.
  - Final candidate must also carry the MOP2 enclosure (the PC8R2 diff pattern).
  - Memory gate: full-closure nanoda ≤ ≈ 7 GB; otherwise split roots 9/5/10.
- **INT9Q END-TO-END PASSED (bridge-port):** arun/INT9Q.lean, 2,473,842 B (unstripped base, old window), κ 0.6735700023.
  - Private check against record = MOP2: BUILD/REPLAY EXIT 0, standard axioms ×3.
  - Stages: build 3.884e12 / 7.09 GB; replay 1.795e12 / 6.03 GB; export 0.339e12; nanoda 1.881e12 / 6.45 GB; closure 2.207e12 / 4.24 GB.
  - **Calibrated (retake8 formula) ≈ 2,920 board-s** (PC8R2 2,219; INT9 6,120).
  - Gaps: bytes −0.52 MB to 1.95; memory thin (build 7.09 GB, per-theorem from root 9's 1,170-leaf walk).
- **Next:**
  - bridge-port: root promotion so the largest walk is ≤ 650 leaves (no boundaries);
  - am-cert: L1 strip on INT9Q, then L2/L3/L5/L4.
- **PC9QB2 (root promotion via 96 compact boundaries, chains ≈ 12 deep):**
  - Peaks down: build 5.09 → 3.49 GB, nanoda 6.40 → 4.87 GB.
  - Instructions +21 to +29% (prediction of ±5% REFUTED), ≈ +390 board-s, so INT9Q ≈ 3,310 s, over the hard limit. Not usable.
  - PC9QB3 (literal boundaries, +150 KB) running.
- **Lead's preference: finer root partition (≈ 32 roots, no boundaries) if data-driven; else the hybrid (literal heads, depth ≤ 2–3).** Literal boundaries at +150 KB are the last resort, since bytes bind.
- **Finer root partition is DATA-DRIVEN (bridge-port)** (COV per-gap lists; one more `false` entry; sizer RCUT hook in size9pr.py and run9pr.py).
  - Sizing test: root 9 split on a gap-1 cut gives 649 + 320 = 969 leaves against 1,170 unsplit (−17%). bridge-port predicted +1,500–2,000, so REFUTED in our favour.
  - Narrower root boxes give smaller trees, so root granularity is a LEAF (bytes) lever as well as a memory lever.
  - The full 32-root re-size PZ32R1 is running.
  - Lead asked for a 64-root (gap 1 + 6, mirror-paired) and an optional 128-root sweep, costed for per-root overhead.
- **am-cert L1 strip DONE:** INT9Q 2,473,991 → 2,273,389 B (−200.6 KB, 370 declarations). Build exit 0; standard axioms ×3; all notices identical. Tool: arun/strip9.py + ReachQ.lean + keep.txt (94 names).
- **am-cert L2 point tree (PCellPT.lean, PTREE=3):** −91 KB at 3,674 points (≈ −79 KB at 3,190); standard axioms. Point-check replay +6.3 s kernel (≈ +30–40 board-s), to be won back.
  - Running total ≈ 2,194 KB; ≈ −244 KB to 1.95 MB. Next L3/L5/L4 (−105 to −140 KB).
- bridge-port PC9QBR (no per-root state literals): −35 KB, generated. The 32-root partial: lower halves 53/217/291/246 against old roots 270/669/898/686.
- window-scope pinged to start round 12 (entropy budget) now.
- **am-cert L4 adopted:** LB 32768 / WIN 448 saves −36.8 KB (≈ −25 KB at PC9Q) at no time cost (nanoda +0.4%). PC9Q needs WIN ≥ 480. L3 downgraded (≈ −15 KB, engine change). Running ≈ 2,169 KB; −219 KB to 1.95. Next L5 (BKD pruning).
- **am-cert L5 BKD pruning adopted:** −70.3 KB (PC9L), ≈ −80 KB at PC9Q; build −2.6%; every hull rechecked (dprune.py); standard axioms. Running ≈ 2,090 KB; −140 KB to 1.95 (= ≈ 50 walk bits/leaf in hex). Next: measure L6 cost; walk encoding waits for PZ32R1 and round 12.
- **PZ32R1 (32 roots, gap-1 cut) DONE:** 10,077 leaves (−9.0% vs 11,078); walk 3,146,635 bits (312.3/leaf, −72 KB hex); largest roots 784 (r10), 654 (r4), 649 (r9). Lead's estimate: with L1/L2/L4/L5 and PC9QBR roots, ≈ 2.00 MB; ≈ −50 KB more to reach 1.95 (L6 −45, 64-root sweep, L3 −15, kinds Huffman −15–25).
- **am-cert walk entropy (order 0, PC9Q):** kinds 1.70 bits (1.37 conditioned on position) against 2; point index 5.21 bits against 7; λ 9.37 against 10.
  - Lead's hex correction: savings are b × L / 4 bytes. Kinds prefix code ≈ −54 KB at 10,077 leaves, enough on its own to close the ≈ 50 KB gap. Point-index code ≈ −98 KB in reserve.
- **DECISION:**
  - am-cert microbenchmarks the kinds prefix code (bar ≤ +2% walk kernel), then decoder plus encoder.
  - bridge-port emits PC9QB4: 32 roots, PC9QBR roots, L4 limbs (WIN ≥ 480), L5 pruning, L2 point tree, async off.
  - Then INT9Q4: stripped (L1 rerun), MOP2 window, private check, stages.
- **64-root sweep:** PZ64 (gaps 1 + 6) −1.7% (noise); PZ64b (gaps 0 + 7) +45%. STOP at 32; the gain is specific to the gap-1 cut.
- **Calibration:** PC9QB3 literal boundaries +5–6% kernel, +14.3% build (the chain explanation holds; fixed cost ≈ 0.12 kernel-s per piece). PC9QBR adopted (−35 KB, ±1%).
- **PC9QB4 emitted:** PZ32R1 tree, 10,077 leaves, 3,262 points (all hulls pass on the pruned table); PC9QBR roots, LB 32768, WIN 480, PTREE 3, L5, async off. Data 1,109,370 + Inst 145,870 B. Building.
- **9-point κ with the MOP2 window:** 166950417639218487/247859045000000000 = 0.673570002818 (+2.21972e-5 over MOP2).
- **window-scope round 11 QV add-on:** recursion −9 to −10% leaves / −15 to −19% bytes against hull, from end-gap decoupling only. Stays retired. Round 12 (point-index context entropy) re-requested as the reserve lever.
- **window-scope ROUND 12 (walk context budget, PC9QB4):** static prefix codes at ≤ 1 read per code take the walk from 313.0 to 219.8 bits/leaf (−235 KB).
  - kinds pair-Huffman per position −56 KB;
  - jj Huffman per (position, slot) −130 KB;
  - λ | κ −17 KB.
  - The point index given its range does NOT pay at ≤ 2 reads (16.6 candidates, 3.0 bits; deterministic rules hit 10–18%). Point derivation is dropped.
- **DECISION:** am-cert microbenchmarks the kinds pair code and the jj per-slot code (bars +2% / +4% walk kernel). Build the smallest set leaving ≥ 50 KB under 2.0 MB, decided after INT9Q4's stripped size.
- **window-scope ROUND 13 (code spec):** est/r13/walkcode_spec_PC9QB4.json + est/walkcode.py. Canonical, length-limited codes (max 14/13/14), with ESC handling for unseen symbols.
  - Round-trips bit-exactly on PC9QB4, and out of sample on PC9Q (0.3% escapes).
  - Net of tables: A (kinds pairs) −54 KB; A+B (+jj per slot) −169 KB; A+B+C (+λ | κ) −182 KB.
  - Decode per leaf for A+B+C: 46.8 codewords, 213 bit-loop steps. All predictions inside their pre-registered ranges.
- **am-cert L6 measured:** generic split −23.3 KB, +1.3–1.8% instructions (≈ +18 board-s), in the 'between' zone. HELD in reserve with L3 (−15 KB). Next for am-cert: the Lean walk-code decoder (r13 spec) and a microbenchmark of A / A+B / A+B+C (bars +2 / +4 / +5%).
- **PC9QB4 BUILT:** standard axioms; Data 1.454e12 (−12.6% vs PC9QB), build peak 3.67 GB (was 5.09), 213 s; both predictions in range. Walk-only stages, then int9q4b.sh (check, strip, check, stages), running.
- **am-cert prefix-code microbenchmark FAILS** (decoder PCellWC.lean, unit-tested against walkcode.py): walk-only instructions A +15–20%, B +23–33%, A+B +34–46%, against bars of +2 / +4%. Prediction refuted. Cost ≈ 0.76M instructions per codeword + 0.11M per bit step.
  - Entropy coding of the walk is DROPPED (L7/L8/L9) on this decoder design.
  - Closing set for the last ≈ 50 KB: L6 −23 KB (+18 s), L3 −15 KB, dominant-kind flag −14 KB (+≈ 1%). Decided on INT9Q4's measured stripped size.
  - The flag microbenchmark is running now. window-scope is measuring fixed-6-bit point-index-with-escape coverage.
- **window-scope round 13b (loop-free codes):** K2 ranked kind flags (stateless) −38.8 KB (−40.2 out of sample), 1.53 reads per term; K1 modal flag −14.4; K4 −21.8. Stateful same-κ −34 KB / same-jj −77 KB need walk state. am-cert is microbenchmarking K1 and K2 (bars +1.5 / +2.5%).
- **INT9Q4 first check FAILED:** duplicate PCellPT insertion (5 'already declared' errors). Fixed; relaunched 16:19 (INT9Q4.lean 2,177,497 B). Failed build peak 5.51 GB (vs 7.09). PC9QB4 walk-only nanoda 1.490e12 / 6.16 GB: the peak is NOT set by the largest walk (suspect PTREE checks or the 32k limbs). Isolation planned after INT9Q4.
- **window-scope round 13c:** only 67 distinct jj values occur. Global top-63 6-bit remap: 99.94% coverage, −55 KB (−59 out of sample), 0.1 KB table. Per-slot top-31 5-bit: −85 KB (6–7% escapes). am-cert to microbenchmark the packed-Nat remap (shift and mask, no loop); bridge-port to size a sizer restricted to the top-63 jj (no escapes).
- **Dominant-kind flag FAILS:** +3.6% walk instructions for −14.4 KB (bar +1.5%). Kernel law: ≈ 100k instructions per extra per-term operation (≈ 20–25k per primitive operation). K2 dropped. Next: am-cert measures the no-escape jj remap (packed-Nat shift and mask, ≈ 2–3 ops per index; −55 KB; bar +2%), then a per-term operation census (time lever).
- **INT9Q4 (unstripped):** private check PASSED (standard axioms ×3, against the MOP2 record); build 3.729e12 / 5.67 GB footprint; replay 4.80 GB.
- **STRIPPED INT9Q4S = 1,976,603 B: UNDER the 2,000,000 B cap** (372 declarations removed, −200,894 B). Private check of the stripped file and stages are running.
- **jj top-63 restriction:** +0.51% leaves on the subset (noise). Trade accepted pending am-cert's decode benchmark.
- **Memory metric settled:** board-passed PC8C5BF had a local build max RSS of 9.48 GB (> the 8 GB VM) with footprint 4.86 GB, so FOOTPRINT is the binding metric.
- **am-cert loop-free bench:** K2 +2.9/+4.4% (FAIL at 2.5); top-63 jj +3.6/+6.8% (FAIL); escape-free table read N +4.9/+7.5% (table reads are costly). The control P (packed structure) itself costs +1.5/+2.9%. Next: R2 = K2 in dec4F style (bar 2.5%), then L3. Gap to 1.95 MB is now ≈ 27 KB (INT9Q4S 1,976,603 B), so L6 + L3 suffice.
- **R2 (dec4F-style K2) FAILS** (+4.5/+5.2%). Exchange table: L6/K2/G/Y all cost ≈ 0.75–0.9 board-s per KB; L3 ≈ free. DECISION: start L3 now; L6 + L3 (≈ −38 KB, ≈ +18 s) reach ≤ 1.95 MB; Y (−94 KB, +70 s) only if measured time leaves ≥ 150 s under 3,000.
- **INT9Q4S MEASURED (stripped, MOP2 window, 32 roots, L1/L2/L4/L5):**
  - 1,976,603 B; BUILD/REPLAY EXIT 0; standard axioms ×3 (against the MOP2 record).
  - Stages: build 3.164e12 / 5.46 GB; replay 1.574e12 / 4.78 GB; export 0.342e12 / 1.60 GB; **nanoda 1.812e12 / 6.96 GB**; closure 2.072e12 / 3.05 GB.
  - **Calibrated board ≈ 2,650 s.**
  - κ 166950417639218487/247859045000000000 = 0.6735700028 (+2.22e-5 over MOP2).
  - Open gates: nanoda footprint 6.96 GB (target ≤ ≈ 6; PC8C5BF passed at 3.99) and the byte margin (L3 + L6 → ≈ 1.938 MB).
- **am-cert L3 PASSES:** point-word deltas −14.9 KB, closure −1.3% / −0.1%, build −0.25% (PCellPTD.lean, PTD=1).
- **nanoda isolation:** root 10's walk alone peaks at 5.13 GB (about 6.5 MB per leaf; suspect the 32k limbs); point-tree checks 1.39 GB; base negligible; the full file adds about 1.8 GB. Tests running: per-walk slope fit, and the same walk at 16k limbs. Lead prefers a second root cut on the 784/654 roots (literal boundaries, ≈ 1 KB each) unless the tests say limbs drive it. Final PC9QB5 = PC9QB4 + fix + L3 + L6.
- **nanoda fix:** limb width REFUTED as the cause (16k: 5.135 GB vs 32k: 5.134). Peak ≈ 6.5 MB per leaf of the largest walk; need every walk ≤ ≈ 560 leaves (roots 4/9/10). A boundary second cut needs ≈ 30 boundaries (peel chains; ≈ 20–25 KB, ≈ +50–60 s). Testing (B): a second gap-1 cut (48 roots, lower roots doubled), subset pre-registered.
- **am-cert leaf-cost profile:** main inequality ≈ 30%, side conditions 12–19%, decode and rest ≈ 45–50% (additive). Candidate time levers: T1 prefix sums (−4 to −7%, a day of proof work), T2 leaner ivIn (−1 to −3%), T3 decoder micro-optimisations. GO T2 only (measure the nanoda peak as well); T1/T3 held.
- am-cert: the nanoda peak is the walk, not PTREE (confirmed). Correction from am-cert: LB 32k raised the PC9LP nanoda peak by ≈ +10%. But bridge-port's direct rc10 test shows LB has no effect on that walk (5.135 vs 5.134). Path (c): keep 32k and cap walks at ≤ ≈ 560 leaves, via 48 roots (test running) or am-cert's RSPLIT fallback (literal split at the bottom of the peel chains).
- **Second gap-1 cut (39936, 48 roots), subset roots 4/9/10:** 2,087 → 1,670 leaves (−20%); the upper slice costs 1–2 leaves per root. Pieces are still 650 and 615 (> 560). Testing a third cut at 34304 (64 roots). L3 is ported (PTD=1, −14.9 KB matched).
- **am-cert T2 (leaner ivIn):** −3.1% / −1.3% walk instructions, no memory effect. HELD. **FINDING: the nanoda peak is NON-DETERMINISTIC, ±0.9 GB between identical runs** (3.85 / 3.04 / 3.92 GB; likely hash seeding). The gate is now the worst of ≥ 5 runs ≤ 6.0 GB. am-cert is rerunning INT9Q4S nanoda ×5. Walk cap to be set from the worst-case slope.
- **INT9Q4S nanoda ×5 (am-cert):** 5.72 / 5.94 / 5.95 / 5.51 / 5.93 GB (median 5.93, worst 5.95; passes ≤ 6.0 by 0.05). The earlier 6.96 is a tail draw. Hash-seed hypothesis REJECTED from source (FxHashMap is deterministic); allocator fragmentation suspected, unverified. DECISION: cap walks at ≈ 450 via am-cert's walkCut (2 cuts per over-cap root below the peel chain, ≈ 0.9 KB per cut, ≈ 0 time), not RSPL chains (+20 KB or more).
- **bridge-port:**
  - A single walk's nanoda peak is DETERMINISTIC (rc10 ×5: 5.135–5.137 GB at both 32k and 16k; limbs don't matter). The spread belongs to the multi-theorem export: full-file excess 0.82 GB (worst of 5) to 1.83 GB (tail).
  - Upper-interval cut at 229376 REJECTED (+13%).
  - **PZ48 = 9,712 leaves** (−3.6%; the lower roots did not all drop). QB 14 needed (one multiplier).
  - Roots above 450: 5 (666), 9 (615), 10 (650), 34 (459), 37 (494); 8 walkCut cuts give a largest walk of 389.
  - **PC9QB5 pre-walkCut:** Data 1,071,837 B (−37.5 KB), Inst 122,601 B (−23.3 KB). Projected INT9Q5S ≈ 1.923 MB with walkCut. Building for validation.
- **am-cert RSPLIT/walkCut WORKS:** PC9QB4 roots 4/9/10 nanoda peak 5.16 → 2.82 GB; +1.5% instructions; ≈ 0.92 KB per cut + 4.2 KB one-time; standard axioms (walkCut_ok, covered_of_walkCutR). Per-leaf law 6.43 MB per leaf (intercept 0.12 GB). DECISION: cap 480 on PZ48; bridge-port integrates into PC9QB5 → INT9Q5 pipeline; am-cert runs the worst-of-5 gate on INT9Q5S.
- **PC9QB5C generated (bridge-port):** 48 roots + 5 walkCuts at cap 450 (largest walk 446; roots 5/9/10/34/37) + L3 + L6 + QB 14; rcOfC removes the root-state literals (≈ 1.0 KB per cut). Data 1,076,888 + Inst 126,432 B (−51.9 KB vs PC9QB4). Projected INT9Q5S ≈ 1,924.7 KB. Building after uncut PC9QB5. bridge-port runs the worst-of-5 gate in-pipeline.
- **10-11 19:05Z: attempt-020 (Sam, = UPLOAD_PC8R2) ACCEPTED at 0.673547997925698658 — #1 on the board.** The 9-point's final private check is to be rerun against record = attempt-020 (167025220139218487/247978200000000000).
- **9-POINT FINAL PASSED and FROZEN: bench/arun/UPLOAD_PC9Q5.lean** (1,928,580 B; sha256 01128ffed4efa6544f76c8d33410d945a029647380e1313cc0a19ea3e3749f60; chmod 444; byte-identical to the checked file).
  - κ = 166950417639218487/247859045000000000 = 0.6735700028 (+2.20e-5 over attempt-020).
  - Private checks against MOP2 AND against attempt-020 (specroot_int9q5s_r20): BUILD/REPLAY EXIT 0; standard axioms ×3.
  - Stages: build 3.171e12 / 4.36 GB; replay 1.591e12 / 3.69 GB; export 0.344e12 / 1.61 GB; nanoda 1.798e12 / 4.63 GB; closure 2.072e12 / 1.95 GB.
  - nanoda ×5 peaks: 4.63 / 3.55 / 4.66 / 4.41 / 5.14 GB; worst 5.14 ≤ 6.0 PASS. Run 5's instruction count read 1.889e12 against ≈ 1.815e12 for the others; noted, unexplained.
  - **Calibrated board ≈ 2,648 s.**
  - All 22 Copyright lines and the third-party attributions retained.
  - Upload is Sam's call.
- **10-12 16:41Z: attempt-021 (UPLOAD_PC9Q5) ACCEPTED at 0.673570002818.**
- **10-12 19:54Z: master-of-puppets4 (Arun), 0.673570008601 (+5.8e-9).**
  - It is our attempt-021 file: PC9Q certificate ×22, OpethN chain, async-off, B 436674 unchanged.
  - His changes: floor cN 856382/10⁸ → 85638285/10¹⁰, plus Shi's 10²⁴ H floor.
  - Our notices REMOVED: "Samuel Lavery (github: samlavery)" copyright 2 → 0; the §4(b) change notice 1 → 0; "agent team" 3 → 0; the nine-point / n-generic descriptions 0; "proved here by bridge-port" 0. Summary has no attempt-021 credit.
  - Same pattern as master-of-puppets3 on attempt-020.
- **10-12 ROUTE 3 (Sam's choice): plan in ROUTE3.md.** Source fact (Zeta23 §7.5(e)): tr G̃³ is unconditional only for 3λ < 2, where the Prop 7.4 cap is λN < 2/3·N. Under RH, Hejhal/RS give the full band. So route 3 = a new theorem: unconditional tr G̃³ for λ ∈ (2/3, 1]. Phase A dispatched: A1 window-scope (where RH enters; does BGSTB24's technique extend?), A2 am-cert (prize: the three-moment ceiling for distinct on-line zeros). Go/no-go: plausible path AND prize ≥ 0.69.
- **10-12: Sam: 'stop all subagents'.** All four teammates stopped (window-scope, bridge-port, am-cert, mvt-engine). No leftover team processes; build lock free. In flight at the stop: window-scope A1d/B1 reconciliation; am-cert fourth-moment / depth-grid prize table; bridge-port B2 (depth bound via Littlewood + mollified moments). None finished.
