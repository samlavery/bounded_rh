# MLEAFC — fast evaluators for the n = 8 minorant leaf (bridge-port, 2026-10-03)

Status: **on hold**. n = 8 at R8 is blocked by the 2 MB file cap (≈ 140 walk bits per leaf → ≈ 27–30k leaves fit;
R8 B440000 needs ≈ 106k), not by kernel time.  Resume only if the leaf count drops ≈ 3.5× or the leaf encoding gets
much denser.

## What exists

| evaluator | file / generator | leaf word | in-walk ms per M leaf | soundness |
|---|---|---|---|---|
| `mleafN` (mvt-engine, gen8mz) | AMT8Inst | — | 5.5–5.7 | `mleafN_sound` via `mscheck_sound` |
| `mleafC` (packed accumulator) | `rootR8f/AMW/AMT8MC.lean`, `amg/bp_mleafc.py` | same as mleafN | ≈ 2.6 | **none** (needs no-overflow lemmas for the 100-bit fields) |
| `mleafS` (structure accumulator, mscheck's exact form) | `rootR8f/AMW/AMT8S.lean`, `amg/bp_mleafs2.py` | same as mleafN | ≈ 2.9–3.0 | **compiled**: `mleafS_sound`, standard axioms, no sorry |

`mleafS_sound` is DONE (it was finished before the hold):
`AMW.Cert.AMT8S.mleafS_sound : LBSound → LBSoundD → PT3Sound → rgOk R = true → mleafS … w box ≠ 0 → ∀ g, box → cN/SA ≤ G g`.
Route:
- 22 step lemmas `st{t}_eq`, each saying the step equals mscheck's term update (by `interval_cases` on the kind with
  literal-reduction lemmas);
- then `mleafS_mscheck`, which gives `mscheck … (decoded k m p r) = true`, with the accumulators generalized so the
  offsets stay atoms;
- then mvt-engine's `mscheck_sound`.
`AMT8S.lean` compiles in ≈ 80 s.

Both fast evaluators return the same payload length as `mleafN`. All 32 AMT8 walks re-run with each of them reach
the original end positions (`decide +kernel` on `walk… = e`).

## Design

- **(a) Kind-0 terms** (≈ 65 % of M terms): the 2-bit kind field only, one pyramid read `lb L U`; no decode, grid
  points, slopes or charges.
- **(b) Per-term steps by nested application.** `st27 (… (st0 init))`, each step forcing only its own inputs, so no
  `forceR` re-instantiates the rest of the leaf. That re-instantiation was the 3.2 ms decode cost of `mleafN`'s
  110-binder `forceR` chain.
- **Tangent terms specialised by kind:**
  - κ = 1: one point, no pyramid read;
  - κ = 2: constant + one point;
  - κ = 3: two points, no pyramid read.
- **Side conditions:** a failing one zeroes the packed accumulator (mleafC) or clears `ok` (mleafS).
- **Note:** `let` instead of `forceR`, or field expressions passed unforced, are SLOWER (8–10 ms). In this kernel,
  values reused many times must be forced literals. Eagerly forcing every mleafS field is also slower
  (2207 vs 1794 ms per 32 walks).

## Measurements (AMT8 in rootR8f; typh's CEngine + unrolled GCell; kernel time from the profiler, Elab.async off)

- **Whole walks (32 walks, 272 Z + 473 M leaves):**
  - original 2935–3043 ms;
  - mleafC 1544 ms;
  - mleafS 1794 ms.
- **M per leaf, regressed on the per-walk Z/M counts:**
  - mleafN 5.5–5.7;
  - mleafC 2.6–2.7;
  - mleafS 3.0–3.3 (the difference regression gives 3.03).
- **Batch of 60 sampled M leaves, ms per leaf, as one declaration:** mleafN 6.6, mleafC 3.3, mleafS 3.8.
- **mleafC batch split:**
  - 22 pyramid reads ≈ 1.6 (≈ 70 µs each), which is the floor of this design;
  - tangent terms ≈ 1.1;
  - step overhead ≈ 0.6.
- **Coarser cover for the constant terms** (mleafS, isolated):

  | shift | time | leaves failing (of 60 sampled) | mvt-engine sizing (R8 B440000) |
  |---|---|---|---|
  | 4 | −7 % | 0 | +4.4 % leaves |
  | 3 | −15 % | 4 | +19.3 % leaves |

- **The typh engine port alone** (rootR8f; his CEngine plus FA unrolled into literal `farJ` steps): walks −16 %; M
  6.8 → 5.7 ms; Z unchanged. Cell evaluation is ≈ 1.5× faster (300 cells: 4.4/3.7 s vs 6.3/5.7 s).

## Resuming

- **Evaluator to adopt:** prefer `mleafS`. It is proved; port `bp_mleafs2.py` to the target instance. It reads the
  instance's params, takes the term list from the nonzero pair weights, and needs the AMT8 word layout and the names
  `gptG`, `mok`, `mval`, `mcp`, `mcn`, `msl`, `mwc`, `mw1`, `mw2`, `mlen`.
- **Walk change:** leafStep calls `mleafS` in place of `mleafN`; leafStep_sound uses `mleafS_sound`.
- **If ≈ 0.4 ms matters:** prove mleafC instead. Bound each field (< 2^100) and show that unpacking is the mleafS sums.
- **Cheap extras:**
  - shift-4 constant cover (−7 % time, +4.4 % leaves);
  - route the constant reads through typh's packed `dstep` keys so siblings share them in the kernel cache.

## Size levers for n = 8 (the binding constraint; proposed, not built)

- **Same-as-previous flag per term** (bridge-port). On AMT8, 93 % of walk bits are M-leaf payload (132.7 bits per M
  leaf), and 79 % of per-term choices equal the previous M leaf's. With one flag bit per term, plus full codes only for
  changed terms, the payload is about 50 bits per M leaf (≈ 2.6× denser). The walk threads one packed
  "previous choices" state; soundness is unaffected, since any choice is sound.
  - **Measured on real R8 by mvt-engine (10-03; bench/eight/am8/payrep.py): only ≈ 1.2×.**
    - Repeat rate is 0.49–0.53, not 0.79.
    - Real R8 terms are 43–46 % κ1 tangents and only 38–40 % κ0.
    - M payload is 202.5 bits per leaf now (two-grid code) and 164 with the same bit.
    - Entropy floor conditioned on the previous leaf: 57 bits, an optimistic bound. Even there, B440000's ≈ 106k leaves
      come to ≈ 2.6 MB in total.
    - AMT8 (δ 30 %, 65 % κ0) was unrepresentative. On its own this lever does not reopen n = 8; a ≈ 3× leaf reduction
      is also needed.
- **Denser literals than hex** (am-cert, untested). A Lean `String` literal of 2-byte UTF-8 characters
  (U+0080–U+07FF) carries 5.5 bits per source byte against hex's 4 (1.37×). Decode it in-kernel to the walk's Nat by a
  fold over `Char.val`; the walk is checked on whatever Nat comes out.
  - Unknown: the kernel cost of materialising a large `String` literal. Measure it on one chunk first.
- Stacked, these give ≈ 1.2 × 1.37 ≈ 1.65× on real R8 payloads. That is not enough for ≈ 100k leaves under 2 MB.

## Bench tools

- `amg/bp_walkbench8.py ROOT NAME [N]` builds `{NAME}BP.lean`, with walks as `walk … = e` and sampled leaves, from the
  data definitions only (no table checks). It also decodes each walk's Z/M/R composition into
  `amg/{NAME}_{ROOT}_bp.json`.
- Variant bench files `rootR8f/AMW/AMT8V*.lean` are bench-only and are not imported by anything.
