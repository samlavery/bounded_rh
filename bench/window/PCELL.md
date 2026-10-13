# PCELL — polytope cells (pair-distance splits): Lean design (bridge-port, 2026-10-03)

## Status

All Lean pieces are compiled at Q = 3 and at **Q = 7**.
- Pieces: splits, tightening, multipliers, the Farkas leaf, the degenerate-range and PLO cases with the two-grid `gptF`, the generic leaf proof, and the generic per-gap root cover.
- Axioms are exactly `[propext, Classical.choice, Quot.sound]`; there is no `sorry`, `axiom` or `native_decide`.
- End-to-end `decide` instances (empty tables):
  - `PCell3I.root_box`: a split, tightening and a multiplier leaf;
  - `PCell3I.farkas_cell`: an LP-infeasible cell that two tightening rounds miss, closed by a Farkas leaf;
  - `PCell3RI.cert`: the whole certificate `∀ g ≥ 0, Pg`, through the root cover, one root cell and its walk.
- No separate zero-order leaf (lead's decision): a Z cell is a minorant leaf with every term constant.

| | v1 (56-variable lemmas) | now |
|---|---|---|
| Q = 7 instance | 481 KB | **87.9 KB** (with the mask loop) |
| generic layer (once, any Q) | 10.7 KB | 68.5 KB (`PCellCore` 12.6, `PCellGen` 29.5, `PCellLeaf` 16.4, `PCellRoot` 10.1) |
| polytope layer total | 492 KB (no root cover) | **156.4 KB** raw (root cover included). It was 147.4 before the mask loop (+5 KB instance) and the kind-aware leaf (+3.8 KB generic) |

Comparison with the box instance `AMT8Inst`: 146.2 KB raw, 142.6 KB without comments. It includes a zero-order leaf and the root cover.
- With the polytope layer, the engine's `mterm_min`/`mterm_ok`/`mok` (6.3 KB, in `CMin`) are no longer used. The anchored versions replace them.
- Net, the polytope layer costs ≈ 141 KB where the box instance costs 146 KB.

## Files (all new; nothing existing was modified)

| file | what |
|---|---|
| `rootR8f/AMW/PCellCore.lean` | `nmax`, `lo_nmax`/`hi_nmin`, `fb_lo`/`fb_hi`, `natsub_diff`, the one-point tangent `tcheckP`/`tangent_certP`, the anchored minorant `mterm_minA`/`mterm_okA` (with a separate constant-read range) |
| `rootR8f/AMW/PCellGen.lean` | `Cl`, `InCell`, `CovBy`, the splits (`cov_gmid`/`cov_smid`), `sumR`/`imap`, tightening (`fbC`, `fb_gen`), multipliers (`MulOKg`, `mul_step`), the Farkas test (`fsum`, `farkas_cov`), `incell_root`, kernel helpers (`tl tu fb1 dec4 fk fm fj plen gptF uc`, `mokT mvT …`, `mtermT`) |
| `rootR8f/AMW/PCellLeaf.lean` | the functional `Fg`/`Pg`, the term list `TS`, the generic check `mcheckG` (`isum`/`iall`) and **`mcheckG_sound`**, for any Q and term list |
| `rootR8f/AMW/PCellRoot.lean` | `coverChk`/`coverChk_sound`, `rootCl`, **`root_cover`**: the per-gap root cover for any Q |
| `amg/genpcell2.py ROOT NAME Q [--bench]` | the instance generator; env `NR`, `QB`, `SIGSH`, `CN`, `PCOUT` |
| `rootR8f/AMW/PCell3.lean`, `PCell3R.lean` | Q = 3 instances (cN = 550000, 40000) |
| `rootR8f/AMW/PCellT7.lean` | the Q = 7 instance (18 s) |
| `rootR8f/AMW/PCell3I.lean`, `PCell3RI.lean` | the end-to-end instances |
| `rootR8f/AMW/PCell3Ax.lean`, `PCellT7Ax.lean` | `#print axioms` |
| `rootR8f/AMW/PCellV8N{0,1,2}.lean`, `PCellV8B.lean`, `amg/bp_pcellv8.py` | walk bench (AMT8's 32 walks in the polytope layout) |
| `rootR8f/AMW/PCellM8B.lean`, `amg/bp_pcellm8.py` | leaf bench: 60 of AMT8's minorant leaves, `mleafN` against `mleafP` (payload re-encoded; jj = 4j + 64 reproduces AMT8's grid points) |
| `amg/genpcell.py` | the v1 generator (superseded) |
| `rootR8f/AMW/PCellHuff.lean`, `amg/genpcell3.py` | the canonical-Huffman decoder and the Huffman instance generator (section below) |
| `rootR8f/AMW/PCell3H{,R,I,RI,Ax}.lean`, `PCellH7{,Ax}.lean` | Huffman instances: Q = 3 end-to-end, Q = 7 |
| `rootR8f/AMW/PCellHG7.lean`, `PCellHGT.lean`, `PCellHGN.lean`, `amg/huffmirror.py` | golden-vector decode test, controls, Python mirror |
| `rootR8f/AMW/PCellHB7.lean`, `PCellHL7.lean`, `PCellH8B.lean`, `PCellHW8B.lean`, `amg/bp_pcellh8.py`, `amg/bp_pcellhw8.py` | Huffman leaf and walk benches |
| `rootR8f/AMW/PCellTZ.lean`, `PCellZ.lean`, `PCellLeafZ.lean`, `PCellT1.lean`, `amg/genpcell4.py` | T1 and Z: generic soundness, kernel shapes, generator (section below) |
| `rootR8f/AMW/PCell3T{,I,R,RI,Ax}.lean`, `PCellT7Z.lean`, `PCellTZG.lean`, `amg/tzgold_lean.py` | T1/Z instances, golden tests |
| `rootR8f/AMW/PCellT7B{,P,E,L}.lean`, `PCellZAx.lean` | T1 cost variants (bench), axioms |

## The design

**Two layers.**
- The kernel functions are unrolled per instance, over the curried state: gap bounds `l_r u_r`, then pair bounds `A_t B_t` in pair order.
- The propositions see the state through `St` and `toCl s : Cl`, four literal lists.
- Every split, tightening pass, multiplier entry, the minorant leaf and the root cover are proved **once**, generically.
- Each kernel node gets a one-line link, by definitional unfolding.
  - The links use section variables and two small macros (`pc_spl`, `pc_fbl`), so a node costs one line.

**(1) `Covered`** is `CovBy Q PR (Pg cN Q BS TS)`.
- `Pg g` is `cN ≤ Fg g ∨ g (Q−1) < g 0`, with `Fg = Σ_r b_r g_r + Σ_n a_n w(gsum g i_n j_n)` in units of 1/SA.
- `TS` is the term list `(i, j, a, k)`; `k` is the pair index of a non-adjacent pair.

**(2) Splits** use `cov_gmid`/`cov_smid` at the kernel midpoints, through `sp_ok`. A split is 6 bits.

**(3) Leaf.**
- Kernel: `mleafP`, the `dec4` chain then `ydec`, then the unrolled `mcheckP`.
- Bridge: `mcheckP_ok` gives `mcheckP = true → mcheckG = true` by definitional equality (`:= h`).
- Soundness: the generic `mcheckG_sound`. The argument is mvt-engine's `mscheck_sound`: per-term anchored minorants, slopes regrouped by gap, per-gap `gap_lo`, the multiplier invariant, and one final `linarith` over aggregate sums.
- Term fields: `[κ 2][j1 7][j2 7 if κ = 3][λ 10 if κ ≥ 2]`. Positions go through mvt-engine's `gpt` (`gptF`: JSH = 5, fine-grid bit 6, PLO at 33).
- The constant is read on `[L, max(U, L + 1)]` (`uc`).
- `tcheckP` accepts the one-point range `L = U = p` with both slope claims.
- Multipliers: `[1][c 5][side][Yq 12]`, closed by `0`, `SIG = 1024·U1·SA >> 14`.

**(4) Empty cells** are caught inside the tightening (`fb_gen`) at 0 bits. Kind 8 (LP-infeasible) uses the Farkas leaf, see below.

**(5) FBBT**: Jacobi, NR rounds, pairs in pair order, with the generic `fb_gen`.

**(root)** The generic `root_cover` (after `of_check`) works per gap:
- the window `g ≤ 1/2` pays through the adjacent term (`w ≥ 1/4`);
- `coverChk` covers `[1/2, Smax)`, where clear segments pay through the adjacent term's cell bound;
- from `Smax` on, the linear part pays.

The rest is the product of bad segments, the root cells `rootCl`, which the walks cover. The instance's `cert_of` passes `ADJ` (the adjacent-term indices, checked by `decide`).

## Source bytes per family (Q = 7 compiled; raw source)

| family | Q = 3 | **Q = 7** | Q = 7 v1 | AMT8Inst (box) |
|---|---|---|---|---|
| splits (kernel defs, links, dispatch) | 4.7 KB | **24.7 KB** | 176.6 KB | 15.0 KB |
| leaf check `mcheckP` (kernel) | 4.4 KB | **19.9 KB** | 22.6 KB | 21.3 KB (`mscheck`) |
| FBBT (kernel defs, links) | 2.2 KB | **16.0 KB** | 87.7 KB | — |
| leaf decoder `mleafP` | 1.7 KB | **5.9 KB** | 13.9 KB | 12.5 KB (`mleafN`) |
| base (`PR`, `BS`, `TS`, `St`, `toCl`, `U`, `CovK`) | 2.6 KB | **4.8 KB** | 26.8 KB | 5.4 KB |
| walk + leaf step (with the kind bit) | 4.0 KB | **4.7 KB** | 8.7 KB | 4.9 KB |
| multipliers | 2.4 KB | **3.0 KB** | 86.8 KB | — |
| leaf bridge `mcheckP_ok` | 0.7 KB | **1.6 KB** | — | — |
| root cover (`ADJ`, `cert_of`, `covered_box`) | 1.4 KB | **1.4 KB** | — | 33.2 KB (`of_check` …) |
| Farkas leaf | 0.5 KB | **0.6 KB** | — | — |
| leaf proof | — | **0** (generic) | 34.1 KB | 30.9 KB (`mscheck_sound`) |
| empty-leaf lemmas / zero-order leaf | — | **0** | 22.5 KB | 21.7 KB |
| **instance total** | 24.7 KB | **82.7 KB** | 481 KB | 146.2 KB |

Per-piece deltas at Q = 7:
- Item 2 (gptF, PLO, degenerate read): +1 KB instance, +3.5 KB generic.
- Generic leaf proof: −19 KB instance (`mcheckP_sound` gone, a 1.6 KB bridge added), +16.4 KB generic.
- Root cover: +1.4 KB instance, +10.1 KB generic (replacing the box instance's 33 KB).
- Link macros: −6.4 KB.

## Kernel cost

**Tightening, with the mask-bit loop.** The state carries a mask `M` of the pairs ever split; a pair split sets its bit.
- `fbN` runs NR rounds of `fbL`, which visits only the set bits, lowest first (that is, pair order).
  - Each visit takes the lowest bit with `m − (m & (m−1))`, then `Nat.log2` (kernel-accelerated), then a binary dispatch `fbD` on its 5 bits to `fb_t`.
- A never-split pair cannot tighten, since its effective range is `[Σl, Σu]`. So the loop matches the full 21-pair pass exactly, and it matches size8pz, which iterates `cons`.
- Soundness is `fbD_ok` (dispatch tree), `fbL_ok` (induction on the fuel) and `fbN_ok`. `fbN_ok` is proved through an unfolding lemma, `fbN_U`; the direct definitional proof took 50 s of kernel time per module.

Bench: the 32 AMT8 walks (1534 nodes), with A active pairs whose bounds are absent, so every pass runs in full. Extra time per node over the AMT8 walk; that run's baseline was 2.33 ms per node.

| active pairs A | 0 | 1 | 2 | 4 | 8 |
|---|---|---|---|---|---|
| NR = 1 | +0.10 ms | +0.26 | +0.39 | +0.79 | +1.69 |
| NR = 2 | +0.11 ms | +0.34 | +0.66 | +1.41 | +3.19 |

- Fit: ≈ 0.1 ms + 0.2 ms·A·NR. A tightening-free walk with the wrapper only costs +0.05 ms.
- The earlier full pass (all 21 pairs every round) cost +2.4 / +4.8 ms per node for NR = 1 / 2. The loop is faster below about A = 11.

**Leaf, kind-aware evaluation.** `dec4K` decodes a point only where the kind reads it.
- `mvK`/`mcK`/`mslK` read the point table only for the tangents the kind has: a constant term reads no point, a one-tangent term one.
- Proof: four generic equalities `mvK_eq …`, one `beq_dec`, and the bridge `simp only [mcheckP, mvK_eq, …] at h; exact h`. There are no per-term step lemmas.

Bench: 60 of AMT8's minorant leaves, re-encoded, each a separate `decide +kernel` theorem, all in the same run.

| | mean ms per M leaf |
|---|---|
| AMT8 `mleafN` | 10.38 |
| polytope `mleafP`, generic forms (before) | 11.93 |
| polytope `mleafP`, kind-aware (now) | **8.87** (−26 % against before, −15 % against `mleafN`) |

**Walk overhead before the mask loop** (v1 → v2 → items 2–5, extra per node): no tightening +0.1 → +0.006 → +0.06 ms; one full round +2.5–2.9 → +2.72 → +2.44; two full rounds +5.5 → +5.32 → +4.77.

## Tables and windows

- AMT8's tables (`AMT8Data.lean`, generated 2026-10-02 22:39, `amg/mk_AMT8.log`) belong to **`rwin7.json`, the rootR7 window**. They verified there (`amg/chain_AMT8.log`: `rootR7/AMW/AMT8Data exit=0`).
- rootR8 and rootR8f carry identical copies, but those roots are keyed to rwin8, where the `blk_*` checks fail. In rootR8f the bench uses the table *values* for timing only.
- The n = 8 build must generate its tables from the chosen weight set's window (`cnum`) and check them under that same root.
- A real-table PCell3I would go in rootR7. It is not needed for this step.

## Kind 8 (LP-infeasible, survives tightening): the Farkas leaf (built)

- mvt-engine's count on R8 B440000, roots 4+17: 391 of 2,768 leaves. NR = 8 or 32 barely changes it, and splitting instead exceeds 120k leaves.
- Kernel (`fleaf`): decode the multiplier list (`ydec`), then accept when `Cp + Σ_r (u_r − l_r)·(P_r − S_r)⁺ < Cm` (`fsum`, left-nested).
- Soundness: the generic `farkas_cov`. `MulOKg` says the multiplier form is ≥ 0 on the cell, while `fsum_ge` bounds it above on the box by `Cp − Cm + fsum < 0`.
- The test is homogeneous in Y, so any SIG works and small integer Yq suffice.
- Leaf: 2 bits (leaf, kind = 1), then the entry list, ≈ 2 + 3·19 + 1 = 60 bits for 3 entries.
- Toy: `PCell3I.farkas_cell`, standard axioms.
  - The cell: `g0 + g1 + g2 ≤ 101701/SC`, `g1 + g2 ≥ 73848/SC` and `g0 ≥ 28672/SC` is infeasible.
  - Jacobi tightening with NR = 2 only moves it to `l = (28672, 26539, 45995)`, `u = (30805, 27853, 47309)`: not empty, not reflected.
  - Two entries (`Yq = 1` on `B03` and on `A13`) close it.
- Bytes: +1.3 KB at Q = 7 (instance), +2.5 KB generic.

## Leaf layout (as the kernel reads it)

This is the fixed-width layout of genpcell2. The canonical-Huffman layout of HUFF.md supersedes it (section below).

- Bit 0 = 0: a leaf.
- Reflected (`u_{Q−1} < l_0` on the tightened cell): 1 bit in total.
- Otherwise bit 1 is the kind: 0 is the minorant leaf, 1 the Farkas leaf. The payload starts at bit 2.
- No zero-order kind (lead's decision): a Z cell is a minorant leaf with every term constant (κ = 0, 2 bits per term).
- Minorant payload, per active term in `TS` order: `[κ 2][j1 7][j2 7 if κ = 3][λ 10 if κ ≥ 2]`, then the multiplier list.
- Farkas payload: the multiplier list only.

## What the sizer must match (size8pz; mvt-engine confirmed the first four)

- Tightening: Jacobi per pair, NR = 2, pairs in pair order. Empty cells cost 0 bits.
- 6-bit splits (5-bit axis), at the midpoints of the gap range and of the effective pair range.
- Leaf fields on the effective ranges, charges at the box corner. Multiplier entries `[1][c][side][Yq]`, closed by `0`.
- `SIG = 1024·U1·SA >> SIGSH` (default 14) and `QB` follow the sizer's chosen quantum.
- Built into the kernel (all three):
  - the degenerate range read `lb(L, max(U, L + 1))`;
  - the PLO one-point tangent (`tcheckP`, position 33);
  - mvt-engine's `gpt` as `gptF` (JSH = 5, fine-grid bit 6).

## Canonical-Huffman walk (HUFF.md; built 2026-10-03)

The walk format is now mvt-engine's `bench/eight/am8/HUFF.md`. Generator `amg/genpcell3.py` (genpcell2 stays as the
fixed-width reference); the decoder is `rootR8f/AMW/PCellHuff.lean`. Q = 3 and Q = 7 compile with the standard axioms.

**Representation.** Each canonical table goes into the instance as hex numbers, not as a `List (ℕ × ℕ)`. The information
is the same, and the kernel reads a field with one shift and one mask.
- `HC` holds the count of each code length, from length 0, in 16-bit fields.
- `HS` holds the symbols in table order, in 16-bit fields.
- `HL` (optional, env `HLUT = K`) is a lookup with 24-bit entries `symbol + 2^16 (length + 1)`. It is indexed by the next
  `min(K, maxlen)` bits in walk order; the entry is `0` when no short codeword is a prefix.
  - When a table's `maxlen ≤ K` the lookup is complete and `HC`/`HS` are dropped.

**Decoder.**
- `hdec` is HUFF.md §3's loop on a 32-bit window: at most 33 steps; it returns `symbol + 2^16 · length`.
- `hdecL` tries the lookup first, then falls back to `hdec`.
- `dec4S` reads a term's λ and grid points from the symbol. The weight is `m = λ · 2^(10 − LB)` of 1024, so it is exact at
  LS = 256 and `mcheckP` is unchanged.
- Nothing in the decoder needs a proof. Decoded values only feed the checked leaf or a split, which are sound for any
  value. `mleafP_ok` is still `simp only [dec4S, forceR_eq]` plus the generic `mcheckG_sound`.
- Grammar changes in the instance:
  - a split decodes its axis, and its children start at the bit after the axis code;
  - `ystep` decodes `c` and takes the `Yq` width as an argument (12 for the minorant leaf, 4 for the Farkas leaf);
  - the multiplier fuel is 42, one entry per (constraint, side).

**Golden vectors.**
- `PCellHGT.golden`: the kernel decodes the whole root-15 walk of `huff_golden_g15.json` and ends at bit 21,281 =
  1 + 21,280.
  - The walk has 209 splits, 4 reflected, 185 minorant and 21 Farkas leaves, with no empty node.
  - This is the decode-test instance `PCellHG7` (genpcell3 `--decode`, LUT 5). It replaces every minorant check by
    `true`, because the window's tables are not in rootR8f. The 21 Farkas leaves are checked for real with huffenc's
    4-bit multipliers.
- Controls (`PCellHGN`):
  - flipping walk bit 10,000 moves the end;
  - raising one Farkas `Yq` from 1 to 2 (same bit count) makes the walk return 0.
- `amg/huffmirror.py` runs the same decode in Python. It ends at 21,281 and matches the axis and bits of the 20 golden
  nodes.

**Q = 3 toy.** `PCell3H`/`PCell3HR` use toy tables with the lookup at K = 2, so both the lookup and the fallback loop run.
- `PCell3HI` re-proves `root_box`, `childB_leaf` and `farkas_cell`; the walks are 30, 19 and 20 bits, against 51, 29 and 36
  fixed-width.
- `PCell3HRI.cert` re-proves `∀ g ≥ 0, Pg` through the root cover.
- `PCell3HAx`, `PCellH7Ax`: all axioms are standard.

**Bytes.**
- Generic: `PCellHuff` 3.7 KB (2.2 KB without comments).
- Q = 7 instance `PCellH7` (B440000 weights, all 28 pairs active, golden in-sample tables, LUT 5): 102.4 KB.

| family | PCellH7 | PCellT7 (fixed width, AMT8 weights, 22 active) |
|---|---|---|
| leaf check `mcheckP` | 27.1 | 21.8 (the 6 extra terms) |
| splits | 25.2 | 25.5 |
| FBBT | 20.0 | 20.0 |
| base incl. tables | 14.1 (tables 6.6; 3.5 without the lookup) | 6.9 |
| leaf decoder `mleafP` | 7.8 | 5.9 |
| walk + leaf step | 4.8 | 4.7 |
| multipliers | 3.2 | 3.0 |

Full-run tables (about 2.8k entries) estimate:
- `HC`/`HS` ≈ 11.5 KB;
- the lookup ≤ 5.4 KB at K = 5, ≤ 2.7 KB at K = 4.

**Kernel cost.** Measured on 60 of AMT8's minorant leaves (`bp_pcellh8.py`, `PCellH8B`), same payloads, Huffman tables
built from AMT8's 473 M leaves at LB = 10. The run was at load ≈ 8, so read the ratios.

| leaf | ms | ratio |
|---|---|---|
| fixed-width kind-aware `mleafP` | 10.22 | 1.00 |
| AMT8 `mleafN` | 12.05 | 1.18 |
| Huffman, loop only | 12.60 | 1.23 |
| Huffman + 5-bit lookup | 10.96 | **1.07** |

- Payload bits per leaf on these leaves: 157.8 fixed-width, 84.1 Huffman.
- On the golden walk, 91 % of the term codes are ≤ 4 bits and 94 % are ≤ 5 bits.
- Per node, on AMT8's 32 walks (`bp_pcellhw8.py`, `PCellHW8B`; NR = 2, mask 0, box leaves), extra over AMT8's own walk:
  - 6-bit split: +0.110 ms;
  - Huffman split, loop: +0.240 ms;
  - Huffman split with the lookup: **+0.122 ms**.

**Limits the encoder must respect.**
- Code length ≤ 32.
- Fewer than 2^16 codes of one length, and symbols < 2^16.
- At most 42 multiplier entries in a list.

## T1 and Z (TZ.md; built 2026-10-03)

Generator `amg/genpcell4.py` (Huffman walk, T1 in place of FBBT, Z in the leaf). Generic files:
`PCellTZ.lean` (13.3 KB), `PCellZ.lean` (27.2 KB), `PCellLeafZ.lean` (11.2 KB), `PCellT1.lean` (3.6 KB). Standard axioms
throughout.

**T1, generic.** The 28 pair intervals are slots of the cell: gap `r` is slot `r`, pair `k` is slot `Q + k`.
- `slot_ok`: every point lies in every slot.
- `setLo_ok` / `setHi_ok`: writing any valid bound keeps every point.
- `triC`: TZ.md's six clipped updates, in order. `tri_gen` shows a triple keeps every point and leaves its slots nonempty
  on a point. Nat truncation is handled by `natsub_lo` / `natsub_hi`, since sums are ≥ 0.
- `matC` / `mat_gen`: the step-2 intervals written into A, B.
- Any sequence of steps is sound, by composition.

**T1, kernel.** `tm` writes the 21 pair intervals into A, B. Then `tr0 … tr55` apply the triples in TZ.md's i, j, k
order, each one unrolled on the curried state. Then `te` runs one emptiness test on all 28 slots (`gempG`, `pempG`).
- Testing emptiness once at the end gives TZ.md's verdict: lower bounds only rise and upper bounds only fall, so a slot
  that is ever empty stays empty.
- Per-triple tests cost +0.7 ms per node.
- Sum splits cut at the raw midpoint `(A + B) >> 1` (`cov_rmid`). The mask `M` is kept in the state but unused (NR = 0).

**Z.**
- `line_le_ends`: a line is maximised at an endpoint.
- `pieces_cover`: some nondegenerate piece holds each point.
- `zpiece_right` / `zpiece_left`, `zside_right` / `zside_left`: the integer piece check `zpt` at both ends, with the
  slope claims M (right) and P (left).
- `tangent_valZ`: `tcheckPZ` (the derivative read, else n pieces of `lb top bk`) gives the tangent's value form
  `v + w'(p)(s − p) ≤ w(s)` on [L, U].
- `mterm_minV` / `mterm_okZ` give the anchored term.
- `mcheckGZ_sound` is the leaf with `mokTZ`.

**Checks.**
- Q = 3 (`PCell3T`, `PCell3TI`, `PCell3TRI`):
  - `root_box`, `childB_leaf` and `cert` re-proved;
  - `t1_empty`: T1 empties the LP-infeasible toy cell, and the walk reads no bit;
  - `farkas_cell` via `fleaf`.
- Q = 7 `PCellT7Z` (B440000, golden Huffman tables, LUT 4) compiles in 39 s.
- `PCellTZG` (`amg/tzgold_lean.py`):
  - all 10 golden T1 nodes give exactly the logged 56-field state after T1;
  - all 5 golden Z checks give their verdicts (3 pass, 2 fail), through the kernel's `zpe`/`zpt` with the logged reads.

**Bytes.** `PCellT7Z` is 118.9 KB; its T1 section is 39.5 KB, against 20.0 KB for FBBT.

**Kernel cost.**
- Per node, on AMT8's 32 walks (`PCellHW8B` with `PCellT7B`, `bp_pcellhw8.py`), T1 costs **+4.77 ms** over AMT8's own
  walk. For comparison, FBBT NR = 2 with no active pair costs +0.17 ms; at the measured A ≈ 13, NR = 1, about 2.7 ms.
- Breakdown (variants `PCellT7BP` / `BE` / `BL`):
  - the 56 continuation calls ≈ 0.9 ms;
  - the intervals ≈ 0.5 ms;
  - the triple arithmetic ≈ 3.4 ms. That is ≈ 60 µs per triple, for 18 primitive operations at the kernel's per-operation
    floor. Writing the step with `let` instead of `forceR` changes nothing.
- Leaf, with Z inside `mokTZ`: 1.08× the fixed-width leaf (60 AMT8 M leaves). Z is free while the derivative read
  passes.
- Not measured: the cost of a Z side (at most 8 pyramid reads). It needs the window's tables under its root.

**Open with mvt-engine.** The leaf's anchor needs L0_t = Σ l_r ≤ L_t. T1's loop order can leave A_t below Σ l_r.
- Proposed fix: a T1 step 5 that re-clips each pair by the box sums.
- The kernel's leaf already reads `[max(A, Σl), min(B, Σu)]`, which is right under either choice.

## The n = 8 try2r certificate PC8 (built 2026-10-03)

The certificate is built in rootR8 from mvt-engine's `bench/eight/am8/DATA_try2r_0.0002.json`, the only valid input
(T1 with the step-5 re-clip).

Settings and figures:
- fixed-width fields: `[κ 2][j1 7][j2 7][λ 8]`, with weight m = 4λ out of 1024;
- multipliers `[1][c 5][side][Yq 12]`;
- T1 with step 5, Z8;
- cN 805003, 26 active terms;
- 32 roots, 1,364,765 walk bits.

**T1 step 5.** The re-clip by the box sums is `matC` again, so `mat_gen` proves it. The kernel runs `tm` a second time
after the 56 triples, then the single final emptiness test.

**Golden vectors** (`tz_golden.json`, regenerated): `PCellTZG` checks all 18:
- the 10 t1_nodes;
- the 3 reclip_nodes, where step 5 binds;
- the 5 Z checks.

**Modules** (rootR8/AMW; the generic `PCell*` files are copied there from rootR8f):
- `PC8Inst` (113.6 KB, 37 s): `amg/genpcell4.py` in DATA mode, i.e. fixed width, the point function `pb` with `PTF pb`,
  and `SA`, `G`, `Fg_G` for the assembler.
- `PC8Data` (755 KB, 404 s), from `amg/make8pc.py`:
  - walks 342 KB;
  - w pyramid 43 KB;
  - derivative pair table 84 KB;
  - **sparse point table** 93 KB: a dispatch on `x >> 10` to per-block `ptl` lists, checked by `ptlOk`. The
    block-packed `PT3B` would be 1.4 MB, because PLO points have arbitrary offsets.
  - `cert` via the generic root cover;
  - `PC8_cert_full`, completed by reflection (`PC8_half`, `PC8_G_rev`).
- Axioms: standard (`PC8Ax`).
- `BrProf` (the band profile with the BrTau import) and the credits file `bpprof/CSRC_PC8.txt` go to am-cert.

**Dry run** of am-cert's assembler: 1.71 MB before safecut, m = 148, Φ = 0.6734812767 ≥ κ = 6734812/10⁷.

**Z cost** on the R8 tables (`PC8ZB`): about 2.5 ms per Z side. There are 40 distinct sides in the certificate, so about
0.1 s in total.

## PC8 performance (2026-10-03 evening)

The profile (variants of root walks 4 and 20, rootR8) showed where the time went. Z cost 36–44 % of a walk: it runs 6–9
times per minorant leaf, at 8 pyramid reads each. T1 cost 17 %, derivative reads 15 %, the rest of the leaf 17 % and
decoding 12 %. The point table was negligible: all 2,262 lookups take 0.39 s. A 2048-bit leaf window saved almost
nothing.

- **Z fast path.** `zsideF` in PCellZ tries 1 piece, then 2, then the sizer's 8. Each alternative is proved sound on
  its own (`zsideF_right` / `zsideF_left`), and tz.py is unchanged. Root walks got 22 % faster.
- **Chunked walks** (make8pc.py, env CH; PC8 uses CH=150). A subtree of at most CH leaves is one walk theorem
  (`covered_of_walkP`). Above that, a node is a boundary: `t1_to` (T1 into the equality continuation `kEq`, shown by
  `decide +kernel`), then `gsplit_to` / `ssplit_to` (the children are field updates of the named T1 state, checked by
  rfl). The sequential-build peak fell from 4.59 to 2.78 GB; bytes rose by about 0.9 KB per boundary.
- **Pipeline rerun PC8b:**
  - kernel replay 409 → 323 s;
  - nanoda 422 s / 8.92 GB → 334 s / 4.92 GB;
  - build 650 s / 7.16 GB → 568 s / 4.85 GB.
- **Typh's engine (rootR8f, PC8F{Inst,Data}).** Roots 4 and 20 ran 13–15 % faster in the same session. Credits go in
  `bpprof/CSRC_PC8F.txt`.
- **Closure.** mvt-engine owns it (PCellClose, genpcellC.py, make8pcC.py): 2.12 ms per node, against 7.57 ms for T1.
  The final build is meant to be closure + CH=150 + the Z fast path, in rootR8f.

## Not done

- The structure-passing walk (held by the lead).
- The n = 8 tables from the chosen window under its matching root (held). Only then can the minorant leaves of the golden
  walk be checked for real.

## Q = 8 port (nine-point rung, 2026-10-07)

**Generators** (new files; the Q = 7 ones are unchanged):
- `amg/genpcellQ.py` is mvt-engine's `genpcellC.py` (closure mode) made Q-generic.
  - DATA mode works for any Q; Q is read from `bN`.
  - The axis field is `bit_length(Q + NC − 1)`: 5 bits at Q = 7, 6 at Q = 8.
  - The short binder names were extended and Lean keywords removed (`at`, `by`, … broke the 73-field state).
- `amg/makepcQ.py` is `make8pcC.py` made Q-generic. It reads Q, NC, AXB, CB and the field widths from the data, and
  handles an empty point table. It accepts closure data only (TCLOSE=1).
- `amg/syn9data.py` writes a synthetic DATA json (env Q = 7 or 8). It has empty tables, one root, a random closure
  split tree (`tz.close`) and constant or reflected leaves.
- Not ported: the T1 path (`genpcell4.py` without CLOSE, and `make8pc.py`).

**Synthetic test** (rootR8f; PS9 is Q = 8, PS8 is its Q = 7 twin from the same generators and the same tree law):

| | PS9 (Q = 8) | PS8 (Q = 7) | ratio |
|---|---|---|---|
| tree | 304 splits, 287 constant + 18 reflected leaves | 303 splits, 228 + 76 | |
| Inst bytes | 310,281 | 198,010 | 1.57 |
| Inst build | 114.7 s, 1.78 GB | 72.5 s, 1.37 GB | 1.58 |
| Inst kernel type checking | 8.1 s | 4.3 s | 1.87 |
| Data bytes (CH=60) | 29,700 | 25,567 | |
| walk kernel time (CH=0, one walk theorem) | 4.98 s = 16.4 ms per split | 3.45 s = 11.4 ms per split | 1.44 |

- Axioms of `PS9_cert_full` and `PS9Data.cert`: `[propext, Classical.choice, Quot.sound]`.
- The 6-bit axis field is exercised: 34 splits are on axes 32–35.
- The per-split figure includes one constant leaf. Minorant-leaf cost needs real tables, so it is not measured.
- Inst bytes: the split functions are 72 % of PS9Inst. That is 28 `ssplit` × 6.2 KB plus 8 `gsplit` × 6.2 KB, with 57
  closure candidates per child.
- Inst elaboration: the 36 `*split*_ok` lemmas take 1.1–1.5 s of `exact` each, and one `exact` takes 14 s (6 s at
  Q = 7). In total that is 62.6 s against 32.8 s.

## One closure helper for every split (`HELP=1`, 2026-10-07)

**Idea.** Through the edge `s → t` of weight `w`, the closure bound of slot `(a, b)` is a path:
- `x_b − x_a ≤ D(a, s) + w + D(t, b)` (upper);
- `x_b − x_a ≥ −(D(b, s) + w + D(t, a))` (lower).

With the column `X_x = BB + D(x, s)` and the row `Y_x = BB + w + D(t, x)` (`BB = 2^42`, one field each or none), every
slot has the same update:
- `hi(a, b) := min(hi(a, b), X_a + Y_b − 2BB)`;
- `lo(a, b) := max(lo(a, b), 2BB − X_b − Y_a)`.

This is one helper, `cuH`. A split passes its 18 entries (Q = 8) and the unchanged state. The split's own slot comes out
as `q`.

**Why the states are unchanged.** Nothing is skipped. The candidates that `cupd` skips never bind on a closed cell.
Truncation in X and Y only loosens a bound. Every chunk boundary's `rfl` agrees with tz.close: 11 synthetic boundaries
at Q = 8, and 179 real ones on PC8C5's data.

**Lean.**
- Generic module `rootR8f/AMW/PCBias.lean`:
  - `cuB`, `ColOK`, `cuB_ok`;
  - `dE`, `colB`, `rowB`, `colB_ok`;
  - `cov_splitB`: a split at any `q` on `(i, j)`.
- Generated per Q:
  - `cuH`, `cuL`, `cuL_eq` (simp + rfl), `cuH_ok`, `spH_ok`;
  - one line per split: `fun s h => spH_ok hih i j (by decide) (by decide) (s := s) h`;
  - `gsplit_to` / `ssplit_to` on `cuB`.
- Flags: `HELP=1` with `CLOSE=1 LETC=1` in `amg/genpcellQ.py`. `makepcQ.py` is unchanged.
- Without HELP, genpcellQ still reproduces PC8C5Inst byte for byte, and `makepcQ CH=150` reproduces PC8C5Data apart
  from two docstring words.

| | PS9 → PS9H (Q = 8, synthetic) | PS8 → PS8H (Q = 7, synthetic) | PC8C5 data, Q = 7 → PQ7H |
|---|---|---|---|
| Inst bytes | 310,281 → 137,528 | 198,010 → 102,825 | 198,080 → 102,895 |
| Inst build | 114.7 → 41.5 s | 72.5 → 26.8 s | 50.6 → 33.1 s (same session) |
| walk kernel (unchunked; 2 runs each, same session) | 3.92 → 3.59 s (−8.5 %) | 2.38 → 2.10 s (−12 %) | |
| Data build (CH = 150 real; CH = 60 synthetic) | 25.4 → 18.0 s | 21.9 → 15.0 s | 233.6 → 199.8 s (−14.5 %) |
| Data kernel type checking | | | 161.9 → 145.4 s (−10 %) |
| axioms | standard | standard | standard |

Split `_ok` lemmas now take about 20 ms each to elaborate, down from 1.1–1.5 s. The largest elaboration item left in
the Inst is `ystep_ok`'s `exact`: 14 s at Q = 8, 6 s at Q = 7.

## Cache-shared reads (`DFAST`, 2026-10-07)

**What changed.** `lbDr` and `lb` now evaluate their cover's level `k`, last cell `ib` and first cell `g` with `forceR`
before calling `dcov2` / `dcov`. Two leaves whose reads cover the same cells then make the same call on numerals, and
the kernel's whnf cache shares the whole cover traversal for the rest of the declaration. Before, only the single
entries (`dstep2`'s packed `lh`) were shared.

**Soundness.** The values are unchanged:
- `lbDrF_eq`, `lbF_eq`;
- `treadUF_eq`, `treadDF_eq`, `zpcF_eq`, `tcheckPZG_eq`;
- `mokTZF_eq`, `mokTZG_eq`, `mvKF_eq`.

All of them are in `rootR8f/AMW/PCDF.lean`. The Inst's `mcheckP_ok` adds the `_eq` names to its simp list, and no
soundness proof changes.

**Flags** (amg/genpcellQ.py):
- `DFAST=1`: the derivative reads only.
- `DFAST=2`: the pyramid reads too, i.e. the Z pieces (`zsideFG`) and the constant-term values (`mvKF`).
- `DFAST=0` reproduces PC8C5UInst byte for byte.

**Kernel time**, roots 4 and 20 of PC8C5U with its tables (`/tmp/huffw/mkrb.py` bench, two runs each, same session):

| | root 4 | root 20 |
|---|---|---|
| PC8C5U | 8.50 / 8.25 s | 8.50 / 8.60 s |
| DFAST=1 | 7.47 / 7.78 s | 7.48 / 7.41 s |
| DFAST=2 | 6.40 / 6.45 s | 6.55 / 6.30 s |

**Profile of a DFAST=2 root walk**, by subtraction from unsound timing variants (`TCHKV=noz` / `nod` / `nochk`), on an
average root of 6.40 s:

| part | time | share |
|---|---|---|
| Z pieces | 1.47 s | 23 % |
| derivative reads and the rest of the tangent check | 1.07 s | 17 % |
| leaf check without tangents | 2.16 s | 34 % |
| walk, closure, forced L/U and decode positions | 1.70 s | 27 % |

**Coarse-first sides (`DFAST=3`, `rootR8f/AMW/PCDZ.lean`).**
- Before the exact alternatives, each tangent side is tried on its far end rounded out: `U` up and `L` down, to a
  multiple of `2^j` with `2^j` about `1/2^CSH` of the side (`rup`, `rdn`). The derivative read is tried there first,
  then the Z pieces. Neighbouring leaves share these checks.
- Soundness: `tangent_valZC` (each alternative on its own; a check on the longer side covers `[zb, U]`), `mterm_okZC`
  and `mtermTZC`.
- The leaf chain is restated once for any term check: `mcheckGX` and `mcheckGX_sound`.
- `CSH` tuning, average per root (roots 4 and 20, two runs): 3 → 5.49 s, 4 → 5.66 s, 5 → 5.71 s. The default is 3.

**Full PC8C5U certificate** (tables, 32 root walks, assembly; `lean -o`, same session):

| | build | peak | axioms |
|---|---|---|---|
| PC8C5U (copy) | 181.6 s | 3.16 GB | standard |
| DFAST=2 (PCF2) | 144.3 s (−20.6 %) | 2.85 GB | standard |
| DFAST=3, CSH=3 (PCF3) | 135.1 s (−25.6 %) | 2.75 GB | standard |

**Root walks 4 and 20** (two runs each, same session): DFAST=3 averages 5.54 s against 6.16 s for DFAST=2 and 8.46 s
for PC8C5U.

**For mvt-engine's generator** (BSPLIT): the same DFAST edits are in `amg/genpcellC_DFAST.patch`. With the patch
applied to a copy, DFAST=3 reproduces PCF3Inst and DFAST=0 reproduces PC8C5UInst, byte for byte.

## PQ7HB: boundary splits + HELP + DFAST=2 (max-margin backup, 2026-10-08)

**Inputs.**
- Data: mvt-engine's `DATA_try2cb_0.00005.json` (BSPLIT=1, BMARG 64, 32 boundaries; 4,566 splits, of which 2,260 are
  mode 1; 4,598 leaves).
- Inst: `BSPLIT=1 HELP=1 DFAST=2 CLOSE=1 LETC=1 amg/genpcellQ.py rootR8f PQ7HBInst 7`.
- Data file: mvt-engine's `make8pcC.py` (CH = 0, run read-only).

**Walk format.** mvt-engine's: a split is `[1][axis 5][mode 1]`, and the children start at pos + 7.

**How the cut composes.** A split's `q` is `Bool.rec (midpoint) (bcutL BND 64 lo hi) (Nat.beq md 1)`, with
`PCellCloseB.bcutL` imported read-only. `cov_splitB` holds at any `q`, so `spH_ok` takes the cut as it is and needs no
`qB` lemma. The golden cuts (8 from walk 0, plus 5 edge cases) all pass by `decide` (`PQ7HBG.lean`).

**Build** (`lean -o`, same session):

| | Inst bytes | Data bytes | Data build | instructions | peak |
|---|---|---|---|---|---|
| PC8C5U (copy) | 198,086 | 791,915 | 185.9 s | 1.41e12 | 3.16 GB |
| PC8C5B (copy) | 201,678 | 717,141 | 155.1 s | 1.17e12 | 3.16 GB |
| PQ7HB | 105,782 | 717,118 | 121.8 s | 0.98e12 | 2.74 GB |

PQ7HB's Data build is −34.5 % against PC8C5U and −21.5 % against PC8C5B. Its Inst builds in 26.1 s. The axioms of
`PQ7HB_cert_full` and `PQ7HBData.cert` are standard.

**PQ7HBF: BSPLIT + HELP + DFAST=3, CSH 3** (`rootR8f/AMW/PQ7HBF{Inst,Data,Ax}`; PQ7HB above is the DFAST=2 build).
Data builds, same session:

| | Inst bytes | Data build | instructions |
|---|---|---|---|
| PC8C5U | 198,086 | 182.1 s | 1.40e12 |
| PC8C5BF (mvt-engine) | ~201.8 KB | 117.0 s | 0.96e12 |
| PQ7HBF | 105,856 | 114.6 s (−37.0 % vs PC8C5U, −2.1 % vs PC8C5BF) | 0.94e12 |

The axioms are standard. On an unchunked certificate HELP is worth about 2 % of the Data build. The −14.5 % measured
on PQ7H came mostly from its 179 chunk boundaries, whose `rfl` checks are much cheaper on `cuB`. What HELP does keep
on every certificate is −96 KB of Inst and a faster Inst build (36.8 s against 48 s).
