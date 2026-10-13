# Generic split: kernel cost and the continuation-form fix (mvt-engine, 2026-10-08)

Headroom for a later method. Nothing here is in a shipped certificate. The 10-08 edge candidates use the unrolled
k=6 instance (PCE6UPC) and the list-evaluated k=5 instance with the kind-aware leaf (PCE5KP).

## 1. What was measured

Kernel micro-benchmarks, run outside the Lean lock. Files:
- `/tmp/mvt_close/geni/SplitBench.lean`: `cupd` alone.
- `/tmp/mvt_close/geni/SplitBench2.lean`: generic against unrolled `splitAx`.
- `/tmp/mvt_close/geni/SplitBench3.lean`: the continuation-form prototype.

They import `AMW.PCE6HPCInst` (generic split, unrolled leaf) and `AMW.PCE6UPCInst` (unrolled split), both Q = 6.

Workload: 20 test cells × 21 split axes, midpoint cuts (md = 0). The continuation sums every field of each child plus
one, so both children are taken and nothing goes unevaluated. Times are the profiler's per-declaration
`type checking` times.

| what | kernel | per call |
|---|---|---|
| `cupd` (PCellClose), fields summed by a `List.rec` sum | 4.71 s / 420 | 11.2 ms |
| `cupdF` (same algorithm; `List.rec` getter `lgd`; `Bool.rec`/`Nat.blt` in place of `if`) | 2.87 s / 420 | 6.8 ms |
| generic `splitAx` (PCE6HPC) | 30.4 s / 420 | 72 ms |
| unrolled `splitAx` (PCE6UPC) | 0.58 s / 420 | 1.4 ms |
| prototype `splitAxF` (`cupdK` below, with `lgd` getters) | 7.35 s / 420 | 17.5 ms |

Each faster form was checked against the slower one with `Nat.beq … = true` by `decide +kernel`: `cupdF` against
`cupd`, and `splitAxF` against the unrolled split. Peak memory was 6.1 GB for the generic-split benchmark and 2.3 GB
for the prototype.

In real certificates (k=6, δ 3 %, 624 splits) the generic split costs about +294e9 Data instructions over the
unrolled split: hybrid PCE6HPC Data 450.6e9 against unrolled PCE6UPC Data 156.1e9. The unrolled instance instead pays
about +169e9 in elaboration (Inst 305e9 against 136e9) and +81 KB of bytes.

## 2. Where the generic split spends its time

1. Slot reads. `slT` is `List.getD` into the 49-entry slot table. `sLo`/`sHi` are `List.getD` into the cell lists
   behind `if s < Q`, and `sI`/`sJ` are `if` plus `PR.getD`. Each slot's new bound runs through `cLo`/`cHi`, which are
   two Option-valued 3-leg paths: 6 leg reads per side and 21 slots per side, per child. `List.getD`
   (`get?` + `Option.getD`) and `ite`/`Nat.decLt` are slow kernel paths. Swapping them for a `List.rec` read and
   `Bool.rec (Nat.blt …)` gives −39 % on `cupd`.
2. The conversion back. `U (ih pos) (ofCl (cupd …) M)` hands the child 43 unevaluated projections, each a
   `getD` into a `List.map … (List.range …)`. This is most of the 72 ms; the slot reads above are the rest.

Not the cause (checked): the root cover and the leaf. A forced CPS decode (`decK`, GENK) changed nothing; the kernel
already caches the decode. The leaf's cost was its kind-unaware term reads, fixed by `mcheckGXK` (PCellGK.lean).

## 3. The fix (prototype, no proofs yet)

Fast reads (each needs an equality lemma with the original):

```lean
def lgd {α : Type} (d : α) : List α → ℕ → α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d) (fun h _ ih n => Nat.rec (motive := fun _ => α) h (fun k _ => ih k) n)
-- lgd d l n = l.getD n d  (induction on l, cases on n)
def sLoF (Q : ℕ) (c : Cl) (s : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (lgd 0 c.A (Nat.sub s Q)) (lgd 0 c.L s) (Nat.blt s Q)
-- likewise sHiF, sIF, sJF, pIF, pJF, slTF; then legPF/legNF/pathPF/pathNF/cHiF/cLoF/nLoF/nHiF, one for one
```

The continuation-form update: each of the 2Q + 2·|PR| slots is computed once, forced, and handed to the child as a
literal. The generator writes the chain from Q and PR, in the ST argument order:

```lean
def cupdK (c : Cl) (s t M : ℕ) (k : ST) : ℕ :=
  forceR (nLoF 6 PR SL c 0 s t) fun l0 => forceR (nHiF 6 PR SL c 0 s t) fun u0 => …          -- gaps 0 … Q-1
  forceR (nLoF 6 PR SL c 6 s t) fun A02 => forceR (nHiF 6 PR SL c 6 s t) fun B02 => …         -- pairs, PR order
  k l0 u0 … l5 u5 A02 B02 … A46 B46 M
```

`splitCF` is `splitC` with `U (ih p) (ofCl (cupd 6 PR SL c' s t) M)` replaced by `cupdK c' s t M (ih p)`.

The lemma that keeps the proofs as they are:

```lean
theorem cupdK_eq (c : Cl) (s t M : ℕ) (k : ST) : cupdK c s t M k = U k (ofCl (cupd 6 PR SL c s t) M)
-- simp only [cupdK, forceR_eq, U, nLoF_eq, nHiF_eq]; then each field (ofCl (cupd …) M).x = nLo/nHi … by rfl
```

Then `splitAx_ok` rewrites with `cupdK_eq` and continues through `sp_ok` and `cov_gsplitQ`/`cov_ssplitQ` unchanged.
The generic part (`lgd`, the F-forms, the `_eq` lemmas) fits a new file next to PCellClose. `cupdK` itself is
instance-shaped: its arity is the state's.

Expected effect, scaled from the benchmark and not measured on a certificate: the generic split falls from 72 to
about 17.5 ms per split. For PCE6HPC that is about 463e9 → 240–280e9 net, roughly −160 to −190 board-s at 0.86 s per
1e9. For PCE5KP it is about −30e9. Bytes do not change.

## 4. What is still left after the fix

The prototype is still 12.6× the unrolled split. What remains is the Option-path evaluation (6 legs per side per slot)
and the list reads of the parent cell. Two further steps, not tried:
- Per-axis candidate tables, emitted as data: for each split edge (s, t), only the live (slot, leg) triples. This is
  what the unrolled form hard-codes; it drops the Option layer and the run-time slot lookups.
- A packed-Nat cell: every bound in one `Nat`, read with `shiftRight`/`land`, which the kernel's GMP path does in one
  step. This means new cell-representation lemmas throughout the split proofs, so it is the larger job.

## 5. Calibration used

0.86 board-s per 1e9 NET instructions (am-cert, E4 against ET), on a 2,319 s base. NET means Inst + Data instructions
minus twice the import load of the Ax module (about 54e9).
