# TZ — the T1 tightening and the Z extension (kernel semantics for the pair-cell eight-point certificate)

`tz.py` in this directory **is** the reference. Its two functions `t1` and `zext` are the code form of this document. The
sizer (`size8pz.py`, env `TRIPLE=1 PERSIST=1 NR=0 ZEXT=8`) and the replay verifier (`emit8pz.py`) both call them.

Golden vectors are in `tz_golden.json`: 10 nodes with their cell before and after T1, and 5 Z checks with every piece.

Units:
- gaps and pair sums in 1/SC, SC = 32768;
- w values in 1/U, U = 10¹⁰;
- slope claims in 1/U1, U1 = 10⁹; KU1 = 2·10⁹; RU = U/U1 = 10.

All arithmetic is on integers. Every intermediate value used below is ≥ 0 (see §1.4).

## 1. T1, the node tightening

### 1.1 When

T1 runs at every node, before anything else: the empty test, the reflection test, the leaf or the split. There is **no
other tightening**: NR = 0, so there is no Jacobi FBBT and no mask. T1 subsumes FBBT, because a gap is the pair
(r, r+1).

### 1.2 State

The node state holds:
- the gap bounds l_r, u_r, r = 0..6;
- the bounds A_t, B_t of the 21 non-adjacent pairs t = (i, j), j − i ≥ 2.

At the root, every A_t, B_t is absent; in the kernel, use A_t = 0 and B_t = ∞, or equivalently the box sums. After the
root's first T1, all of them are present (persisted, §1.3).

### 1.3 The pass

1. **Gap check.** If any l_r > u_r, the cell is empty.
2. **Intervals for all 28 pairs, in pair order** (i ascending, then j ascending):
   - lo = Σ_{r=i}^{j−1} l_r and hi = Σ_{r=i}^{j−1} u_r;
   - for a non-adjacent pair, lo := max(lo, A_t) and hi := min(hi, B_t);
   - if lo > hi, the cell is **empty**.
3. **The triples.** For i = 0..7, for j = i+2..7, for k = i+1..j−1 (56 triples, in this nested order), with
   a = I(i, k), b = I(k, j), c = I(i, j), execute in this order, each line using the values just written:

   ```
   c.lo := max(c.lo, a.lo + b.lo);   c.hi := min(c.hi, a.hi + b.hi)
   a.lo := max(a.lo, c.lo − b.hi);   a.hi := min(a.hi, c.hi − b.lo)
   b.lo := max(b.lo, c.lo − a.hi);   b.hi := min(b.hi, c.hi − a.lo)
   ```

   Then, if a.lo > a.hi, or b.lo > b.hi, or c.lo > c.hi, the cell is **empty**.
4. **Write back the gaps.** l_r := I(r, r+1).lo and u_r := I(r, r+1).hi.
5. **Re-clip** (added 2026-10-03 after bridge-port found the L0 ≤ L gap). For every non-adjacent pair t = (i, j), in pair order:
   - lo := max(lo, Σ_{r=i}^{j−1} l_r) and hi := min(hi, Σ_{r=i}^{j−1} u_r), on the gaps written back in step 4;
   - if lo > hi, the cell is **empty**.

   Then every non-adjacent pair is persisted: A_t := I(t).lo and B_t := I(t).hi. The children inherit them.

   Why: a gap raised by a later triple can lift Σ l above the lower end of an interval settled earlier, and can lower
   Σ u in the same way. Without step 5, the leaf's anchor L0_t = Σ l_r can exceed L_t = A_t, but the charges assume
   L0_t ≤ L_t. In the first emitted certificate (now void), 653 of 11,322 nodes had such an interval; 410 of them were
   minorant leaves. After step 5, Σ l_r ≤ A_t ≤ B_t ≤ Σ u_r holds for every t at every node. That makes every anchored
   difference a Nat: p − L0_t (tangent charges), A_t − L0_t (side-0 multipliers) and B_t − L0_t (side-1 multipliers).

### 1.4 Nat subtraction

In Nat, `c.hi − b.lo` truncates at 0 where Python goes negative. That happens only when c.hi < b.lo. Since c.lo ≥ a.lo +
b.lo ≥ b.lo, it then holds that c.lo > c.hi, so c is empty and the verdict is the same. The lower updates use
`c.lo − b.hi` inside a max with a.lo ≥ 0, so truncation does not change them either. (bridge-port's argument, confirmed.)

### 1.5 Uses of the written-back state

- **Split, gap r:** m = (l_r + u_r) >> 1. Child A gets u_r := m; child B gets l_r := m.
- **Split, sum t:** m = (A_t + B_t) >> 1. Child A gets B_t := m; child B gets A_t := m.
- **Reflection test:** u_6 < l_0.
- **Leaf:**
  - the effective range of term t is I(t): A_t, B_t for a non-adjacent pair, (l_r, u_r) for an adjacent one;
  - the charges are anchored at L0_t = Σ_{r∈t} l_r on the written-back gaps;
  - multiplier entries refer to A_t (side 0) and B_t (side 1).

## 2. Z, the zero-order extension of a tangent

### 2.1 When

Inside the leaf's tangent check (`tcheck`), for every tangent with nonzero weight. On [L, U] = the term's effective range,
take the point p, the convex region [za, zb] of p (REG, k = (p + 16384) >> 15), and the point triple at p:
v = lo32, P, M.
- **Right side**, when U > zb. It passes if the derivative read passes: e = lo32(lbDr(zb, U)), with e ≥ 1 and
  e + M ≥ 4·U1. Otherwise it passes iff **Z(a = zb, b = U, right)** passes.
- **Left side**, when L < za. It passes if e = hi32(lbDr(L, za)) has e ≥ 1 and e + P ≥ 4·U1. Otherwise it passes iff
  **Z(a = L, b = za, left)** passes.
- The rest of tcheck is unchanged: region membership, p ∈ [L, U], P, M ≥ 1, the one-point case L = U = p, and PLO.
- **No walk bits:** the kernel tries the derivative read first and Z only when that fails.

### 2.2 Z(a, b, side), with n = ZEXT = 8 fixed per certificate

For k = 0..n−1:
- x0 = a + ((b − a)·k) // n and x1 = a + ((b − a)·(k + 1)) // n;
- if x1 ≤ x0, the piece passes;
- otherwise read lo = **lb top bk x0 x1**, the w pyramid's single read (not lb3, not the derivative table);
- with s = KU1 − M on the right side, or s = P − KU1 on the left side, require **both**:

  ```
  v·SC + RU·s·(x0 − p) ≤ SC·lo
  v·SC + RU·s·(x1 − p) ≤ SC·lo
  ```

  These are integer (ℤ) expressions: x − p is ≥ 0 on the right and ≤ 0 on the left, and s may be negative.

Z passes iff every piece passes.

### 2.3 Soundness

On a piece, the tangent through (p, v) with true slope d ∈ [(P−KU1)/U1, (KU1−M)/U1] is ≤ v + max_d d·(x − p). That is the
worst slope s/U1, since x − p has a fixed sign on each side. It is linear in x, so its maximum over [x0, x1] is at an end.
The read gives w ≥ lo/U on [x0, x1], and the tangent through (p, w(p)) lies above the one through (p, v), since v ≤ w(p).
Inside [za, zb] the tangent is below w by convexity, as before.

### 2.4 The bug this fixes

The first sizer version took `max(x0 − p, x1 − p)` inside the right-side product. When M > KU1 the slope is negative, so
the maximum is at x0, not x1. Now both ends are checked on both sides. The sizing used for the certificate was re-run
with the fix.

## 3. Golden vectors (tz_golden.json)

- **`t1_nodes`.** The first 10 nodes of root 0's walk (R8 try2, δ 0.02 %), in depth-first order. They are 10 splits: 8 on
  sums, 2 on gaps. Each gives:
  - `before`: the incoming gaps and the persisted pair bounds;
  - `after`: the gaps and all 28 pair intervals after T1, checked against the sizer's dump;
  - the split taken and its midpoint.
- **`reclip_nodes`.** The first 3 nodes of the walk (roots in order, depth first) where step 5 changes an interval or
  empties the cell. Each gives `root_index`, `path`, `before`, `after_step4` (the intervals as they stand after steps 1–4),
  `after` (after step 5, or `empty`), and `reclipped`, the pairs that step 5 changed.
- **`z_checks`.** Five checks; each piece gives x0, x1, the pyramid read, lhs (the larger end value), rhs = SC·lb, and the
  verdict.
  - Three are logged from the certificate's final verification: two left-side, one right-side, all PASS.
  - One is the first of those with v raised just past its smallest slack: FAIL.
  - One is a right-side check with M = 0 (the largest slope claim): FAIL.
  - The table reads are part of the inputs, so the vectors test the arithmetic without the tables.

## 4. The certificate this supports (R8 try2, δ 0.02 %, cN 805003)

| item | value |
|---|---|
| leaves | 5,676 (minorant 5,409, reflected 267; no Farkas, no empty) |
| splits | 5,644, of which 4,061 on sums |
| nodes | 11,320 |
| points | 2,262 |
| tables | w 1,984 finest cells (WMIN 8), derivative 2,240 (DLO/DHI 7/8) |
| walk | 1,364,765 bits = 341.2 KB hex, fixed-width |

These figures are for the certificate re-sized with step 5 (2026-10-03).

Files:
- `DATA_try2r_0.0002.json`, from `emit8pz.py` on the dump `pzfr_try2_0.0002.pkl`: the dump replayed with kernel
  semantics, the built tables re-verified, and every walk round-tripped. **This is the only valid input.** Its Z log
  is `DATA_try2r_0.0002_zlog.json`.
- `verify8pz.py`: an independent replay from DATA.json alone. It ends every walk exactly at its bit count with
  **0 failures**.
  - It also asserts L0_t ≤ L_t at every weighted leaf term and L0_t ≤ A_t at every multiplier entry. Both hold with 0
    exceptions.
  - Controls: cN + 2000 gives 523 failures; flipping walk bit 7 gives 30; flipping bit 0 desynchronises the walk.
  - The anchor assertion has a positive control: `ctl_anchor.py` replays with T1 minus step 5. On the void first
    emission it reports 70 anchor failures.
- **Void:** everything emitted or sized under the pre-step-5 semantics is renamed with the suffix `.VOID_L0GAP`, so no
  script can pick it up by its old name. That covers `DATA_try2_0.0002.VOID_L0GAP.json` (with its zlog) and the dumps
  `pzfz_try2_p1_0.0002`, `pzfy_try2_{0.0002,0.0005,0.001}`. `tz_golden_v1_noreclip.json` is kept for the record. Do
  not build from any of them.

## 5. FALLBACK (2026-10-03, not adopted for this build): the exact closure in place of T1

Status: sized, emitted and verified, and kept as the fallback.

**Lead's decision (2026-10-03).** This build keeps T1 + step 5 (§1) with `DATA_try2r_0.0002.json`, the only valid
input:
- T1's ≈ 54 s of replay keeps the board projection inside budget (≈ 1,800–2,100 s conservative);
- bridge-port's T1 kernel already matches the golden vectors;
- switching would delay the upload by a kernel rewrite and a re-verification.

**Switch triggers.** Switch to the closure only if either:
1. the measured private-check projection of the T1 file exceeds ≈ 2,600 s conservative; or
2. the next rung (n = 9) needs the time margin.

Until a trigger fires, do not build from `DATA_try2c_0.0002.json`.

### 5.1 Why

- **Cost.** T1 costs the kernel +4.77 ms per node (bridge-port's measurement), about 54 s of replay for this
  certificate. The closure costs 56 bound candidates per child, each two additions and one min or max. By operation
  count (not measured in the kernel) that is roughly a quarter of T1's arithmetic, with no step 5, no emptiness test,
  and no box sums recomputed at each node.
- **Strength.** The closure is the tightest any propagation can reach, so it is never looser than T1.
- **No order to specify.** The closure is unique.

### 5.2 The object

A cell is a system of difference constraints on the prefix sums x_0 = 0, x_k = g_0 + … + g_{k−1}. A pair (i, j) bounds
x_j − x_i; a gap is the pair (r, r+1). The state is the 28 intervals [lo(i, j), hi(i, j)].

The state is **closed** when every interval is the exact range of x_j − x_i over the cell. This is the all-pairs
shortest-path closure of the constraint graph.

### 5.3 The kernel's form

- **Root.** lo(i, j) = Σ l_r and hi(i, j) = Σ u_r over the root box. A box is already closed. Use these values and
  **not** 0 / 2^40: the split update reads the parent's bounds, so the root has to be closed for the kernel to match
  the sizer.
- **Split** on the pair (p, q), p < q (a gap is q = p+1), with m = (lo(p, q) + hi(p, q)) >> 1. Define
  D(a, b) = hi(a, b) if a < b, 0 if a = b, and −lo(b, a) if a > b, all taken from the parent.
  - Child A (hi(p, q) := m, a new edge p → q of weight m), for every pair (i, j):
    `hi' = min(hi, D(i,p) + m + D(q,j))` and `lo' = max(lo, −(D(j,p) + m + D(q,i)))`.
  - Child B (lo(p, q) := m, a new edge q → p of weight −m):
    `hi' = min(hi, D(i,q) − m + D(p,j))` and `lo' = max(lo, −(D(j,q) − m + D(p,i)))`.
- **Node.** No tightening at all. The node reads its state as stored. The reflection test and the leaf are as in
  §1.5, with A_t, B_t = lo, hi of the pair and (l_r, u_r) = the gap pairs.

### 5.4 Soundness

Soundness does not need closedness. Each candidate is a path bound: for example,
x_j − x_i = (x_p − x_i) + (x_q − x_p) + (x_j − x_q) ≤ D(i,p) + m + D(q,j) in child A. So every stored bound is valid
whenever the parent's bounds are valid.

Nat arithmetic works out as follows:
- hi candidate: compute (positive terms) − (negative terms). Truncation can only raise the bound, which keeps it valid.
  It does not happen here anyway: candidate ≥ hi' ≥ lo' ≥ 0.
- lo candidate: compute (negative terms) − (positive terms), truncated at 0, then take the max with lo ≥ 0. The result
  is exact, and it is valid because x_j − x_i ≥ 0.

Closedness is what makes the kernel's incremental result equal the closure from scratch. One new edge enters a
shortest path at most once, and the new cycle has weight m − lo(p, q) ≥ 0 or hi(p, q) − m ≥ 0, so a child is never
empty. Closedness also gives Σ l_r ≤ lo(t) for every t, so L0 ≤ L holds without a re-clip.

### 5.5 Files

- `tz.close` computes the closure from scratch (Floyd–Warshall on 8 nodes; the sizer and verifier use it).
  `tz.close_split` is the kernel's incremental form above.
- Random test: 16,464 splits, incremental equal to from-scratch on every one. On every state T1 kept non-empty, the
  closure is non-empty and at least as tight; it was strictly tighter on 222 of 294 closed states.
- The certificate is `DATA_try2c_0.0002.json` (sizer env `TCLOSE=1`, dump `pzfc_try2_0.0002.pkl`), δ 0.02 %,
  cN 805003, so κ is unchanged.
  - 5,651 leaves (5,398 minorant, 253 reflected), against 5,676 under T1.
  - 5,619 splits (4,025 on sums); 11,270 nodes; 2,196 points.
  - Walk 1,361,398 bits = 340.3 KB hex.
- `verify8pz.py` on it: 0 failures and 0 anchor exceptions. At each of the 11,238 non-root nodes, `close_split` of the
  parent equals `close` of the child.
- Golden vectors: `tz_golden_close.json`, from `tzclose_gold.py`. It holds the root of walk 0 and its first 12 splits
  (2 on gaps, 10 on sums), each with the parent, both children and the changed pairs.

### 5.6 The Lean kernel (built 2026-10-03, after the lead triggered the fallback)

**The 13 skipped candidates.** The kernel computes 43 of the 56 candidates per child. With s → t the new edge, it keeps
hi(a, b) when b = s or a = t, and lo(a, b) when a = s or b = t (`tz.close_split(…, skip=True)`).
- On a closed cell those candidates never bind: d[a][s] + w + d[t][s] ≥ d[a][s] because w + d[t][s] ≥ 0, and likewise
  at a = t.
- They are the only candidates that read the split slot other than through the edge weight.
- `verify8pz.py` checks the skip form against all 56 candidates and against `tz.close` at all 11,238 nodes.

**Generic layer:** `rootR8/AMW/PCellClose.lean`.
- `cupd Q PR SL c s t` updates all 28 slots of the cell c at once, after the split's bound is set. Each candidate is
  the path a → s → t → b. Its legs are `legP` (hi of a forward pair) and `legN` (lo of a backward pair), read through
  the instance's slot table `SL` (`SLok`, by decide). The positive and negative sums are `oadd`, and the candidate is
  `csub` (Nat subtraction).
- `cupd_ok` says every point of c stays in `cupd c`, with no closedness assumption.
- The splits are `cov_gmidC` (gap r: child A is edge r → r+1, child B is edge r+1 → r) and `cov_rmidC` (pair k: child A
  is pI → pJ, child B is pJ → pI).
- Axioms are [propext, Classical.choice, Quot.sound] throughout (`AMW/PC8CAx.lean`).

**Instance:** `genpcellC.py` (a copy of bridge-port's genpcell4.py) with `CLOSE=1 LETC=1`.
- Each split computes the midpoint and both children's candidates as `let`s, then calls the walk on child A, then on
  child B.
- The link is `simp only [U, split] at h; exact sp_ok … (cov_gmidC …)`. It holds definitionally, because `let`
  zeta-reduces.
- `walk bits fuel := fun pos => tm (walkC bits fuel pos)`: `tm` closes the root box once, and `walkC` does no node
  tightening.
- Chunk boundaries use `gsplit_to` / `ssplit_to`, whose children are `cupd` by `rfl`, and `tm_to` for a chunked root.
  The data generator is `make8pcC.py`.

**Checks:**
- `AMW/PCellCloseG.lean` (`tzclose_lean.py`): all 12 golden splits under `decide +kernel`. Both children's 56 fields
  equal the sizer's.
- `AMW/PCellCloseBT.lean`: a root boundary (`tm_to`, then `ssplit_to`) and two inner boundaries, on real states.

**Bytes:** `PC8CLInst` (DATA_try2c) is 198.0 KB against `PC8Inst` 118.2 KB. The split and tightening section is 140.4 KB
against 61.9 KB. The olean is 13.2 MB against 14.8 MB.
- A `forceR` version also compiles, but its links, `simp … forceR_eq` over 87 nested binders, make a 48 MB olean.

**Cost:** the certificate's 32 walks through decode-only instances (every minorant check replaced by `true`, so a node
costs its decode plus its split work), as cumulative kernel type-checking time in one compile session.

| variant | nodes | kernel time | per node |
|---|---|---|---|
| T1 + step 5 (DATA_try2r) | 11,320 | 85.7 s | 7.57 ms |
| closure, `forceR` (DATA_try2c) | 11,270 | 27.2 s | 2.41 ms |
| closure, `let` (DATA_try2c) | 11,270 | 23.9 s | 2.12 ms |

**End to end:** `AMW.Cert.PC8CL_cert_full` is in rootR8 (`PC8CLInst` and `PC8CLData`; `make8pcC.py`, CH = 0, 766 KB) with
axioms [propext, Classical.choice, Quot.sound] (`AMW/PC8CLAx.lean`). Its statement is PC8's: cN 805003, so κ is
unchanged.
- The data module compiles in 251.8 s wall (`-DElab.async=false`, 2 threads), peak footprint 3.5 GB.
- Not measured: the private-check projection (export, nanoda, replayx).
