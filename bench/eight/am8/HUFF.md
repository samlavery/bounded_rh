# HUFF — walk encoding for the pair-cell (polytope) eight-point certificate

Reference encoder and round-trip decoder: `huffenc.py` (this directory). Golden data: `huff_tables_g15.json`,
`huff_golden_g15.json` (R8 B440000, δ 0.1 %, root 15, LS = 256). The Lean decoder must reproduce `huffenc.py` bit
for bit. Every field below is exact; where a choice is arbitrary, it is fixed here.

## 1. Bits

- The walk of one root is a natural number `W`. **Bit k of the walk is `(W >> k) & 1`.** Bits are written in
  increasing k. A walk is stored as one hex literal per chunk, as now.
- A **fixed-width field** of n bits at position p has value `Σ_{b<n} bit(p+b)·2^b`, least significant bit first.
- A **Huffman codeword** of length l at position p is read MSB first: the first bit read (position p) is the most
  significant bit of the code integer. See §3.

## 2. Node grammar, depth first per root

Every node first runs the kernel's tightening (Jacobi, NR rounds, constraints in PAIRS order; bridge-port's PCELL
spec).

- **Empty** (tightening finds Le > Ue or l_r > u_r): the node reads **no bits**.
- **Split:** `[1][axis codeword]` (§4), then child A, then child B.
  - Gap axis r: A has u_r := m, B has l_r := m, with m = (l_r + u_r) >> 1.
  - Sum axis: A has Ub := m, B has Lb := m, with m = (Le + Ue) >> 1 on the tightened cell's effective range.
- **Leaf:** `[0]`, then:
  - if `u_{Q-1} < l_0` (reflected): **nothing more**;
  - else `[kind: 1 bit]`: 0 = minorant leaf (§5), 1 = Farkas leaf (§6).
  - Zero-order cells are minorant leaves with every term constant. There is no separate Z kind.

## 3. Canonical Huffman tables

A table is a list of `(symbol, length)` pairs **sorted by (length, symbol)**. The symbol is a natural number.

- **Codes:** the first entry gets code 0. Each next entry gets `code := (code + 1) << (len − prev_len)`.
- **One-entry table:** the length is 0, and decoding reads **no bits** and returns the symbol.
- **Decoding**, reading bits b1, b2, … from position p:

  ```
  code := 0; first := 0
  for ln in 1, 2, …, maxlen:
      code := (code << 1) | next_bit
      cnt  := number of entries of length ln
      if code − first < cnt: return the (code − first)-th entry of length ln (in table order)
      first := (first + cnt) << 1
  ```

  This is `get_code` in huffenc.py. Lengths are at most 32 in practice.

## 4. Split axis

Axis value a: 0..6 = gap a; 7..27 = the sum constraint of rank a − 7.

- **Rank order:** the non-adjacent pairs (i, j) with j − i ≥ 2, in PAIRS order. PAIRS is i < j, i ascending, then j
  ascending:
  `(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5),(2,6),(2,7),(3,5),(3,6),(3,7),(4,6),(4,7),(5,7)`.
- The codeword comes from `axis_table`, one table per certificate.

## 5. Minorant leaf payload

1. **Term fields.** For every active term t (aN_t > 0), in PAIRS order:
   - read a codeword from `term_tables[t]`, giving the symbol `s = κ·2^14 + j1·2^7 + j2`;
   - if κ = 2, read λ as an LB-bit field;
   - if κ = 3, read λ − 1 as an (LB − 1)-bit field.

   Here LB = log2 LS (LS = 256, so LB = 8). The meaning of the fields:

   | κ | minorant | weights (out of LS) |
   |---|---|---|
   | 0 | constant `lb(L, max(U, L+1))` on the effective range [L, U] | LS on the constant |
   | 1 | tangent at `gpt(L, U, j1)` | LS on the tangent |
   | 2 | constant + tangent at `gpt(L, U, j1)` | LS − λ on the constant, λ on the tangent; 1 ≤ λ ≤ LS − 1 |
   | 3 | tangents at `gpt(L, U, j1)` and `gpt(L, U, j2)` | LS − λ on j1, λ on j2; 1 ≤ λ ≤ LS/2, the heavier tangent first |

   - j1 and j2 are 7-bit position values (JSH = 5): bits 0..5 give the position j ∈ 0..32; bit 6 selects the fine
     2^GSH grid (GSH = 5), clear means the 256 grid.
   - **The value 33 (bit 6 clear) is PLO, p = L.**
   - gpt is exactly as follows (all integers; None means the leaf fails):

     ```
     def gpt(L, U, jj, JSH=5, GS=5):
         if jj == (1 << JSH) + 1: return L
         gs = GS if (jj >> (JSH + 1)) & 1 else 8
         j = jj & ((1 << (JSH + 1)) - 1); gm = (1 << gs) - 1
         ga = ((L + gm) >> gs) << gs; gb = (U >> gs) << gs
         x = ((L + (((U - L) * j) >> JSH)) >> gs) << gs
         r = ga if x <= ga else (gb if gb <= x else x)
         return r if ga <= gb else (r if L <= r <= U else None)
     ```

   - tchk on [L, U] at p is as MinCore, plus the one-point case: L = U = p with P, M ≥ 1.
   - [L, U] is the term's effective range on the tightened cell. The expansion point is L0 = Σ_{r∈t} l_r.
2. **Multiplier list.** Entries `[1][c codeword][side: 1 bit][Yq: YB bits]`, closed by `[0]`.
   - c comes from `c_table` and is the rank of the constraint (§4 order).
   - side 0 = the Lb constraint, side 1 = Ub.
   - YB = 12, and Y = SIG·Yq with SIG = (1024·U1·SA) >> 14.
   - The encoder writes entries sorted by (c, side), and no (c, side) twice.

## 6. Farkas leaf payload

Only the multiplier list, as in §5.2, with **YB = 4** (Yq ∈ 1..15). The test is homogeneous in Y, so SIG plays no
role. huffenc.py finds the multipliers by LP and certifies them with the integer test

```
Σ const·Yq + Σ_r (u_r − l_r)·max(0, Σ_{side 0} Yq − Σ_{side 1} Yq) < 0
```

with const = L0 − Lb (side 0) or Ub − L0 (side 1), on the tightened cell. All 6,040 Farkas cells of the full B440000
run certify with Yq ≤ 15.

## 7. Tables in the certificate (huff_tables_*.json)

```
term_tables : "i,j" -> [[symbol, length], …]   (canonical order; symbol = κ·16384 + j1·128 + j2)
axis_table  : [[axis, length], …]
c_table     : [[rank, length], …]
```

These go into the instance as data: one `List (ℕ × ℕ)` per table.

## 8. Golden vectors (huff_golden_g15.json)

- `walk_hex` is the whole root-15 walk, 21,280 bits.
- `nodes` lists the first 20 nodes in depth-first order. Each gives its path (A/B from the root), type, cell before
  tightening (box and constraints), and its own bits as a '0'/'1' string in write order.
- Splits also give the axis value. Leaves give the decoded terms (κ, j1, j2, λ) and multipliers.
- The node bit strings concatenated in order are the prefix of the walk.

## 9. Measured sizes, R8 B440000 δ 0.1 %, current rules

| run | minorant leaf | Farkas leaf | split | walk |
|---|---|---|---|---|
| full run (41,531 leaves), LS 1024 | 167.4 bits: term codes 91.6, λ 43.2, multipliers ≈ 31, kind 2 | 25.5 bits | ≈ 5.5 bits | ≈ 6.06 Mbit ≈ 1.51 MB hex |
| roots 4 + 17, LS 256 | (λ fields 8/7 bits; +0.8 % leaves) | | | |
| root 15 (in-sample tables) | 106.4 bits | 21.6 bits | 5.46 bits | |
