#!/usr/bin/env python3
"""Emit natural-number checker data for a weighted n-point certificate (Q = n-1 gaps).
Inputs: Q, weights (pairs a_ij as Fractions with denominator SA, b_r with denominator SA, c with denominator SA),
the certificate structures from gen_w.size (per-gap covers).  Scales: SC = 2^56, SW = 10^13.
Writes data_<NAME>.lean with namespace Zeta23Ext.Bridge.ThreePoint.<NAME>Data, plus the walk theorems."""
import sys, os, itertools
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/zeta-lab/hunts/ainta_seven_point"))
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
import three_point_gen as G, four_point_gen as G4
G4.extend_anchors(24)
import gen_w
SC = 2**96; SW = 10**13; SC4 = 2**94

def nat_scaled(q, scale):
    v = Fr(q) * scale
    assert v.denominator == 1, (q, scale)
    return int(v)

def emit(Q, pairs, A, Bv, c, SA, NAME, CH=250, TABD=5, FUEL0=64, out=None):
    n = Q + 1
    aN = [nat_scaled(A[pq], SA) for pq in pairs]; bN = [nat_scaled(b, SA) for b in Bv]; cN = nat_scaled(c, SA)
    ok, nleaves, covers = gen_w.size(Q, pairs, A, Bv, c, verbose=True)
    assert ok
    terms = [(A[(i, j)], tuple(range(i, j))) for (i, j) in pairs]
    bads = [cv[2] for cv in covers]
    # trees for all tuples (by the generator's rule)
    def lower(box):
        tot = sum(Bv[r] * box[r][0] for r in range(Q))
        for coef, idxs in terms:
            if coef == 0: continue
            lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
            tot += coef * gen_w.Wmulti(lo, hi)
        return tot
    def subdivide(box, depth=0):
        if gen_w.half_skip(box, Q): return ('leaf', box)
        if sum(Bv[r] * box[r][0] for r in range(Q)) >= c: return ('leaf', box)
        if lower(box) >= c: return ('leaf', box)
        assert depth <= 80
        k = gen_w.choose_axis(box, lower, c, Q); m = (box[k][0]+box[k][1])/2
        a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
        return ('split', box, k, m, subdivide(tuple(a), depth+1), subdivide(tuple(b2), depth+1))
    nodes = {}
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        nodes[tup] = ('leaf', box) if sum(Bv[r] * box[r][0] for r in range(Q)) >= c else subdivide(box)
    # cells referenced
    ivals = set()
    for cv in covers: ivals.update(cv[1])
    def walkn(node):
        if node[0] == 'leaf':
            box = node[1]
            if gen_w.half_skip(box, Q): return
            for coef, idxs in terms:
                if coef == 0: continue
                lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
                if gen_w.Wmulti(lo, hi) == 0: continue
                for pc in gen_w.pieces_far(lo, hi): ivals.add(pc)
        else:
            walkn(node[4]); walkn(node[5])
    for nd in nodes.values(): walkn(nd)
    ivals = sorted(ivals)
    cells = {iv: G.build_cell(*iv) for iv in ivals}
    assert all(v is not None and v.W > 0 for v in cells.values())
    def cell_text(iv):
        cl = cells[iv]; k = int(2 * cl.a); assert Fr(k, 2) == cl.a
        return f"⟨{nat_scaled(cl.l, SC)}, {nat_scaled(cl.u, SC)}, {k}, {'true' if cl.side > 0 else 'false'}, {nat_scaled(cl.W, SW)}⟩"
    def box_text(box):
        return f"({NAME}.Box.mk " + " ".join(f"{nat_scaled(b[0], SC)} {nat_scaled(b[1], SC)}" for b in box) + ")"
    L = []; W = L.append
    NS = f"Zeta23Ext.Bridge.ThreePoint.{NAME}"
    W(f"\n/-! ###### certificate data `{NAME}`: {len(ivals)} cells, {nleaves} leaves (axis-coded walk){' (half-space)' if gen_w.HALF else ''} ###### -/\n")
    W(f"namespace {NS}Data\n\nopen Zeta23Ext.Bridge.ThreePoint {NS}\n\nset_option maxRecDepth 100000\n")
    subs = []
    def bst(lo, hi, depth):
        if lo >= hi: return "CTN.nil"
        if depth == TABD:
            name = f"tab{len(subs)}"; subs.append((name, lo, hi)); return name
        m = (lo + hi) // 2
        return f"(CTN.node {bst(lo, m, depth + 1)} {cell_text(ivals[m])} {bst(m + 1, hi, depth + 1)})"
    def bst_full(lo, hi):
        if lo >= hi: return "CTN.nil"
        m = (lo + hi) // 2
        return f"(CTN.node {bst_full(lo, m)} {cell_text(ivals[m])} {bst_full(m + 1, hi)})"
    top = bst(0, len(ivals), 0)
    for name, lo, hi in subs:
        W(f"noncomputable def {name} : CTN :=\n  {bst_full(lo, hi)}\n")
    W(f"noncomputable def table : CTN :=\n  {top}\n")
    for name, _, _ in subs:
        W(f"theorem {name}_ok : {name}.allOk = true := by decide +kernel\n")
    W("theorem table_ok : table.allOk = true := by\n  simp only [table, CTN.allOk, " + ", ".join(f"{nm}_ok" for nm, _, _ in subs) + ", Bool.true_and, Bool.and_true]\n  decide +kernel\n")
    # covers
    S_scaled = []
    for r in range(Q):
        level, clear, bad = covers[r]
        segs = sorted([(l, u, True) for (l, u) in clear] + [(l, u, False) for (l, u) in bad])
        pos = G.X0; lines = []
        for (l, u, cl) in segs:
            assert l == pos; pos = u
            lines.append(f"({nat_scaled(l, SC)}, {nat_scaled(u, SC)}, {'true' if cl else 'false'})")
        Sr = Fr(-(-(4 * c) // Bv[r]), 4); assert pos == Sr, (pos, Sr)
        Sn = nat_scaled(Sr, SC); assert cN * SC <= bN[r] * Sn
        S_scaled.append(Sn)
        W(f"def cover{r} : List (ℕ × ℕ × Bool) := [\n  " + ",\n  ".join(lines) + "]\n")
        W(f"theorem cover{r}_ok : {NAME}.coverCheck table {aN[pairs.index((r, r+1))]} (SC / 2) {Sn} cover{r} = true := by decide +kernel\n")
    # bits + walk theorems
    bits = []
    def emit_bits(node):
        if node[0] == 'leaf': bits.append(0)
        else:
            bits.append(1); bits.extend([(node[2] >> i) & 1 for i in range(3)]); emit_bits(node[4]); emit_bits(node[5])
    starts = {}
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        starts[tup] = len(bits); emit_bits(nodes[tup])
    N = 0
    for i, b in enumerate(bits):
        if b: N |= (1 << i)
    W(f"def bits : ℕ := {N}\n")
    def nleaf(nd): return 1 if nd[0] == 'leaf' else nleaf(nd[4]) + nleaf(nd[5])
    def nnode(nd): return 1 if nd[0] == 'leaf' else 4 + nnode(nd[4]) + nnode(nd[5])
    thm = [0]
    def mk(node, pos, depth):
        box = node[1]; fuel = FUEL0 - depth; end = pos + nnode(node)
        name = f"wk{thm[0]}"; thm[0] += 1
        if node[0] == 'leaf' or nleaf(node) <= CH:
            W(f"theorem {name} : {NAME}.walk table bits {fuel} {pos} {box_text(box)} = some {end} := by decide +kernel\n")
            return name, end
        k, m = node[2], node[3]
        boxA = list(box); boxA[k] = (box[k][0], m); boxB = list(box); boxB[k] = (m, box[k][1])
        nA, endA = mk(node[4], pos + 4, depth + 1); nB, endB = mk(node[5], endA, depth + 1)
        assert endB == end
        bt = box_text(box)
        W(f"theorem {name} : {NAME}.walk table bits {fuel} {pos} {bt} = some {end} :=\n"
          f"  {NAME}.walk_split table bits {fuel - 1} {pos} {bt} {endA} {end} (by decide +kernel)\n"
          f"    (by rw [show ({bt} : {NAME}.Box).setHi ({NAME}.axOf bits {pos}) ({NAME}.Box.mid {bt} ({NAME}.axOf bits {pos})) = {box_text(boxA)} from by decide +kernel]; exact {nA})\n"
          f"    (by rw [show ({bt} : {NAME}.Box).setLo ({NAME}.axOf bits {pos}) ({NAME}.Box.mid {bt} ({NAME}.axOf bits {pos})) = {box_text(boxB)} from by decide +kernel]; exact {nB})\n")
        return name, end
    roots = []
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        name, end = mk(nodes[tup], starts[tup], 0)
        roots.append((tup, name, starts[tup], end, nodes[tup][1]))
    for r in range(Q):
        W(f"theorem nb{r}_eq : ({NAME}.badOf cover{r}).length = {len(bads[r])} := by decide +kernel\n")
    covs = " ".join(f"({NAME}.badOf cover{r})" for r in range(Q))
    for (tup, name, st, end, box) in roots:
        idx = "".join(str(i) for i in tup); args = " ".join(str(i) for i in tup)
        W(f"theorem root_{idx} : {NAME}.walk table bits {FUEL0} {st} ({NAME}.boxOf {covs} {args}) = some {end} := by\n"
          f"  rw [show {NAME}.boxOf {covs} {args} = {box_text(box)} from by decide +kernel]; exact {name}\n")
    cases = []
    for (tup, name, st, end, box) in roots:
        idx = "".join(str(i) for i in tup)
        cases.append(f"  | {', '.join(str(i) for i in tup)}, {', '.join('_' for _ in range(Q))} => exact ⟨_, _, root_{idx}⟩")
    for r in range(Q):
        pat = ", ".join((f"i + {len(bads[r])}" if k == r else "_") for k in range(Q))
        hp = ", ".join(("hi" if k == r else "_") for k in range(Q))
        cases.append(f"  | {pat}, {hp} => exact absurd hi (by omega)")
    ivars = " ".join(f"i{r}" for r in range(Q)); hvars = " ".join(f"hi{r}" for r in range(Q))
    W(f"theorem run_ok : ∀ {ivars}, {' → '.join(f'i{r} < ({NAME}.badOf cover{r}).length' for r in range(Q))} →\n"
      f"    ∃ pos pos', {NAME}.walk table bits {FUEL0} pos ({NAME}.boxOf {covs} {ivars}) = some pos' := by\n"
      f"  intro {ivars} {hvars}\n" + "".join(f"  rw [nb{r}_eq] at hi{r}\n" for r in range(Q)) +
      f"  match {', '.join(f'i{r}' for r in range(Q))}, {', '.join(f'hi{r}' for r in range(Q))} with\n" + "\n".join(cases) + "\n")
    W(f"theorem cert : ∀ {' '.join(f'g{r}' for r in range(Q))} : ℝ, {' → '.join(f'0 ≤ g{r}' for r in range(Q))} → ({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(f'g{r}' for r in range(Q))} :=\n"
      f"  {NAME}.of_check table table_ok bits {FUEL0} {' '.join(f'cover{r}' for r in range(Q))} {' '.join(str(s) for s in S_scaled)}\n"
      f"    {' '.join('(by decide +kernel)' for _ in range(Q))} {' '.join(f'cover{r}_ok' for r in range(Q))} (by decide +kernel) run_ok\n")
    W(f"\nend {NS}Data\n")
    text = "\n".join(L)
    open(out or f"data_{NAME}.lean", "w", encoding="utf-8").write(text)
    print(f"[{NAME}] cells={len(ivals)} leaves={nleaves} bits={len(bits)} walk_thms={thm[0]} bytes={len(text.encode())}")
    return dict(aN=aN, bN=bN, cN=cN, S=S_scaled)

if __name__ == "__main__":
    # four-point fixed-coefficient test instance: SA = 6*10^8
    Q = 3; SA = 600000000
    pairs = [(i, j) for i in range(Q+1) for j in range(i+1, Q+1)]
    A = {(i, j): Fr(2, 4 - (j - i)) for (i, j) in pairs}
    Bv = [Fr(1, 2500)] * Q
    c = Fr(2310, 10**6)
    emit(Q, pairs, A, Bv, c, SA, "FourN")
