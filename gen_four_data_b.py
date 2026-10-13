#!/usr/bin/env python3
"""Emit the five-point certificate as checker5 data with CHUNKED kernel checks:
table split into subtrees, every bisection tree cut into subtrees of <= CH leaves (composed
through `walk5_split`), one theorem per piece."""
import sys, os, pickle, itertools
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/zeta-lab/hunts/ainta_seven_point"))
import three_point_gen as G, four_point_gen as G4
G4.extend_anchors(12)
F5 = G4   # the four-point generator plays the role of F5 below

CN, P = 2310, 2500
CH = int(sys.argv[1]) if len(sys.argv) > 1 else 600     # max leaves per kernel check
TABD = int(sys.argv[2]) if len(sys.argv) > 2 else 4     # table split depth (2^TABD subtrees)
FUEL0 = 64

res = G4.certificate(CN, P); assert res is not None
c, S, level = res['c'], res['S'], res['level']
clear, bad = res['clear'], sorted(res['bad'])
nb = len(bad)

# ---- trees for all tuples ----
nodes = {}
for t in itertools.product(range(nb), repeat=3):
    box = tuple(bad[i] for i in t)
    if sum(b[0] for b in box) >= S:
        nodes[t] = ('leaf', box, [Fr(0)] * len(F5.COEFFS)); continue
    node = F5.subdivide(box, c, S, P); assert node is not None, t
    nodes[t] = node

# ---- cells ----
ivals = set(clear)
def walk(node):
    if node[0] == 'leaf':
        box, Ws = node[1], node[2]
        for (coef, idxs), W in zip(F5.COEFFS, Ws):
            if W == 0: continue
            lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
            for pc in G.quarter_pieces(lo, hi): ivals.add(pc)
    else:
        walk(node[4]); walk(node[5])
for node in nodes.values(): walk(node)
ivals = sorted(ivals)
cells = {iv: G.build_cell(*iv) for iv in ivals}
assert all(v is not None and v.W > 0 for v in cells.values())

def Q(q):
    q = Fr(q); return f"{q.numerator}" if q.denominator == 1 else f"({q.numerator}/{q.denominator})"
def cell_text(iv):
    cl = cells[iv]; k = int(2 * cl.a); assert Fr(k, 2) == cl.a
    return f"⟨{Q(cl.l)}, {Q(cl.u)}, {k}, {'true' if cl.side > 0 else 'false'}, {Q(cl.W)}⟩"
def box_text(box):
    return "⟨" + ", ".join(Q(v) for b in box for v in b) + "⟩"

out = []; A = out.append
A(f"\n/-! ###### four-point certificate data (bit-walk): c = {CN}/10^6, p = {P} ###### -/\n")
A("namespace Zeta23Ext.Bridge.ThreePoint.FourDataB\n")
A("set_option maxRecDepth 100000\n")

# ---- table: balanced BST, subtrees at depth TABD are separate defs ----
subs = []
def bst(lo, hi, depth):
    if lo >= hi: return "CT.nil"
    if depth == TABD:
        name = f"tab{len(subs)}"
        subs.append((name, lo, hi))
        return name
    m = (lo + hi) // 2
    return f"(CT.node {bst(lo, m, depth + 1)} {cell_text(ivals[m])} {bst(m + 1, hi, depth + 1)})"
def bst_full(lo, hi):
    if lo >= hi: return "CT.nil"
    m = (lo + hi) // 2
    return f"(CT.node {bst_full(lo, m)} {cell_text(ivals[m])} {bst_full(m + 1, hi)})"
top = bst(0, len(ivals), 0)
for name, lo, hi in subs:
    A(f"def {name} : CT :=\n  {bst_full(lo, hi)}\n")
A(f"def table : CT :=\n  {top}\n")
for name, _, _ in subs:
    A(f"theorem {name}_ok : {name}.allOk = true := by decide +kernel\n")
A("theorem table_ok : table.allOk = true := by\n  simp only [table, CT.allOk, " + ", ".join(f"{n}_ok" for n, _, _ in subs)
  + ", Bool.true_and, Bool.and_true]\n  decide +kernel\n")

# ---- cover ----
segs = sorted([(l, u, True) for (l, u) in clear] + [(l, u, False) for (l, u) in bad])
pos = G.X0; cover_lines = []
for (l, u, cl) in segs:
    assert l == pos; pos = u
    if cl: assert cells[(l, u)].W >= level
    cover_lines.append(f"({Q(l)}, {Q(u)}, {'true' if cl else 'false'})")
assert pos == S
A("def cover : List (ℚ × ℚ × Bool) := [\n  " + ",\n  ".join(cover_lines) + "]\n")

# ---- bits + chunked walk theorems ----
bits = []
def emit_bits(node):
    if node[0] == 'leaf': bits.append(0)
    else: bits.append(1); emit_bits(node[4]); emit_bits(node[5])
starts = {}
for t in itertools.product(range(nb), repeat=3):
    starts[t] = len(bits); emit_bits(nodes[t])
NBITS = len(bits)
N = 0
for i, b in enumerate(bits):
    if b: N |= (1 << i)
A(f"def bits : ℕ := {N}\n")
A(f"def cQ : ℚ := {CN}/1000000\ndef pQ : ℚ := {P}\ndef SQ : ℚ := {Q(S)}\n")

def nleaves(n): return 1 if n[0] == 'leaf' else nleaves(n[4]) + nleaves(n[5])
def nnodes(n): return 1 if n[0] == 'leaf' else 1 + nnodes(n[4]) + nnodes(n[5])
thm = [0]
def mk(node, pos, depth):
    """Emit theorems proving walk4 table cQ pQ bits (FUEL0 - depth) pos box = some end; return (name, end)."""
    box = node[1]; fuel = FUEL0 - depth
    end = pos + nnodes(node)
    name = f"wk{thm[0]}"; thm[0] += 1
    if node[0] == 'leaf' or nleaves(node) <= CH:
        A(f"theorem {name} : walk4 table cQ pQ bits {fuel} {pos} {box_text(box)} = some {end} := by decide +kernel\n")
        return name, end
    k, m = node[2], node[3]
    boxA = list(box); boxA[k] = (box[k][0], m); boxB = list(box); boxB[k] = (m, box[k][1])
    nA, endA = mk(node[4], pos + 1, depth + 1)
    nB, endB = mk(node[5], endA, depth + 1)
    assert endB == end
    A(f"theorem {name} : walk4 table cQ pQ bits {fuel} {pos} {box_text(box)} = some {end} :=\n"
      f"  walk4_split table cQ pQ bits {fuel - 1} {pos} {box_text(box)} {endA} {end} (by decide +kernel)\n"
      f"    (by rw [show ({box_text(box)} : Box).setHi (Box.widthArg {box_text(box)}) (Box.mid {box_text(box)} (Box.widthArg {box_text(box)})) = {box_text(boxA)} from by decide +kernel]; exact {nA})\n"
      f"    (by rw [show ({box_text(box)} : Box).setLo (Box.widthArg {box_text(box)}) (Box.mid {box_text(box)} (Box.widthArg {box_text(box)})) = {box_text(boxB)} from by decide +kernel]; exact {nB})\n")
    return name, end

roots = []
for t in itertools.product(range(nb), repeat=3):
    name, end = mk(nodes[t], starts[t], 0)
    roots.append((t, name, starts[t], end, nodes[t][1]))
A(f"theorem nb_eq : (badOf5 cover).length = {nb} := by decide +kernel\n")
for (t, name, st, end, box) in roots:
    i, j, k = t
    A(f"theorem root_{i}{j}{k} : walk4 table cQ pQ bits {FUEL0} {st} (boxOf4 (badOf5 cover) {i} {j} {k}) = some {end} := by\n"
      f"  rw [show boxOf4 (badOf5 cover) {i} {j} {k} = {box_text(box)} from by decide +kernel]; exact {name}\n")
cases = []
for (i, j, k), _, _, _, _ in roots:
    cases.append(f"  | {i}, {j}, {k}, _, _, _ => exact ⟨_, _, root_{i}{j}{k}⟩")
cases.append(f"  | i + {nb}, _, _, hi, _, _ => exact absurd hi (by omega)")
cases.append(f"  | _, j + {nb}, _, _, hj, _ => exact absurd hj (by omega)")
cases.append(f"  | _, _, k + {nb}, _, _, hk => exact absurd hk (by omega)")
A(f"""theorem run_ok : ∀ i j k, i < (badOf5 cover).length → j < (badOf5 cover).length →
    k < (badOf5 cover).length →
    ∃ pos pos', walk4 table cQ pQ bits {FUEL0} pos (boxOf4 (badOf5 cover) i j k) = some pos' := by
  intro i j k hi hj hk
  rw [nb_eq] at hi hj hk
  match i, j, k, hi, hj, hk with
""" + "\n".join(cases) + "\n")
A("theorem cover_ok : coverCheck5 table (3/2 * cQ) (1/2) SQ cover = true := by decide +kernel\n")
A("theorem SQ_eq : SQ = cQ * pQ := by decide +kernel\n")
A("\nend Zeta23Ext.Bridge.ThreePoint.FourDataB\n")
open("data4b.lean", "w", encoding="utf-8").write("\n".join(out))
print(f"cells={len(ivals)} subtrees={len(subs)} nb={nb} bits={NBITS} walk_theorems={thm[0]} bytes={os.path.getsize('data4b.lean')}")
