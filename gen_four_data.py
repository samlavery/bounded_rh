#!/usr/bin/env python3
"""Emit the four-point certificate as checker DATA (cells, cover, trees) for checker.lean,
using the lab's exact-rational branch-and-bound (four_point_gen.certificate)."""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/zeta-lab/hunts/ainta_seven_point"))
import four_point_gen as F4
import three_point_gen as G

CN = int(sys.argv[1]) if len(sys.argv) > 1 else 2310
P = int(sys.argv[2]) if len(sys.argv) > 2 else 2500

F4.extend_anchors(12)
res = F4.certificate(CN, P)
assert res is not None
c, S, level = res['c'], res['S'], res['level']
clear, bad, boxes = res['clear'], res['bad'], res['boxes']
ivals = F4.collect_intervals(res)
idx = {iv: i for i, iv in enumerate(ivals)}
cells = {iv: G.build_cell(*iv) for iv in ivals}
assert all(v is not None and v.W > 0 for v in cells.values())

def Q(q):
    q = Fr(q)
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator}/{q.denominator}"

# ---- cells ----
cell_lines = []
for iv in ivals:
    cl = cells[iv]
    k = int(2 * cl.a); assert Fr(k, 2) == cl.a
    side = "true" if cl.side > 0 else "false"
    cell_lines.append(f"⟨{Q(cl.l)}, {Q(cl.u)}, {k}, {side}, {Q(cl.W)}⟩")

# ---- cover ----
segs = sorted([(l, u, 'clear') for (l, u) in clear] + [(l, u, 'bad') for (l, u) in bad])
pos = G.X0
cover_lines = []
for s in segs:
    assert s[0] == pos, ("gap", pos, s)
    pos = s[1]
    if s[2] == 'clear':
        ci = idx[(s[0], s[1])]
        assert cells[(s[0], s[1])].W >= level
        cover_lines.append(f"({Q(s[0])}, {Q(s[1])}, [{ci}])")
    else:
        cover_lines.append(f"({Q(s[0])}, {Q(s[1])}, [])")
assert pos == S
nb = len(bad)
bad_sorted = [s for s in segs if s[2] == 'bad']
assert [(l, u) for (l, u, _) in bad_sorted] == sorted(bad)
bad = sorted(bad)

# ---- trees ----
def chain(lo, hi, W):
    if W == 0: return "[]"
    pcs = G.quarter_pieces(lo, hi)
    ids = [idx[pc] for pc in pcs]
    assert min(cells[pc].W for pc in pcs) == W
    return "[" + ", ".join(str(i) for i in ids) + "]"

def mirror(node):
    if node[0] == 'leaf':
        box, Ws = node[1], node[2]
        return ('leaf', (box[2], box[1], box[0]), [Ws[2], Ws[1], Ws[0], Ws[4], Ws[3], Ws[5]])
    _, box, k, m, a, b = node
    return ('split', (box[2], box[1], box[0]), 2 - k, m, mirror(a), mirror(b))

def emit_tree(node):
    if node[0] == 'leaf':
        box, Ws = node[1], node[2]
        terms = []
        for (coef, idxs), W in zip(F4.COEFFS, Ws):
            lo = sum(box[i][0] for i in idxs); hi = sum(box[i][1] for i in idxs)
            terms.append(chain(lo, hi, W))
        return ".leaf " + " ".join(terms)
    _, box, k, m, a, b = node
    return f".split {k} ({Q(m)}) ({emit_tree(a)}) ({emit_tree(b)})"

seen = dict(boxes)   # key -> node
tree_texts = []
nleaf = 0
for i in range(nb):
    for j in range(nb):
        for k in range(nb):
            t = (i, j, k)
            if bad[i][0] + bad[j][0] + bad[k][0] >= S:
                tree_texts.append(".leaf [] [] [] [] [] []"); continue
            key = min(t, tuple(reversed(t)))
            node = seen[key]
            if key != t: node = mirror(node)
            assert node[1] == (bad[i], bad[j], bad[k]), (node[1], t)
            nleaf += F4.nleaves(node)
            tree_texts.append(emit_tree(node))

# ---- Lean ----
def chunks(xs, n): return [xs[i:i+n] for i in range(0, len(xs), n)]
out = []
A = out.append
A("\n/-! ###### four-point certificate data: c = %d/10^6, p = %d ###### -/\n" % (CN, P))
A("namespace Zeta23Ext.Bridge.ThreePoint.FourData\n")
A("set_option maxRecDepth 100000\n")
cc = chunks(cell_lines, 150)
for n, ch in enumerate(cc):
    A(f"def cells{n} : List Cell := [\n  " + ",\n  ".join(ch) + "]\n")
A("def cells : List Cell := " + " ++ ".join(f"cells{n}" for n in range(len(cc))) + "\n")
A("def cover : List (ℚ × ℚ × List ℕ) := [\n  " + ",\n  ".join(cover_lines) + "]\n")
tc = chunks(tree_texts, 8)
for n, ch in enumerate(tc):
    A(f"def trees{n} : List Tree := [\n  " + ",\n  ".join(ch) + "]\n")
A("def trees : List Tree := " + " ++ ".join(f"trees{n}" for n in range(len(tc))) + "\n")
A(f"def cQ : ℚ := {CN}/1000000\ndef pQ : ℚ := {P}\ndef SQ : ℚ := {Q(S)}\n")
A("theorem cells_ok : cells.all Cell.ok = true := by decide +kernel\n")
A("theorem cover_ok : coverCheck cells (3/2 * cQ) (1/2) SQ cover = true := by decide +kernel\n")
A("theorem trees_ok : treesCheck cells cQ pQ (badOf cover) trees = true := by decide +kernel\n")
A("theorem SQ_eq : SQ = cQ * pQ := by decide +kernel\n")
A("\nend Zeta23Ext.Bridge.ThreePoint.FourData\n")
open("data4.lean", "w", encoding="utf-8").write("\n".join(out))
print(f"cells={len(ivals)} cover_segments={len(cover_lines)} bad={nb} trees={len(tree_texts)} leaves={nleaf} bytes={os.path.getsize('data4.lean')}")
