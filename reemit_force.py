#!/usr/bin/env python3
"""Re-emit an existing certificate data file (data_<NAME>.lean, produced by gen_data_N.emit) without re-running
the sizing: rebuild the bisection tree from `bits` + the covers, then write the same structures with
  * coordinates at scale 2^SCE instead of 2^96 (every coordinate is divided by 2^(96-SCE); must be exact),
  * walk chunks of up to CH leaves,
  * optionally cells as ⟨LN, UN, WN⟩ (NOKSIDE=1; anchor index and side are then derived by the checker).
Usage: reemit_force.py NAME SCE CH OUTNAME   (reads data_NAME.lean + NAME_params.txt; writes data_OUTNAME.lean + OUTNAME_params.txt)
FORCE variant (copy of reemit.py): leaf-level walk theorems are proved as
`(OUT.walkF_eq table bits fuel pos box).symm.trans (by decide +kernel)`, i.e. the kernel evaluates the call-by-value
checker `walkF` emitted by gen_checkerN_force.py; the statements (about `walk`) are unchanged."""
import re, sys, os, itertools
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
NAME, SCE, CH, OUT = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
NOKSIDE = os.environ.get("NOKSIDE") == "1"
params = open(f"{NAME}_params.txt").read().split()
Q, SA = int(params[0]), int(params[1]); aN = [int(x) for x in params[2].split(",")]; bN = [int(x) for x in params[3].split(",")]; cN = int(params[4])
SCE_IN = int(params[6]) if len(params) > 6 else 96
assert SCE <= SCE_IN; DIV = 1 << (SCE_IN - SCE)
def sc(v):
    assert v % DIV == 0, v
    return v // DIV
s = open(f"data_{NAME}.lean", encoding="utf-8").read()
n = Q + 1; pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
cells = {}
for mm in re.finditer(r"⟨([0-9a-z,\s]+?)⟩", s):
    f = [x for x in mm.group(1).replace(" ", "").split(",") if x != ""]
    if not f or not f[0].isdigit(): continue
    if len(f) == 2: key, WN = int(f[0]), int(f[1]); LN, UN = key // 1048576, key % 1048576
    elif len(f) == 3: LN, UN, WN = int(f[0]), int(f[1]), int(f[2])
    elif len(f) == 5: LN, UN, WN = int(f[0]), int(f[1]), int(f[4])
    else: continue
    SCin = 1 << SCE_IN; k = (2 * (LN + UN) + SCin) // (2 * SCin); side = k * SCin <= 2 * LN
    cells[(LN, UN)] = (k, side, WN)
ivals = sorted(cells)
m = re.search(r"/-! ###### certificate data `\w+`: (\d+) cells, (\d+) leaves( \(axis-coded walk\))?( \(half-space\))? ###### -/", s)
AXISIN = bool(m and m.group(3)); HALFIN = bool(m and m.group(4))
assert m and int(m.group(1)) == len(ivals), (m and m.group(1), len(ivals))
bits = int(re.search(r"def bits : ℕ := (\d+)", s).group(1))
covers = []; S_in = []
for r in range(Q):
    body = re.search(rf"def cover{r} : List \(ℕ × ℕ × Bool\) := \[(.*?)\]", s, re.S).group(1)
    covers.append([(int(a), int(b), c == "true") for a, b, c in re.findall(r"\((\d+), (\d+), (true|false)\)", body)])
    S_in.append(int(re.search(rf"theorem cover{r}_ok : \w+\.coverCheck (?:table )?\d+ \(SC / 2\) (\d+) cover{r}", s).group(1)))
FUEL0 = int(re.search(r"theorem root_\d+ : \w+\.walk (?:table )?bits (\d+) ", s).group(1))
bads = [[(a, b) for a, b, cl in cv if not cl] for cv in covers]
def widthArg(box):
    ws = [u - l for l, u in box]
    for r in range(Q - 1):
        if all(ws[t] <= ws[r] for t in range(r + 1, Q)): return r
    return Q - 1
def build(pos, box):
    if (bits >> pos) & 1:
        k = ((bits >> (pos + 1)) & 7) if AXISIN else widthArg(box); mid = (box[k][0] + box[k][1]) // 2
        a = list(box); a[k] = (box[k][0], mid); b2 = list(box); b2[k] = (mid, box[k][1])
        A, pos = build(pos + (4 if AXISIN else 1), tuple(a)); B, pos = build(pos, tuple(b2))
        return ('split', box, k, mid, A, B), pos
    return ('leaf', box), pos + 1
nodes = {}; starts = {}; pos = 0
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    box = tuple(bads[r][tup[r]] for r in range(Q)); starts[tup] = pos
    nodes[tup], pos = build(pos, box)
nleaves = int(m.group(2))
def nleaf(nd): return 1 if nd[0] == 'leaf' else nleaf(nd[4]) + nleaf(nd[5])
def nnode(nd): return 1 if nd[0] == 'leaf' else 4 + nnode(nd[4]) + nnode(nd[5])
bitsout = []
def emit_bits(nd):
    if nd[0] == 'leaf': bitsout.append(0)
    else:
        bitsout.append(1); bitsout.extend([(nd[2] >> i) & 1 for i in range(3)]); emit_bits(nd[4]); emit_bits(nd[5])
starts2 = {}
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    starts2[tup] = len(bitsout); emit_bits(nodes[tup])
starts = starts2
bits_new = 0
for i, b in enumerate(bitsout):
    if b: bits_new |= (1 << i)
assert sum(nleaf(nd) for nd in nodes.values()) == nleaves, (sum(nleaf(nd) for nd in nodes.values()), nleaves)
# ---- emit (mirror of gen_data_N.emit) ----
COMPACT = os.environ.get("COMPACT") == "1"
TABLELESS = os.environ.get("TABLELESS") == "1"   # no cell table: piece bounds computed in the kernel   # local notation N/E for the tree constructors, no spaces in cells
NODE, NIL = ("N", "E") if COMPACT else ("CTN.node", "CTN.nil")
KB = 1048576   # key = LN * KB + UN at the output scale (every coordinate must be below KB)
def cell_text(iv):
    k, side, WN = cells[iv]
    assert sc(iv[0]) < KB and sc(iv[1]) < KB, iv
    if NOKSIDE and COMPACT: return f"⟨{sc(iv[0]) * KB + sc(iv[1])},{WN}⟩"
    if NOKSIDE: return f"⟨{sc(iv[0]) * KB + sc(iv[1])}, {WN}⟩"
    return f"⟨{sc(iv[0])}, {sc(iv[1])}, {k}, {'true' if side else 'false'}, {WN}⟩"
def box_text(box): return f"({OUT}.Box.mk " + " ".join(f"{sc(l)} {sc(u)}" for l, u in box) + ")"
TABD = 5
L = []; W = L.append
NS = f"Zeta23Ext.Bridge.ThreePoint.{OUT}"
W(f"\n/-! ###### certificate data `{OUT}`: {len(ivals)} cells, {nleaves} leaves (axis-coded walk){' (half-space)' if HALFIN else ''} ###### -/\n")
W(f"namespace {NS}Data\n\nopen Zeta23Ext.Bridge.ThreePoint {NS}\n\nset_option maxRecDepth 100000\n" + ('local notation "N" => CTN.node\nlocal notation "E" => CTN.nil\n' if (COMPACT and not TABLELESS) else ""))
subs = []
def bst(lo, hi, depth):
    if lo >= hi: return NIL
    if depth == TABD:
        name = f"tab{len(subs)}"; subs.append((name, lo, hi)); return name
    mm = (lo + hi) // 2
    return f"({NODE} {bst(lo, mm, depth + 1)} {cell_text(ivals[mm])} {bst(mm + 1, hi, depth + 1)})"
def bst_full(lo, hi):
    if lo >= hi: return NIL
    mm = (lo + hi) // 2
    return f"({NODE} {bst_full(lo, mm)} {cell_text(ivals[mm])} {bst_full(mm + 1, hi)})"
top = bst(0, len(ivals), 0)
TB = "" if TABLELESS else "table "
assert not TABLELESS, "reemit_force.py: the forced checker needs the cell table"
if TABLELESS: subs.clear()
for name, lo, hi in subs: W(f"noncomputable def {name} : CTN :=\n  {bst_full(lo, hi)}\n")
if not TABLELESS: W(f"noncomputable def table : CTN :=\n  {top}\n")
for name, _, _ in subs: W(f"theorem {name}_ok : {name}.allOk = true := by decide +kernel\n")
if not TABLELESS: W("theorem table_ok : table.allOk = true := by\n  simp only [table, CTN.allOk, " + ", ".join(f"{nm}_ok" for nm, _, _ in subs) + ", Bool.true_and, Bool.and_true]\n  decide +kernel\n")
S_scaled = []
for r in range(Q):
    lines = [f"({sc(l)}, {sc(u)}, {'true' if cl else 'false'})" for (l, u, cl) in covers[r]]
    Sn = sc(S_in[r]); S_scaled.append(Sn)
    assert cN * (1 << SCE) <= bN[r] * Sn
    W(f"def cover{r} : List (ℕ × ℕ × Bool) := [\n  " + ",\n  ".join(lines) + "]\n")
    W(f"theorem cover{r}_ok : {OUT}.coverCheck {TB}{aN[pairs.index((r, r+1))]} (SC / 2) {Sn} cover{r} = true := by decide +kernel\n")
W(f"def bits : ℕ := {bits_new}\n")
thm = [0]
DEFS = os.environ.get("DEFS", "1") == "1"   # box of each walk theorem as a def chained to its parent (no repeated literals)
def mk(node, pos, depth, bxname=None):
    box = node[1]; fuel = FUEL0 - depth; end = pos + nnode(node)
    name = f"wk{thm[0]}"; thm[0] += 1
    if DEFS:
        if bxname is None:
            bxname = f"bx{name[2:]}"; W(f"noncomputable def {bxname} : {OUT}.Box := {box_text(box)}\n")
        bt = bxname
    else:
        bt = box_text(box)
    if node[0] == 'leaf' or nleaf(node) <= CH:
        # FORCE: the leaf-level walk is evaluated by the kernel on the call-by-value copy `walkF` and read back
        # through `walkF_eq` (emitted by gen_checkerN_force.py); the statement is unchanged
        W(f"theorem {name} : {OUT}.walk {TB}bits {fuel} {pos} {bt} = some {end} :=\n"
          f"  ({OUT}.walkF_eq {TB}bits {fuel} {pos} {bt}).symm.trans (by decide +kernel)\n")
        return name, end
    k, mid = node[2], node[3]
    if DEFS:
        nA_name = f"bx{thm[0]}"; nB_name = f"bx{thm[0] + nnode_thms(node[4])}"
        W(f"noncomputable def {nA_name} : {OUT}.Box := ({bt}).setHi ({OUT}.axOf bits {pos}) ({OUT}.Box.mid {bt} ({OUT}.axOf bits {pos}))\n")
        nA, endA = mk(node[4], pos + 4, depth + 1, nA_name)
        W(f"noncomputable def {nB_name} : {OUT}.Box := ({bt}).setLo ({OUT}.axOf bits {pos}) ({OUT}.Box.mid {bt} ({OUT}.axOf bits {pos}))\n")
        nB, endB = mk(node[5], endA, depth + 1, nB_name)
        assert endB == end
        W(f"theorem {name} : {OUT}.walk {TB}bits {fuel} {pos} {bt} = some {end} :=\n"
          f"  {OUT}.walk_split {TB}bits {fuel - 1} {pos} {bt} {endA} {end} (by decide +kernel) {nA} {nB}\n")
        return name, end
    boxA = list(box); boxA[k] = (box[k][0], mid); boxB = list(box); boxB[k] = (mid, box[k][1])
    nA, endA = mk(node[4], pos + 4, depth + 1); nB, endB = mk(node[5], endA, depth + 1)
    assert endB == end
    W(f"theorem {name} : {OUT}.walk {TB}bits {fuel} {pos} {bt} = some {end} :=\n"
      f"  {OUT}.walk_split {TB}bits {fuel - 1} {pos} {bt} {endA} {end} (by decide +kernel)\n"
      f"    (by rw [show ({bt} : {OUT}.Box).setHi ({OUT}.axOf bits {pos}) ({OUT}.Box.mid {bt} ({OUT}.axOf bits {pos})) = {box_text(boxA)} from by decide +kernel]; exact {nA})\n"
      f"    (by rw [show ({bt} : {OUT}.Box).setLo ({OUT}.axOf bits {pos}) ({OUT}.Box.mid {bt} ({OUT}.axOf bits {pos})) = {box_text(boxB)} from by decide +kernel]; exact {nB})\n")
    return name, end
def nnode_thms(node):
    """number of walk theorems emitted for a subtree (so sibling def names can be predicted)"""
    if node[0] == 'leaf' or nleaf(node) <= CH: return 1
    return 1 + nnode_thms(node[4]) + nnode_thms(node[5])
roots = []
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    name, end = mk(nodes[tup], starts[tup], 0)
    roots.append((tup, name, starts[tup], end, nodes[tup][1]))
for r in range(Q): W(f"theorem nb{r}_eq : ({OUT}.badOf cover{r}).length = {len(bads[r])} := by decide +kernel\n")
covs = " ".join(f"({OUT}.badOf cover{r})" for r in range(Q))
for (tup, name, st, end, box) in roots:
    idx = "".join(str(i) for i in tup); args = " ".join(str(i) for i in tup)
    W(f"theorem root_{idx} : {OUT}.walk {TB}bits {FUEL0} {st} ({OUT}.boxOf {covs} {args}) = some {end} := by\n"
      f"  rw [show {OUT}.boxOf {covs} {args} = {('bx' + name[2:]) if DEFS else box_text(box)} from by decide +kernel]; exact {name}\n")
cases = []
for (tup, name, st, end, box) in roots:
    idx = "".join(str(i) for i in tup)
    cases.append(f"  | {', '.join(str(i) for i in tup)}, {', '.join('_' for _ in range(Q))} => exact ⟨_, _, root_{idx}⟩")
for r in range(Q):
    pat = ", ".join((f"i + {len(bads[r])}" if k == r else "_") for k in range(Q))
    hp = ", ".join(("hi" if k == r else "_") for k in range(Q))
    cases.append(f"  | {pat}, {hp} => exact absurd hi (by omega)")
ivars = " ".join(f"i{r}" for r in range(Q)); hvars = " ".join(f"hi{r}" for r in range(Q))
W(f"theorem run_ok : ∀ {ivars}, {' → '.join(f'i{r} < ({OUT}.badOf cover{r}).length' for r in range(Q))} →\n"
  f"    ∃ pos pos', {OUT}.walk {TB}bits {FUEL0} pos ({OUT}.boxOf {covs} {ivars}) = some pos' := by\n"
  f"  intro {ivars} {hvars}\n" + "".join(f"  rw [nb{r}_eq] at hi{r}\n" for r in range(Q)) +
  f"  match {', '.join(f'i{r}' for r in range(Q))}, {', '.join(f'hi{r}' for r in range(Q))} with\n" + "\n".join(cases) + "\n")
W(f"theorem cert : ∀ {' '.join(f'g{r}' for r in range(Q))} : ℝ, {' → '.join(f'0 ≤ g{r}' for r in range(Q))} → ({OUT}.cN : ℝ) / {OUT}.SA ≤ {OUT}.G {' '.join(f'g{r}' for r in range(Q))}{f' ∨ g{Q-1} < g0' if HALFIN else ''} :=\n"
  f"  {OUT}.of_check {"" if TABLELESS else "table table_ok "}bits {FUEL0} {' '.join(f'cover{r}' for r in range(Q))} {' '.join(str(x) for x in S_scaled)}\n"
  f"    {' '.join('(by decide +kernel)' for _ in range(Q))} {' '.join(f'cover{r}_ok' for r in range(Q))} (by decide +kernel) run_ok\n")
W(f"\nend {NS}Data\n")
text = "\n".join(L)
open(f"data_{OUT}.lean", "w", encoding="utf-8").write(text)
XF = os.environ.get("XFAR", params[7] if len(params) > 7 else "0"); FG = os.environ.get("FARG", params[8] if len(params) > 8 else "0")
open(f"{OUT}_params.txt", "w").write(f"{Q} {SA} {','.join(map(str, aN))} {','.join(map(str, bN))} {cN} {OUT} {SCE} {XF} {FG}\n")
print(f"[{OUT}] cells={len(ivals)} leaves={nleaves} walk_thms={thm[0]} bytes={len(text.encode())} SCE={SCE} CH={CH}")
