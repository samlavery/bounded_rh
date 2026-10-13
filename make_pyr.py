#!/usr/bin/env python3
"""Size and emit a weighted six-point certificate on the PYRAMID oracle (new pipeline; make_w.py / gen_data_N.py /
reemit_force.py are untouched).  Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).

Usage: make_pyr.py DELTA NAME [CH]
  DELTA: slack (cN = round(358287 (1 - DELTA))), NAME: certificate name, CH: max leaves per walk theorem.
Writes data_<NAME>.lean, <NAME>_params.txt (for gen_tail_w.py), <NAME>_order.txt (early-exit order for
gen_checker_pyr.py), head_<NAME>.lean, and prints the sizes.
The bisection rule is gen_w's passfirst_sum (WFRAC=4, half-space); the leaf test is the Lean `leafOK` (integer,
oracle `Pyr.lb` on the table built here); every leaf is re-verified on the built table before emission."""
import os, sys, itertools, time
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "bench", "pyr"))
from size_pyr import run, PAIRS, Q, AN, BN, SA
from pyr_table import lean_consts
DELTA = float(sys.argv[1]); NAME = sys.argv[2]; CH = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
cN = round(358287 * (1 - DELTA))
t0 = time.time()
r = run(cN, PE=5, PB=10, MAXA=4)
assert r is not None and r["bad_leaves"] == 0
P = r["P"]; nodes = r["nodes"]; covers = r["covers"]; bads = r["bads"]; S = r["S"]
SC = 1 << 15; U = P.U
assert (P.PE, P.PB, P.KT, P.MAXA, P.EB, P.FUEL, P.U) == (5, 10, 19, 4, 32, 14, 10**10), "the Lean checker bakes these in"
assert max(P.res) < 512 and P.xmax <= (1 << 19)
# ---- early-exit order: by total contribution over the leaves ----
leaves = []
def collect(nd):
    if nd[0] == 'leaf': leaves.append(nd[1])
    else: collect(nd[4]); collect(nd[5])
for nd in nodes.values(): collect(nd)
def terms(box): return [(sum(box[q][0] for q in range(i, j)), sum(box[q][1] for q in range(i, j))) for (i, j) in PAIRS]
contrib = [0] * len(PAIRS)
for b in leaves:
    if b[0][0] > b[Q - 1][1]: continue
    for t, (lo, hi) in enumerate(terms(b)): contrib[t] += AN[t] * P.lb(lo, hi)
ORDER = sorted(range(len(PAIRS)), key=lambda t: -contrib[t])
# ---- Lean data ----
L = []; W = L.append
NS = f"Zeta23Ext.Bridge.ThreePoint.{NAME}"
st = P.stats()
W(f"\n/-! ###### certificate data `{NAME}`: pyramid table ({st['blocks']} blocks, {st['finest']} finest cells, "
  f"{st['entries']} entries), {r['nleaves']} leaves (half-space) ###### -/\n")
W(f"noncomputable section\n\nnamespace {NS}Data\n\nopen Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr {NS}\n\nset_option maxRecDepth 100000\n")
W(lean_consts(P))
W("theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel\n")
# block checks in chunks of about equal cost (finest cells)
cost = {j: (1 << (P.PB - P.res[j])) for j in P.res}
chunks = []; a = 0; acc = 0; TARGET = 600
for j in range(512):
    acc += cost.get(j, 0) + 1
    if acc >= TARGET or j == 511:
        chunks.append((a, j + 1 - a)); a = j + 1; acc = 0
for c, (a, nn) in enumerate(chunks):
    W(f"theorem blk_{c} : Pyr.allFrom {a} {nn} (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel")
expr = "blk_0"
for c in range(1, len(chunks)): expr = f"(Pyr.allFrom_add {expr} blk_{c})"
W(f"theorem blk_all : Pyr.allFrom 0 512 (fun j => Pyr.blockOk (BK j) j) = true := by\n  have h := {expr}\n  exact h")
W("theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok\n")
# covers
aAdj = [AN[PAIRS.index((q, q + 1))] for q in range(Q)]
for q in range(Q):
    clear, bad = covers[q]
    segs = sorted([(l, u, True) for (l, u) in clear] + [(l, u, False) for (l, u) in bad])
    pos = SC // 2
    for (l, u, cl) in segs: assert l == pos; pos = u
    assert pos == S[q]
    W(f"def cover{q} : List (ℕ × ℕ × Bool) := [\n  " + ",\n  ".join(f"({l}, {u}, {'true' if cl else 'false'})" for (l, u, cl) in segs) + "]")
    W(f"theorem cover{q}_ok : {NAME}.coverCheck {aAdj[q]} (SC / 2) {S[q]} cover{q} = true := by decide +kernel\n")
# walk chunks
def nleaf(nd): return 1 if nd[0] == 'leaf' else nleaf(nd[4]) + nleaf(nd[5])
def height(nd): return 1 if nd[0] == 'leaf' else 1 + max(height(nd[4]), height(nd[5]))
def code(nd, out):
    if nd[0] == 'leaf': out.append(0)
    else:
        out.append(1); out.extend([(nd[2] >> i) & 1 for i in range(3)]); code(nd[4], out); code(nd[5], out)
def coords(box): return " ".join(f"{l} {u}" for (l, u) in box)
nthm = [0]; nbits = [0]; nchunk_leaves = []
def proof(nd):
    if nleaf(nd) <= CH:
        bl = [0]; code(nd, bl)
        bits = sum(1 << i for i, b in enumerate(bl) if b)
        e = len(bl); nbits[0] += len(bl)
        name = f"wk{nthm[0]}"; nthm[0] += 1; nchunk_leaves.append(nleaf(nd))
        W(f"theorem {name} : {NAME}.Covered {coords(nd[1])} :=\n  {NAME}.covered_of_walk lbS {bits} {height(nd) + 1} {coords(nd[1])} {e} (by decide +kernel) (by decide)")
        return name
    k, m = nd[2], nd[3]
    return f"({NAME}.covered_split{k} {m} {proof(nd[4])} {proof(nd[5])})"
roots = {}
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    roots[tup] = proof(nodes[tup])
for q in range(Q):
    for i, (l, u) in enumerate(bads[q]):
        W(f"theorem bd{q}_{i} : ({NAME}.badOf cover{q}).getD {i} (0, 0) = ({l}, {u}) := by decide +kernel")
    W(f"theorem nb{q}_eq : ({NAME}.badOf cover{q}).length = {len(bads[q])} := by decide +kernel")
cases = []
for tup, pf in roots.items():
    rw = ", ".join(f"bd{q}_{tup[q]}" for q in range(Q))
    cases.append(f"  | {', '.join(str(i) for i in tup)}, {', '.join('_' for _ in range(Q))} => rw [{rw}]; exact {pf}")
for q in range(Q):
    pat = ", ".join((f"i + {len(bads[q])}" if k == q else "_") for k in range(Q))
    hp = ", ".join(("hi" if k == q else "_") for k in range(Q))
    cases.append(f"  | {pat}, {hp} => exact absurd hi (by omega)")
iv = " ".join(f"i{q}" for q in range(Q)); hv = " ".join(f"hi{q}" for q in range(Q))
W(f"theorem run_ok : ∀ {iv}, {' → '.join(f'i{q} < ({NAME}.badOf cover{q}).length' for q in range(Q))} →\n"
  f"    {NAME}.Covered {' '.join(f'(({NAME}.badOf cover{q}).getD i{q} (0, 0)).1 (({NAME}.badOf cover{q}).getD i{q} (0, 0)).2' for q in range(Q))} := by\n"
  f"  intro {iv} {hv}\n" + "".join(f"  rw [nb{q}_eq] at hi{q}\n" for q in range(Q)) +
  f"  match {', '.join(f'i{q}' for q in range(Q))}, {', '.join(f'hi{q}' for q in range(Q))} with\n" + "\n".join(cases) + "\n")
W(f"theorem cert : ∀ {' '.join(f'g{q}' for q in range(Q))} : ℝ, {' → '.join(f'0 ≤ g{q}' for q in range(Q))} → "
  f"({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(f'g{q}' for q in range(Q))} ∨ g{Q-1} < g0 :=\n"
  f"  {NAME}.of_check {' '.join(f'cover{q}' for q in range(Q))} {' '.join(str(x) for x in S)}\n"
  f"    {' '.join('(by decide +kernel)' for _ in range(Q))} {' '.join(f'cover{q}_ok' for q in range(Q))} (by decide +kernel) run_ok\n")
W(f"end {NS}Data\n\nend\n")
text = "\n".join(L)
open(os.path.join(HERE, f"data_{NAME}.lean"), "w", encoding="utf-8").write(text)
open(os.path.join(HERE, f"{NAME}_params.txt"), "w").write(f"{Q} {SA} {','.join(map(str, AN))} {','.join(map(str, BN))} {cN} {NAME} 15 0 0\n")
open(os.path.join(HERE, f"{NAME}_order.txt"), "w").write(",".join(map(str, ORDER)) + "\n")
print(f"[{NAME}] delta={DELTA} cN={cN} leaves={r['nleaves']} table={st} chunks={nthm[0]} (max {max(nchunk_leaves)} leaves) "
      f"bits={nbits[0]} order={ORDER} bytes={len(text.encode())} ({time.time()-t0:.0f}s)")
