#!/usr/bin/env python3
"""(bridge-port, 2026-10-11) make9qIP.py: make9qIL.py plus ROOT PROMOTION — LIMB walks with CHB/CHE boundaries (no CHL):
a root walk above CHB bits is split at its top cut(s) into walks on the same limb function from their own positions.

(bridge-port, 2026-10-11) make9qIL.py: am-cert's make9pcI.py (10-11 10:30, with LIMB walks) with the rank-1 field
widths read from the data params in `leafend`.

make8pcI.py (am-cert, 2026-10-10): make8pcC.py for a lever-1 instance (genpcellCI.py, rootR8f/AMW/PCellIV.lean).
Env IV: the interval json of arun/lever1_ivs.py on the same DATA.  Each point word is `triple + 2^96·(a + 2^24·b)` (b = 0:
no interval); every block list is checked once by `ptlOkI` (triples and intervals, the coarse-first tangent check on each
interval, ZN = the DATA's ZEXT, CSH = 3 unless set), so REG is written before the point table.  No SHARE/PTBASE/PTFLAT.

(mvt-engine) make8pc.py (bridge-port's, copied 2026-10-03) for a CLOSE instance (genpcellC.py, TZ.md §5): the node
semantics is the exact closure (tz.close; a node's incoming state is closed, the root box is closed by `tm` inside
`walk`), chunk boundaries split a closed state with `gsplit_to`/`ssplit_to` (children = `cupd`, by `rfl`), and a
chunked root goes through `tm_to`.  The data DATA.json must have been sized with TCLOSE=1.
Output: ROOT is a path relative to bench/window.

(bridge-port) The data module of the pair-cell eight-point certificate (T1 with the step-5 re-clip, Z8, fixed-width
fields) from mvt-engine's certificate data (emit8pz.py's DATA json): ROOT/AMW/{NAME}Data.lean, on the instance
ROOT/AMW/{NAME}Inst.lean (amg/genpcell4.py with DATA=..., namespace AMW.Cert.{NAME}).

Writes: the w pyramid (TOP, BK and their verification), the derivative pair table (TOPD, BKD), the sparse point table (PT: per-block lists),
the convex regions (REG), the per-gap root covers and their checks, one walk theorem per root (the walk ends at its bit
count + 1, as the kernel's walk starts at bit 1), the root run, `cert` (the half-space certificate through the generic
root cover) and `{NAME}_cert_full` (completed by reflection). Table formats and verification calls are those of
make8am.py (rootR8's CEngine).
Usage: make8pc.py DATA.json NAME [ROOT] [FUEL]"""
import os, sys, json
sys.set_int_max_str_digits(0); sys.setrecursionlimit(100000)
DJ, NAME = sys.argv[1], sys.argv[2]
ROOT = sys.argv[3] if len(sys.argv) > 3 else "rootR8"
FUEL = int(sys.argv[4]) if len(sys.argv) > 4 else 128
HERE = os.path.dirname(os.path.abspath(__file__))
D = json.load(open(DJ))
assert D["settings"].get("TCLOSE") == "1", "make8pcC.py needs closure (TCLOSE=1) data"
BSPLIT = bool(D["params"].get("BSPLIT", 0)); BND = D["params"].get("BND", []); BMG = D["params"].get("BMARG", 64)
def bcut(lo, hi):
    """the region-boundary cut (PCellCloseB.bcutL): nearest the midpoint, >= BMARG inside, first on a tie"""
    best = None
    for z in BND:
        if lo + BMG <= z <= hi - BMG and (best is None or abs(2 * z - lo - hi) < abs(2 * best - lo - hi)): best = z
    assert best is not None
    return best
Q = len(D["bN"]); WW = 1 << 40; SC = 32768                    # gaps from the data (7 for n = 8, k for a truncated window)
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
NC = sum(1 for (i, j) in PAIRS if j - i >= 2)
# (bridge-port, 2026-10-10: make9pcC.py = mvt-engine's eight/am8/make8pcC.py with the split-axis field AXB sized for any
#  Q (5 bits at Q = 7: output unchanged; 6 at Q = 8), as emit9pz.py and genpcellQ.py; ROOT may be an absolute path.)
AXB = max(1, (Q + NC - 1).bit_length())
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/eight/am8")
assert D["pairs"] == [f"{i},{j}" for (i, j) in PAIRS]
aN = D["aN"]; bN = D["bN"]
A_ = dict(zip(PAIRS, aN))
NOREFL = D["settings"].get("NOREFL") == "1"   # no mirror symmetry: the certificate covers every point (PgL), no reflection
assert NOREFL or (all(A_[(i, j)] == A_[(Q - j, Q - i)] for (i, j) in PAIRS) and bN == bN[::-1]), "the weights must be symmetric"
SHARE = os.environ.get("SHARE")              # reuse the tables (TOP, BK, TOPD, BKD, REG and their proofs) of AMW.{SHARE}Data

def dispatch(name, consts):
    """`def name (j : ℕ) : ℕ` returning consts[j], 0 elsewhere (`dsel` / `dpk` tree; make8am.py)"""
    L = []; js = sorted(consts)
    if not js: return [f"def {name} (j : ℕ) : ℕ := 0"]
    def sub(a, b):
        if b - a == 1: return f"(dpk j {js[a]} {consts[js[a]]})"
        return f"({name}s{a}_{b} j)"
    def mk(a, b):
        if b - a == 1: return
        m = (a + b) // 2; mk(a, m); mk(m, b)
        L.append(f"def {name}s{a}_{b} (j : ℕ) : ℕ := dsel j {js[m]} {sub(a, m)} {sub(m, b)}")
    mk(0, len(js))
    L.append(f"def {name} (j : ℕ) : ℕ := {sub(0, len(js))}")
    return L

out = []; W = out.append
T = D["tables"]
BK = {int(j): int(v, 16) for j, v in T["BK"].items()}
BKD = {int(j): int(v, 16) for j, v in T["BKD"].items()}
cnt = D["counts"]
W(f"""import AMW.{NAME}Inst
""" + (f"import AMW.{SHARE}Data\n" if SHARE else "") + f"""
/-! ###### certificate data `{NAME}`: the pair-cell eight-point certificate (the exact closure, Z8, fixed-width fields;
generated by mvt-engine's eight/am8/make8pcC.py, the closure variant of bridge-port's amg/make8pc.py)

From mvt-engine's `{os.path.basename(DJ)}` (window `{D['window']}`, δ {D['delta']}, cN {D['cN']}): pyramid table ({T['w_finest']} finest
cells), derivative pair table ({T['d_finest']} finest cells){f" (both shared with {SHARE}Data)" if SHARE else ""}, point table ({len(T['points'])} points), {len(D['walks'])} root walks
({cnt['walk_bits']} bits; {cnt['splits']} splits, {cnt['leaves']} leaves). Pyramid lower-bound table adapted from
five-point-pyramid-2 by typh (Apache-2.0). ###### -/

noncomputable section

namespace AMW.Cert.{NAME}Data

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.{NAME}

set_option maxRecDepth 100000
""")
def chunked(name, res, check, target, unit):
    cost = {j: (1 << (10 - res[j])) for j in res}
    chunks = []; a0 = 0; acc = 0
    for j in range(512):
        acc += cost.get(j, 0) * unit + 1
        if acc >= target or j == 511:
            chunks.append((a0, j + 1 - a0)); a0 = j + 1; acc = 0
    for cc, (a1, nn) in enumerate(chunks):
        W(f"theorem {name}_{cc} : Pyr.allFrom {a1} {nn} (fun j => {check}) = true := by decide +kernel")
    expr = f"{name}_0"
    for cc in range(1, len(chunks)): expr = f"(Pyr.allFrom_add {expr} {name}_{cc})"
    W(f"theorem {name}_all : Pyr.allFrom 0 512 (fun j => {check}) = true := by\n  have h := {expr}\n  exact h")
if SHARE:
    S_ = f"AMW.Cert.{SHARE}Data"
    W(f"""/-- the w pyramid, the derivative pair table and the regions of `{SHARE}Data`, shared (the leaves were replayed on them) -/
def TOP : ℕ := {S_}.TOP
def BK (j : ℕ) : ℕ := {S_}.BK j
theorem lbS : Pyr.LBSound TOP BK := {S_}.lbS
def TOPD : ℕ := {S_}.TOPD
def BKD (j : ℕ) : ℕ := {S_}.BKD j
theorem lbD : LBSoundD TOPD BKD := {S_}.lbD
""")
else:
    # the w pyramid
    W(f"def TOP : ℕ := {T['TOP']}")
    for j in sorted(BK): W(f"def BK_{j} : ℕ := {hex(BK[j])}")
    W("\n".join(dispatch("BK", {j: f"BK_{j}" for j in BK})))
    W("theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel\n")
    chunked("blk", {j: BK[j] & 31 for j in BK}, "Pyr.blockOk (BK j) j", 600, 1)
    W("theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok\n")
    # the derivative pair table
    W(f"def TOPD : ℕ := {T['TOPD']}")
    for j in sorted(BKD): W(f"def BKD_{j} : ℕ := {hex(BKD[j])}")
    W("\n".join(dispatch("BKD", {j: f"BKD_{j}" for j in BKD})))
    W("theorem topD_ok : topOk2 TOPD BKD = true := by decide +kernel\n")
    chunked("dblk", {j: BKD[j] & 31 for j in BKD}, "blockOk2 (BKD j) j", 600, 3)
    W("theorem lbD : LBSoundD TOPD BKD := lbDr_sound (blocks2_of dblk_all) topD_ok\n")
# the convex regions (before the point table: the interval checks read them)
RGK = {int(k): v for k, v in T["REG"].items()}
RA = sum((RGK[k][0] if k in RGK else 1) << (20 * k) for k in range(16))
RB = sum((RGK[k][1] if k in RGK else 0) << (20 * k) for k in range(16))
assert not SHARE, "lever 1: SHARE is not built"
W(f"def REG : ℕ × ℕ × List (List ℕ) := ({RA}, {RB}, [" + ", ".join("[" + ", ".join(map(str, RGK[k][2])) + "]" if k in RGK else "[]" for k in range(16)) + "])")
W("theorem hR : rgOk REG = true := by decide +kernel\n")
# the point table: sparse, a dispatch on the block `x >> 10` to a short list per block (`ptl`, each list checked once by
# `ptlOkI`: the triple and the word's precertified tangent interval); reads of a point repeat across leaves and the kernel
# caches them
from collections import defaultdict
IVJ = json.load(open(os.environ["IV"]))
IVS = {int(p): tuple(v) for p, v in IVJ["ivs"].items()}
ZNI = int(D["params"]["ZEXT"]); CSHI = int(os.environ.get("CSH", "3"))
assert ZNI > 0
blocks = defaultdict(list)
for x, tr in T["points"]:
    assert x < 524288
    v = int(tr, 16); assert v < (1 << 96)
    if x in IVS:
        a, b = IVS[x]; assert 0 < b and a <= x <= b and a < (1 << 24)
        v |= (a << 96) | (b << 120)
    blocks[x >> 10].append((x, v))
assert set(IVS) <= {x for x, _ in T["points"]}, "an interval for a point outside the table"
print(f"points {len(T['points'])}, with an interval {len(IVS)}")
ROOTC = os.environ.get("ROOTC") == "1"       # (CH = 0) root walks on `ofCl (rootCl …) 0`: no root-state literals
assert not os.environ.get("PTFLAT") and not os.environ.get("PTBASE"), "lever 1: PTFLAT/PTBASE are not built"
for j in sorted(blocks):
    W(f"def PTL_{j} (x : ℕ) : ℕ := ptl [" + ", ".join(f"({x}, {hex(v)})" for x, v in sorted(blocks[j])) + "] x")
    W(f"theorem PTL_{j}_ok : ∀ x, PVI x (PTL_{j} x) :=\n  ptlI_sound (n := {ZNI}) (csh := {CSHI}) lbS lbD hR (by decide) _ (by decide +kernel)")
js = sorted(blocks)
def psub(a_, b_):
    if b_ - a_ == 1: return f"(dpk (Nat.shiftRight x 10) {js[a_]} (PTL_{js[a_]} x))"
    return f"(PTs{a_}_{b_} x)"
def ppf(a_, b_):
    if b_ - a_ == 1: return f"(pvi_dpk (PTL_{js[a_]}_ok x))"
    return f"(PTs{a_}_{b_}_ok x)"
def pmk(a_, b_):
    if b_ - a_ == 1: return
    m_ = (a_ + b_) // 2; pmk(a_, m_); pmk(m_, b_)
    W(f"def PTs{a_}_{b_} (x : ℕ) : ℕ := dsel (Nat.shiftRight x 10) {js[m_]} {psub(a_, m_)} {psub(m_, b_)}")
    W(f"theorem PTs{a_}_{b_}_ok (x : ℕ) : PVI x (PTs{a_}_{b_} x) := pvi_dsel {ppf(a_, m_)} {ppf(m_, b_)}")
pmk(0, len(js))
W(f"/-- the point function: the point words (triple, interval) -/\ndef PT (x : ℕ) : ℕ := {psub(0, len(js))}")
W(f"theorem ptS : ∀ x, PVI x (PT x) := fun x => {ppf(0, len(js))}\n")
PB3 = blocks
# the root covers
S = D["S"]; COV = D["covers"]
for k in range(Q):
    pos = SC // 2
    for (l, u, cl) in COV[k]: assert l == pos; pos = u
    assert pos == S[k]
bads = [[(l, u) for (l, u, cl) in COV[k] if not cl] for k in range(Q)]
W("/-- the per-gap root covers `(l, u, clear)` and their ends -/")
W("def COV : List (List (ℕ × ℕ × Bool)) := [\n  " + ",\n  ".join("[" + ", ".join(f"({l}, {u}, {'true' if cl else 'false'})" for (l, u, cl) in COV[k]) + "]" for k in range(Q)) + "]")
W(f"def SMAX (r : ℕ) : ℕ := [{', '.join(map(str, S))}].getD r 0\n")
# the root walks, chunked: a subtree of at most CH leaves is one walk theorem; above that, the node is a boundary (T1
# into the equality continuation, the split lemma, both children covered)
CH = int(os.environ.get("CH", "0")); assert not (BSPLIT and CH), "midpoint chunk boundaries (CH) do not cover BSPLIT; use CHB"
# CHB (am-cert, 2026-10-10): chunk by walk bits — a node whose walk is at most CHB bits is one walk theorem; above that
# the node is a boundary split at the walk's own cut q (midpoint or region boundary; `gsplitq_to`/`ssplitq_to`, the HELP
# instance of genpcellQI.py), and a non-root chunk runs `walkC` on its closed incoming state (`covered_of_walkCP`)
CHB = int(os.environ.get("CHB", "0")); assert not (CH and CHB)
# CHL=1 (with CHB): each chunk walk reads its own literal `WB{n}L{k}` (the chunk's bits only, positions from 1), so no
# leaf reads the whole root literal; the root literal is not written for a split root
CHL = os.environ.get("CHL") == "1"; assert not CHL or CHB
# CHE=1 (with CHB): compact boundaries — child states are expressions `chA t i j q` / `chB t j i q` (the walk's own
# closure), proved by `gsplitc_to`/`ssplitc_to` with no state literal and no elaborator `rfl`; the root boundary keeps
# its closed root literal (`tm_to`)
CHE = os.environ.get("CHE") == "1"; assert not CHE or CHB
# LIMB=LB, WIN (am-cert, 2026-10-11): limb-table walks (the instance from genpcellQI.py with the same LIMB and WIN):
# each root walk is written as overlapping limbs `WL{n}_{k}` (bits [k·LB, k·LB + LB + WIN)) behind a `dsel` dispatch
# `WL{n}`, and the walk reads `WD{n} := rdw WL{n}`; no chunking
LIMB = int(os.environ.get("LIMB", "0")); LWIN = int(os.environ.get("WIN", "0"))
# (bridge-port, make9qIP.py, ROOT PROMOTION): LIMB walks may now carry CHB boundaries without chunk-local literals (CHL):
#  a subtree above CHB bits splits at its own cut (with CHE: compact `chA`/`chB` children, `gsplitc_to`/`ssplitc_to`), and
#  every piece runs `walkC` on the root's own limb function `WD{n}` from its absolute bit position (`covered_of_walkCP`,
#  which the LIMB instance states for `bits : ℕ → ℕ`).  No new literal; the root's closed state is the one `T{n}_k` def.
assert not LIMB or (LWIN and not CH and not (CHB and os.environ.get("CHL") == "1"))
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(DJ))))
import tz
def kstate(l, u, cons):
    """the kernel state: gaps, the 21 pair bounds (absent: 0 and 2^40), the unused mask"""
    return [x for r in range(Q) for x in (l[r], u[r])] + [x for t in SUMS for x in ((cons[t] if t in cons else (0, WW)))] + [0]
def build(W_, l, u, cons, pos):
    """the walk tree from bit pos (0-based): (kind, state, pos, end, leaves, extra)"""
    st0 = kstate(l, u, cons)
    r_ = tz.t1(l, u, {k: v for k, v in cons.items()}, Q)
    if r_ is None: return ("empty", st0, pos, pos, 0, None)
    l2, u2, cons2, I = r_
    cons2 = {t: tuple(v) for t, v in cons2.items()}
    get = lambda p_, k: (W_ >> p_) & ((1 << k) - 1)
    if get(pos, 1):
        ax = get(pos + 1, AXB)
        if ax < Q:
            m = (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
            A = build(W_, l2, uA, dict(cons2), pos + 1 + AXB); B = build(W_, lB, u2, dict(cons2), A[3])
        else:
            t = SUMS[ax - Q]; lo, hi = cons2[t]; m = (lo + hi) >> 1
            cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
            A = build(W_, l2, u2, cA, pos + 1 + AXB); B = build(W_, l2, u2, cB, A[3])
        return ("split", st0, pos, B[3], A[4] + B[4], (ax, kstate(l2, u2, cons2), A, B))
    if u2[Q - 1] < l2[0]: return ("leaf", st0, pos, pos + 1, 1, None)
    raise RuntimeError("leaf payload lengths are taken from the walk theorem")
def leafend(W_, pos, nACT):
    """a minorant leaf's end (fixed-width layout)"""
    # (bridge-port, make9qIL.py = am-cert's make9pcI.py of 10-11 10:30 (LIMB walks) with the rank-1 field widths from the
    #  data params: j fields JB, λ LB, Yq QB; identical output when JB = 7, LB = 8, QB = 12)
    p_ = pos + 2
    for _ in range(nACT):
        k = (W_ >> p_) & 3; p_ += 2 + (JBW if k >= 1 else 0) + (JBW if k == 3 else 0) + (LBW if k >= 2 else 0)
    while (W_ >> p_) & 1: p_ += 1 + 5 + 1 + QBW
    return p_ + 1
JBW = int(D["params"]["JB"]); LBW = int(D["params"]["LB"]); QBW = int(D["params"]["QB"])
NACT = sum(1 for a in aN if a > 0)
def build2(W_, l, u, cons, pos, root=True):
    """(closure) a node's incoming kernel state is its closed state (the parent's split closes it), except the root's,
    the box with pair bounds absent, which `walk` closes (`tm`)"""
    r_ = tz.close(l, u, dict(cons), Q)
    if r_ is None: raise RuntimeError("a closed child is never empty")
    l2, u2, cons2, I = r_
    cons2 = {t: tuple(v) for t, v in cons2.items()}
    st0 = kstate(l, u, cons) if root else kstate(l2, u2, cons2)
    if (W_ >> pos) & 1:
        ax = (W_ >> (pos + 1)) & ((1 << AXB) - 1)
        md = (W_ >> (pos + 1 + AXB)) & 1 if BSPLIT else 0; p2 = pos + 2 + AXB if BSPLIT else pos + 1 + AXB
        if ax < Q:
            m = bcut(l2[ax], u2[ax]) if md else (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
            A = build2(W_, l2, uA, dict(cons2), p2, False); B = build2(W_, lB, u2, dict(cons2), A[3], False)
        else:
            t = SUMS[ax - Q]; lo, hi = cons2[t]; m = bcut(lo, hi) if md else (lo + hi) >> 1
            cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
            A = build2(W_, l2, u2, cA, p2, False); B = build2(W_, l2, u2, cB, A[3], False)
        return ("split", st0, pos, B[3], A[4] + B[4], (ax, kstate(l2, u2, cons2), A, B, m))
    if u2[Q - 1] < l2[0] and not NOREFL: return ("leaf", st0, pos, pos + 1, 1, None)
    return ("leaf", st0, pos, leafend(W_, pos, NACT), 1, None)
def sts(v): return "⟨" + ", ".join(map(str, v)) + "⟩"
STV = [x for r in range(Q) for x in (f"l{r}", f"u{r}")] + [x for (i, j) in SUMS for x in (f"A{i}{j}", f"B{i}{j}")] + ["M"]
nchunk = [0, 0]
def emit_chunk(n, nd, sx, root=False):
    """the theorem covering node nd, whose incoming state is the Lean term sx; returns its name.  (closure) A boundary
    splits its closed state `t` (for the root, after `tm_to`), the children being the closed `cupd` states (by `rfl`)"""
    name = f"cc{n}_{nchunk[0]}"; nchunk[0] += 1
    kind, st0, pos, end, nl, ex = nd
    if CHB and CHL and not root and (kind != "split" or end - pos <= CHB):
        lit = ((W_ >> pos) & ((1 << (end - pos)) - 1)) << 1
        W(f"""def WB{n}L{nchunk[0]} : ℕ := {hex(lit)}
theorem w{name} : U (walkC TOP BK TOPD BKD PT REG WB{n}L{nchunk[0]} {FUEL} 1) {sx} = {end - pos + 1} := by
  decide +kernel
theorem {name} : Covered (toCl {sx}) :=
  covered_of_walkCP lbS lbD ptS hR WB{n}L{nchunk[0]} {FUEL} 1 {end - pos + 1} _ w{name} (by decide)""")
        return name
    if CHB and not root and (kind != "split" or end - pos <= CHB):
        WSRC = f"WD{n}" if LIMB else f"WB{n}"      # (root promotion) the root's limb function, absolute positions
        W(f"""theorem w{name} : U (walkC TOP BK TOPD BKD PT REG {WSRC} {FUEL} {pos + 1}) {sx} = {end + 1} := by
  decide +kernel
theorem {name} : Covered (toCl {sx}) :=
  covered_of_walkCP lbS lbD ptS hR {WSRC} {FUEL} {pos + 1} {end + 1} _ w{name} (by decide)""")
        return name
    if kind != "split" or (nl <= CH if CH else end - pos <= CHB if CHB else True):
        WBN = f"WD{n}" if LIMB else f"WB{n}"
        W(f"""theorem w{name} : U (walk TOP BK TOPD BKD PT REG {WBN} {FUEL} {pos + 1}) {sx} = {end + 1} := by
  decide +kernel
theorem {name} : Covered (toCl {sx}) :=
  covered_of_walkP lbS lbD ptS hR {WBN} {FUEL} {pos + 1} {end + 1} _ w{name} (by decide)""")
        return name
    nchunk[1] += 1
    ax, st1, A, B, mq = ex
    # a non-root boundary's closed state is its incoming state (a child def of the boundary above): reuse its name
    tn = f"T{n}_{nchunk[1]}" if root else sx; tA = f"T{n}_{nchunk[1]}A"; tB = f"T{n}_{nchunk[1]}B"
    if CHE:
        ij = (f"{ax}", f"({ax} + 1)") if ax < Q else (f"(pI PR {ax - Q})", f"(pJ PR {ax - Q})")
        W((f"def {tn} : St := {sts(st1)}\n" if root else "") + f"def {tA} : St := chA {tn} {ij[0]} {ij[1]} {mq}\ndef {tB} : St := chB {tn} {ij[1]} {ij[0]} {mq}")
        sp = f"gsplitc_to {ax} {mq} (by decide)" if ax < Q else f"ssplitc_to {ax - Q} {mq} (by decide)"
        a = emit_chunk(n, A, tA); b = emit_chunk(n, B, tB)
        body = f"{sp} (t := {tn}) {a} {b}"
        W(f"""theorem {name} : Covered (toCl {sx}) :=
  """ + (f"tm_to (t := {tn}) (by decide +kernel) ({body})" if root else body))
        return name
    W((f"def {tn} : St := {sts(st1)}\n" if root else "") + f"def {tA} : St := {sts(A[1])}\ndef {tB} : St := {sts(B[1])}")
    if CHB: sp = f"gsplitq_to {ax} {mq} (by decide)" if ax < Q else f"ssplitq_to {ax - Q} {mq} (by decide)"
    else: sp = f"gsplit_to {ax} (by decide)" if ax < Q else f"ssplit_to {ax - Q} (by decide)"
    a = emit_chunk(n, A, tA); b = emit_chunk(n, B, tB)
    body = f"{sp} (t := {tn}) (sA := {tA}) (sB := {tB}) rfl rfl {a} {b}"
    W(f"""theorem {name} : Covered (toCl {sx}) :=
  """ + (f"tm_to (t := {tn}) (by decide +kernel) ({body})" if root else body))
    return name
names = []
# RCOMP (with ROOTC, CH = 0): one root lemma `rcOf` and a one-line theorem per root (the same walk, the same `decide`)
RCOMP = os.environ.get("RCOMP") == "1" and ROOTC and CH == 0
if RCOMP:
    iv0 = " ".join(f"i{r}" for r in range(Q)); il0 = ", ".join(f"i{r}" for r in range(Q))
    W(f"""/-- the root cell with cover indices `i0 … i{Q - 1}` -/
def RC ({iv0} : ℕ) : Cl := rootCl {Q} {NC} {WW} COV (fun r => [{il0}].getD r 0)
/-- a root is covered when its walk ends at a nonzero bit count -/
theorem rcOf {{{iv0} : ℕ}} (wb e : ℕ) (h : U (walk TOP BK TOPD BKD PT REG wb {FUEL} 1) (ofCl (RC {iv0}) 0) = e)
    (he : e ≠ 0) : Covered (RC {iv0}) := by
  have h' := covered_of_walk lbS lbD ptS hR wb {FUEL} e _ h he
  rwa [toCl_ofCl _ _ rfl rfl rfl rfl] at h'""")
for n, wk in enumerate(D["walks"]):
    tup = wk["root"]; box = wk["cell"]
    assert [tuple(box[r]) for r in range(Q)] == [bads[r][tup[r]] for r in range(Q)], (n, tup)
    W_ = int(wk["hex"], 16)
    bits = W_ << 1
    idx = ", ".join(map(str, tup))
    tree = build2(W_, [c[0] for c in box], [c[1] for c in box], {}, 0)
    if LIMB:
        nlimb = (bits.bit_length() + LIMB - 1) // LIMB
        for k_ in range(nlimb): W(f"def WL{n}_{k_} : ℕ := {hex((bits >> (k_ * LIMB)) & ((1 << (LIMB + LWIN)) - 1))}")
        W("\n".join(dispatch(f"WL{n}", {k_: f"WL{n}_{k_}" for k_ in range(nlimb)})))
        W(f"def WD{n} : ℕ → ℕ := rdw WL{n}")
    elif not (CHL and tree[0] == "split" and tree[3] - tree[2] > CHB): W(f"def WB{n} : ℕ := {hex(bits)}")
    assert tree[3] == wk["nbits"], (n, tree[3], wk["nbits"])
    if RCOMP:
        W(f"theorem rc{n} : Covered (RC {' '.join(map(str, tup))}) := rcOf WB{n} {tree[3] + 1} (by decide +kernel) (by decide)")
    elif ROOTC and CH == 0:
        # (compact) the walk runs on the root cell itself, `ofCl (rootCl …) 0`, so no state literal is written
        rc_ = f"rootCl {Q} {NC} {WW} COV (fun r => [{idx}].getD r 0)"
        W(f"""theorem wr{n} : U (walk TOP BK TOPD BKD PT REG WB{n} {FUEL} 1) (ofCl ({rc_}) 0) = {tree[3] + 1} := by
  decide +kernel
theorem rc{n} : Covered ({rc_}) := by
  have h := covered_of_walk lbS lbD ptS hR WB{n} {FUEL} {tree[3] + 1} _ wr{n} (by decide)
  rwa [toCl_ofCl _ _ rfl rfl rfl rfl] at h""")
    else:
        top = emit_chunk(n, tree, sts(tree[1]), root=True)
        st = ", ".join(map(str, tree[1]))
        W(f"""theorem rc{n} : Covered (rootCl {Q} {NC} {WW} COV (fun r => [{idx}].getD r 0)) := by
  have e : rootCl {Q} {NC} {WW} COV (fun r => [{idx}].getD r 0) = toCl ⟨{st}⟩ := rfl
  rw [e]; exact {top}""")
    names.append((tuple(tup), f"rc{n}"))
print("chunks", nchunk[0], "boundaries", nchunk[1])
assert len(names) == len({t for t, _ in names}) and len(names) == eval("*".join(str(len(b)) for b in bads))
iv_ = " ".join(f"i{r}" for r in range(Q)); hv_ = " ".join(f"h{r}" for r in range(Q))
cases = []
for tup, nmx in names:
    cases.append(f"  | {', '.join(map(str, tup))}, {', '.join('_' for _ in range(Q))} => exact {nmx}")
for r in range(Q):
    pat = ", ".join((f"i + {len(bads[r])}" if rr == r else "_") for rr in range(Q))
    hp = ", ".join(("hi" if rr == r else "_") for rr in range(Q))
    cases.append(f"  | {pat}, {hp} => exact absurd hi (by omega)")
W(f"""theorem run{Q} ({iv_} : ℕ) {' '.join(f'(h{r} : i{r} < {len(bads[r])})' for r in range(Q))} :
    Covered (rootCl {Q} {NC} {WW} COV (fun r => [{', '.join(f'i{r}' for r in range(Q))}].getD r 0)) := by
  match {', '.join(f'i{r}' for r in range(Q))}, {', '.join(f'h{r}' for r in range(Q))} with
""" + "\n".join(cases) + "\n")
W(f"""theorem run : ∀ idx : ℕ → ℕ, (∀ r < {Q}, idx r < (badOf (COV.getD r [])).length) → Covered (rootCl {Q} {NC} {WW} COV idx) := by
  intro idx h
  rw [rootCl_congr (idx' := fun r => [{', '.join(f'idx {r}' for r in range(Q))}].getD r 0) (fun r hr => by interval_cases r <;> rfl)]
""" + "".join(f"  have l{r} : (badOf (COV.getD {r} [])).length = {len(bads[r])} := rfl\n" for r in range(Q)) +
  f"  exact run{Q} {' '.join(['_'] * Q)} " + " ".join(f"(l{r} ▸ h {r} (by norm_num))" for r in range(Q)) + "\n")
XS_ = ' '.join(f'x{r}' for r in range(Q)); HS_ = ' '.join(f'h{r}' for r in range(Q))
if NOREFL:
    W(f"""/-- the certificate on every point with nonnegative gaps (no reflection: the truncated functional has no mirror symmetry) -/
theorem cert : ∀ g : ℕ → ℝ, (∀ r < {Q}, 0 ≤ g r) → PgL cN {Q} BS TS g :=
  cert_of COV SMAX (by decide) (by decide +kernel) (by decide) {WW} (by decide) run

end AMW.Cert.{NAME}Data

end

noncomputable section

namespace AMW.Cert

/-- **the truncated-window certificate** on every point with nonnegative gaps -/
theorem {NAME}_cert_full : ∀ {XS_} : ℝ, {' → '.join(f'0 ≤ x{r}' for r in range(Q))} →
    ({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {XS_} := by
  intro {XS_} {HS_}
  have hg : ∀ r < {Q}, 0 ≤ (fun r => [{', '.join(f'x{r}' for r in range(Q))}].getD r 0) r := by
    intro r hr; interval_cases r <;> simpa
  have h := {NAME}Data.cert _ hg
  simp only [AMW.Cert.PCell.PgL] at h
  rw [{NAME}.Fg_G] at h
  rw [div_le_iff₀ (by norm_num [{NAME}.SA])]
  linarith

end AMW.Cert

end
""")
TAIL_SYM = (f"""/-- the half-space certificate on every point with nonnegative gaps -/
theorem cert : ∀ g : ℕ → ℝ, (∀ r < {Q}, 0 ≤ g r) → Pg cN {Q} BS TS g :=
  cert_of COV SMAX (by decide) (by decide +kernel) (by decide) {WW} (by decide) run

end AMW.Cert.{NAME}Data

end

noncomputable section

namespace AMW.Cert

theorem {NAME}_G_rev ({' '.join(f'x{r}' for r in range(Q))} : ℝ) : {NAME}.G {' '.join(f'x{r}' for r in reversed(range(Q)))} = {NAME}.G {' '.join(f'x{r}' for r in range(Q))} := by
  unfold {NAME}.G; ring_nf

theorem {NAME}_half ({' '.join(f'y{r}' for r in range(Q))} : ℝ) {' '.join(f'(h{r} : 0 ≤ y{r})' for r in range(Q))} :
    ({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(f'y{r}' for r in range(Q))} ∨ y{Q - 1} < y0 := by
  have hg : ∀ r < {Q}, 0 ≤ (fun r => [{', '.join(f'y{r}' for r in range(Q))}].getD r 0) r := by
    intro r hr; interval_cases r <;> simpa
  rcases {NAME}Data.cert _ hg with h | h
  · left
    rw [{NAME}.Fg_G] at h
    rw [div_le_iff₀ (by norm_num [{NAME}.SA])]
    linarith
  · right; simpa using h

/-- **the AM eight-point certificate**: the half-space certificate completed by reflection (symmetric weights) -/
theorem {NAME}_cert_full : ∀ {' '.join(f'x{r}' for r in range(Q))} : ℝ, {' → '.join(f'0 ≤ x{r}' for r in range(Q))} →
    ({NAME}.cN : ℝ) / {NAME}.SA ≤ {NAME}.G {' '.join(f'x{r}' for r in range(Q))} := by
  intro {' '.join(f'x{r}' for r in range(Q))} {' '.join(f'h{r}' for r in range(Q))}
  rcases lt_or_ge x{Q - 1} x0 with hlt | hle
  · rcases {NAME}_half {' '.join(f'x{r}' for r in reversed(range(Q)))} {' '.join(f'h{r}' for r in reversed(range(Q)))} with h | h
    · rw [← {NAME}_G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases {NAME}_half {' '.join(f'x{r}' for r in range(Q))} {' '.join(f'h{r}' for r in range(Q))} with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)

end AMW.Cert

end
""")
if not NOREFL: W(TAIL_SYM)
txt = "\n".join(out)
P = os.path.join(HERE, "..", "..", "window", ROOT, "AMW", f"{NAME}Data.lean")
if os.path.exists(P) and os.environ.get("OVERWRITE") != "1": raise SystemExit(f"{P} exists (OVERWRITE=1 to replace)")
open(P, "w").write(txt)
print(P, "bytes", len(txt.encode()), "walks", len(D["walks"]), "bads", [len(b) for b in bads], "point blocks", len(PB3))
