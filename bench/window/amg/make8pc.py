#!/usr/bin/env python3
"""(bridge-port) The data module of the pair-cell eight-point certificate (T1 with the step-5 re-clip, Z8, fixed-width
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
Q = 7; NC = 21; WW = 1 << 40; SC = 32768
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
assert D["pairs"] == [f"{i},{j}" for (i, j) in PAIRS]
aN = D["aN"]; bN = D["bN"]
A_ = dict(zip(PAIRS, aN))
assert all(A_[(i, j)] == A_[(Q - j, Q - i)] for (i, j) in PAIRS) and bN == bN[::-1], "the weights must be symmetric"

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

/-! ###### certificate data `{NAME}`: the pair-cell eight-point certificate (T1 with the re-clip, Z8, fixed-width fields)

From mvt-engine's `{os.path.basename(DJ)}` (window `{D['window']}`, δ {D['delta']}, cN {D['cN']}): pyramid table ({T['w_finest']} finest
cells), derivative pair table ({T['d_finest']} finest cells), point table ({len(T['points'])} points), 32 root walks
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
# the point table: sparse, a dispatch on the block `x >> 10` to a short list per block (`ptl`, each list checked by
# `ptlOk`); reads of a point repeat across leaves and the kernel caches them
from collections import defaultdict
blocks = defaultdict(list)
for x, tr in T["points"]:
    assert x < 524288
    blocks[x >> 10].append((x, int(tr, 16)))
for j in sorted(blocks):
    W(f"def PTL_{j} (x : ℕ) : ℕ := ptl [" + ", ".join(f"({x}, {hex(v)})" for x, v in sorted(blocks[j])) + "] x")
    W(f"theorem PTL_{j}_ok : PTF PTL_{j} := ptl_sound _ (by decide +kernel)")
js = sorted(blocks)
def psub(a_, b_):
    if b_ - a_ == 1: return f"(dpk (Nat.shiftRight x 10) {js[a_]} (PTL_{js[a_]} x))"
    return f"(PTs{a_}_{b_} x)"
def ppf(a_, b_):
    if b_ - a_ == 1: return f"(pv_dpk (PTL_{js[a_]}_ok x))"
    return f"(PTs{a_}_{b_}_ok x)"
def pmk(a_, b_):
    if b_ - a_ == 1: return
    m_ = (a_ + b_) // 2; pmk(a_, m_); pmk(m_, b_)
    W(f"def PTs{a_}_{b_} (x : ℕ) : ℕ := dsel (Nat.shiftRight x 10) {js[m_]} {psub(a_, m_)} {psub(m_, b_)}")
    W(f"theorem PTs{a_}_{b_}_ok (x : ℕ) : PV x (PTs{a_}_{b_} x) := pv_dsel {ppf(a_, m_)} {ppf(m_, b_)}")
pmk(0, len(js))
W(f"/-- the point function -/\ndef PT (x : ℕ) : ℕ := {psub(0, len(js))}")
W(f"theorem ptS : PTF PT := fun x => {ppf(0, len(js))}\n")
PB3 = blocks
# the convex regions
RGK = {int(k): v for k, v in T["REG"].items()}
RA = sum((RGK[k][0] if k in RGK else 1) << (20 * k) for k in range(16))
RB = sum((RGK[k][1] if k in RGK else 0) << (20 * k) for k in range(16))
W(f"def REG : ℕ × ℕ × List (List ℕ) := ({RA}, {RB}, [" + ", ".join("[" + ", ".join(map(str, RGK[k][2])) + "]" if k in RGK else "[]" for k in range(16)) + "])")
W("theorem hR : rgOk REG = true := by decide +kernel\n")
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
CH = int(os.environ.get("CH", "0"))
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
        ax = get(pos + 1, 5)
        if ax < Q:
            m = (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
            A = build(W_, l2, uA, dict(cons2), pos + 6); B = build(W_, lB, u2, dict(cons2), A[3])
        else:
            t = SUMS[ax - Q]; lo, hi = cons2[t]; m = (lo + hi) >> 1
            cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
            A = build(W_, l2, u2, cA, pos + 6); B = build(W_, l2, u2, cB, A[3])
        return ("split", st0, pos, B[3], A[4] + B[4], (ax, kstate(l2, u2, cons2), A, B))
    if u2[Q - 1] < l2[0]: return ("leaf", st0, pos, pos + 1, 1, None)
    raise RuntimeError("leaf payload lengths are taken from the walk theorem")
def leafend(W_, pos, nACT):
    """a minorant leaf's end (fixed-width layout)"""
    p_ = pos + 2
    for _ in range(nACT):
        k = (W_ >> p_) & 3; p_ += 2 + (7 if k >= 1 else 0) + (7 if k == 3 else 0) + (8 if k >= 2 else 0)
    while (W_ >> p_) & 1: p_ += 1 + 5 + 1 + 12
    return p_ + 1
NACT = sum(1 for a in aN if a > 0)
def build2(W_, l, u, cons, pos):
    st0 = kstate(l, u, cons)
    r_ = tz.t1(l, u, dict(cons), Q)
    if r_ is None: return ("empty", st0, pos, pos, 0, None)
    l2, u2, cons2, I = r_
    cons2 = {t: tuple(v) for t, v in cons2.items()}
    if (W_ >> pos) & 1:
        ax = (W_ >> (pos + 1)) & 31
        if ax < Q:
            m = (l2[ax] + u2[ax]) >> 1; uA = list(u2); uA[ax] = m; lB = list(l2); lB[ax] = m
            A = build2(W_, l2, uA, dict(cons2), pos + 6); B = build2(W_, lB, u2, dict(cons2), A[3])
        else:
            t = SUMS[ax - Q]; lo, hi = cons2[t]; m = (lo + hi) >> 1
            cA = dict(cons2); cA[t] = (lo, m); cB = dict(cons2); cB[t] = (m, hi)
            A = build2(W_, l2, u2, cA, pos + 6); B = build2(W_, l2, u2, cB, A[3])
        return ("split", st0, pos, B[3], A[4] + B[4], (ax, kstate(l2, u2, cons2), A, B))
    if u2[Q - 1] < l2[0]: return ("leaf", st0, pos, pos + 1, 1, None)
    return ("leaf", st0, pos, leafend(W_, pos, NACT), 1, None)
def sts(v): return "⟨" + ", ".join(map(str, v)) + "⟩"
STV = [x for r in range(Q) for x in (f"l{r}", f"u{r}")] + [x for (i, j) in SUMS for x in (f"A{i}{j}", f"B{i}{j}")] + ["M"]
nchunk = [0, 0]
def emit_chunk(n, nd, sx):
    """the theorem covering node nd, whose incoming state is the Lean term sx; returns its name"""
    name = f"cc{n}_{nchunk[0]}"; nchunk[0] += 1
    kind, st0, pos, end, nl, ex = nd
    if kind != "split" or nl <= CH or CH == 0:
        W(f"""theorem w{name} : U (walk TOP BK TOPD BKD PT REG WB{n} {FUEL} {pos + 1}) {sx} = {end + 1} := by
  decide +kernel
theorem {name} : Covered (toCl {sx}) :=
  covered_of_walkP lbS lbD ptS hR WB{n} {FUEL} {pos + 1} {end + 1} _ w{name} (by decide)""")
        return name
    nchunk[1] += 1
    ax, st1, A, B = ex
    tn = f"T{n}_{nchunk[1]}"
    W(f"def {tn} : St := {sts(st1)}")
    if ax < Q:
        m = A[1][2 * ax + 1]; assert B[1][2 * ax] == m
        sA = f"{{ {tn} with u{ax} := {m} }}"; sB = f"{{ {tn} with l{ax} := {m} }}"
        sp = f"gsplit_to {ax} (by decide)"
    else:
        k = ax - Q; i_, j_ = SUMS[k]; m = A[1][2 * Q + 2 * k + 1]; assert B[1][2 * Q + 2 * k] == m
        sA = f"{{ {tn} with B{i_}{j_} := {m} }}"; sB = f"{{ {tn} with A{i_}{j_} := {m} }}"
        sp = f"ssplit_to {k} (by decide)"
    a = emit_chunk(n, A, f"({sA})"); b = emit_chunk(n, B, f"({sB})")
    W(f"""theorem {name} : Covered (toCl {sx}) :=
  t1_to (t := {tn}) (by decide +kernel) ({sp} (sA := {sA}) (sB := {sB}) rfl rfl {a} {b})""")
    return name
names = []
for n, wk in enumerate(D["walks"]):
    tup = wk["root"]; box = wk["cell"]
    assert [tuple(box[r]) for r in range(Q)] == [bads[r][tup[r]] for r in range(Q)], (n, tup)
    W_ = int(wk["hex"], 16)
    bits = W_ << 1
    idx = ", ".join(map(str, tup))
    W(f"def WB{n} : ℕ := {hex(bits)}")
    tree = build2(W_, [c[0] for c in box], [c[1] for c in box], {}, 0)
    assert tree[3] == wk["nbits"], (n, tree[3], wk["nbits"])
    top = emit_chunk(n, tree, sts(tree[1]))
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
  f"  exact run{Q} _ _ _ _ _ _ _ " + " ".join(f"(l{r} ▸ h {r} (by norm_num))" for r in range(Q)) + "\n")
W(f"""/-- the half-space certificate on every point with nonnegative gaps -/
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
txt = "\n".join(out)
P = os.path.join(HERE, "..", ROOT, "AMW", f"{NAME}Data.lean")
open(P, "w").write(txt)
print(P, "bytes", len(txt.encode()), "walks", len(D["walks"]), "bads", [len(b) for b in bads], "point blocks", len(PB3))
