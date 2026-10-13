#!/usr/bin/env python3
"""(bridge-port) Polytope-cell instance layer with mvt-engine's canonical-Huffman walk (bench/eight/am8/HUFF.md); the
fixed-width predecessor is genpcell2.py.  Emits ROOT/AMW/{NAME}.lean (or $PCOUT/{NAME}.lean).

The kernel walk keeps the curried state (gap bounds l_r u_r, then pair bounds A_t B_t in pair order, then the mask M).  The
propositions see it through a structure `St` and the generic cell `toCl s : Cl` (four lists); every split, tightening
pass and multiplier entry is proved once in PCellGen, the leaf in PCellLeaf, the root in PCellRoot.  The Huffman decoder
(PCellHuff) carries no proof: the decoded fields feed a checked leaf or a split, sound for any value.

Walk (HUFF.md §2): split `[1][axis code]`, child A then child B; leaf `[0]`, reflected: nothing, else `[kind]`: minorant
(per active pair, its term code and lambda; then the multiplier list, Yq in QB bits) or Farkas (the list, Yq in QBF bits);
a multiplier entry is `[1][c code][side][Yq]`, the list closed by `[0]`.

Usage: genpcell3.py ROOT NAME Q [--bench | --decode]
  Q = 3: toy weights and toy tables.  Q = 7: AMWIN (window json; weights aN, bN, cN of DELTA) or else AMT8's weights.
  --bench: definitions only, AMT8's box leaf as the leaf step.  --decode: definitions only, every minorant leaf's check
  replaced by `true`, the Farkas leaves checked (the golden-vector decode test; not a certificate).
Env: HT (tables json, HUFF.md §7), NR (2), QB (12), QBF (4), LB (from HT, else 8), SIGSH (14), CN (Q = 3), AMWIN, DELTA
(0.001)."""
import sys, os, json

ROOT, NAME, Q = sys.argv[1], sys.argv[2], int(sys.argv[3])
BENCH = "--bench" in sys.argv
DECODE = "--decode" in sys.argv
DEFS = BENCH or DECODE          # definitions only
NR = int(os.environ.get("NR", "2"))
QB = int(os.environ.get("QB", "12"))
QBF = int(os.environ.get("QBF", "4"))
YFUEL = 42                      # at most one entry per (constraint, side)
SIGSH = int(os.environ.get("SIGSH", "14"))
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [(i, j) for (i, j) in PAIRS if j - i >= 2]
NC = len(SUMS)
if Q == 3:
    BW = [31833, 58928, 31833]
    AW = {(0, 1): 16291486, (0, 2): 59631729, (0, 3): 100000000, (1, 2): 32082429, (1, 3): 59631729, (2, 3): 16291486}
    CN = int(os.environ.get("CN", "550000"))
elif Q == 7:
    BW = [31833, 58928, 69744, 83339, 69744, 58928, 31833]
    AL = [16291486, 0, 0, 100000000, 39006345, 100000000, 200000000, 32082429, 3747073, 59631729, 0, 121987310, 100000000,
          32723633, 96252927, 80736542, 0, 39006345, 37804904, 96252927, 59631729, 100000000, 32723633, 3747073, 0, 32082429, 0,
          16291486]
    AW = dict(zip(PAIRS, AL)); CN = 557992
    if os.environ.get("AMWIN"):
        JW = json.load(open(os.environ["AMWIN"]))
        AW = {t: int(JW["aN"][f"{t[0]},{t[1]}"]) for t in PAIRS}; BW = [int(x) for x in JW["bN"]]
        CN = int(JW["delta_" + os.environ.get("DELTA", "0.001")]["cN"])
else:
    raise SystemExit("Q = 3 or 7")
ACT = [t for t in PAIRS if AW[t] > 0]
NA = len(ACT)
SIG = max(1, (1024 * 1000000000 * 100000000) >> SIGSH)
CB = max(1, (NC - 1).bit_length())

# ---- the canonical tables (HUFF.md §3, §7): per table `cs` (count per length from 0) and `sy` (symbols in table order),
# 16-bit fields ----
def canon(lengths):
    return sorted(([s_, l_] for s_, l_ in lengths.items()), key=lambda e: (e[1], e[0]))
if os.environ.get("HT"):
    HTJ = json.load(open(os.environ["HT"]))
    TTAB = {tuple(map(int, k.split(","))): v for k, v in HTJ["term_tables"].items()}
    ATAB = HTJ["axis_table"]; CTAB = HTJ["c_table"]; LB = int(os.environ.get("LB", HTJ.get("LB", 8)))
    assert HTJ["sum_constraints_in_rank_order"] == [f"{i},{j}" for (i, j) in SUMS]
elif Q == 3:
    # toy tables: one-entry tables (length 0) on the adjacent pairs, two entries (constant, a PLO tangent) on the others
    TTAB = {t: ([[0, 0]] if t[1] - t[0] == 1 else canon({0: 1, 16384 + 33 * 128: 1})) for t in PAIRS}
    ATAB = canon({3: 1, 0: 3, 1: 3, 2: 3, 4: 4, 5: 4}); CTAB = canon({0: 1, 1: 2, 2: 2}); LB = int(os.environ.get("LB", "8"))
else:
    raise SystemExit("Q = 7 needs HT (the tables json)")
HLUT = int(os.environ.get("HLUT", "0"))     # lookup on the next HLUT bits (0: the canonical loop only)
def hlut(tab):
    """(kb, lut, complete): the 24-bit entries `symbol + 2^16 (length + 1)` indexed by the next kb bits in walk order"""
    mx = max(l_ for _, l_ in tab); kb = min(HLUT, mx); ent = [0] * (1 << kb); code = 0; prev = None
    for s_, l_ in tab:
        if l_ == 0: ent = [s_ + 65536]; break
        code = 0 if prev is None else (code + 1) << (l_ - prev); prev = l_
        if l_ > kb: continue
        v = sum(((code >> (l_ - 1 - j_)) & 1) << j_ for j_ in range(l_))
        for i_ in range(1 << kb):
            if i_ & ((1 << l_) - 1) == v: assert ent[i_] == 0; ent[i_] = s_ + ((l_ + 1) << 16)
    return kb, hex(sum(e_ << (24 * i_) for i_, e_ in enumerate(ent))), mx <= kb
def hdecT(nm_, tab, w, o):
    """the kernel decode of table `nm_` (constants HC/HS/HL) at bit `o` of `w`"""
    if not HLUT: return f"hdec HC{nm_} HS{nm_} {w} {o}"
    kb, _, full = hlut(tab)
    return f"hdecL {(1 << kb) - 1} HL{nm_} {'0 0' if full else f'HC{nm_} HS{nm_}'} {w} {o}"
def hdefs(nm_, tab):
    out_ = []
    if HLUT: out_.append(f"def HL{nm_} : ℕ := {hlut(tab)[1]}")
    if not (HLUT and hlut(tab)[2]): out_ += [f"def HC{nm_} : ℕ := {hpack(tab)[0]}", f"def HS{nm_} : ℕ := {hpack(tab)[1]}"]
    return "\n".join(out_)
def hpack(tab):
    mx = max(l_ for _, l_ in tab); cnt = [0] * (mx + 1)
    for _, l_ in tab: cnt[l_] += 1
    assert tab == canon(dict(tab)) and mx <= 32 and max(cnt) < 1 << 16 and all(s_ < 1 << 16 for s_, _ in tab)
    return hex(sum(c_ << (16 * k_) for k_, c_ in enumerate(cnt))), hex(sum(s_ << (16 * k_) for k_, (s_, _) in enumerate(tab)))

def nm(t): return f"{t[0]}{t[1]}"
def single(t): return t[1] - t[0] == 1
GS = [f"g{r}" for r in range(Q)]
STV = [x for r in range(Q) for x in (f"l{r}", f"u{r}")] + [x for t in SUMS for x in (f"A{nm(t)}", f"B{nm(t)}")] + ["M"]
NS = len(STV)
ST = " ".join(STV)
def st(**kw): return " ".join(kw.get(v, v) for v in STV)
import re as _re
# short binder names for the kernel definitions (letters except k, p, q, then two-letter names)
_SN = [c for c in "abcdefghijlmnorstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"] + ["a" + c for c in "abcdefghijlmnorstuvwxyz"]
SHORT = dict(zip(STV, _SN))
_SRE = _re.compile(r"\b(" + "|".join(sorted(STV, key=len, reverse=True)) + r")\b")
def short(txt): return _SRE.sub(lambda m: SHORT[m.group(1)], txt)
def sv(v): return f"s.{v}"

# ---- kernel sums (left-nested Nat.add), and the same in infix (the simp normal form) ----
def nadd(xs):
    s = xs[0]
    for x in xs[1:]: s = f"Nat.add {p(s)} {p(x)}"
    return s
def p(s): return s if " " not in s else f"({s})"
def sl(t, pre=""): return nadd([f"{pre}l{r}" for r in range(*t)])
def su(t, pre=""): return nadd([f"{pre}u{r}" for r in range(*t)])
def slI(t, pre=""): return " + ".join(f"{pre}l{r}" for r in range(*t))
def suI(t, pre=""): return " + ".join(f"{pre}u{r}" for r in range(*t))
def Le(t, pre=""): return f"{pre}l{t[0]}" if single(t) else f"(nmax {pre}A{nm(t)} {p(sl(t, pre))})"
def Ue(t, pre=""): return f"{pre}u{t[0]}" if single(t) else f"(nmin {pre}B{nm(t)} {p(su(t, pre))})"
def LeI(t, pre=""): return f"{pre}l{t[0]}" if single(t) else f"(nmax {pre}A{nm(t)} ({slI(t, pre)}))"
def UeI(t, pre=""): return f"{pre}u{t[0]}" if single(t) else f"(nmin {pre}B{nm(t)} ({suI(t, pre)}))"
def gsI(t): return " + ".join(f"g {r}" for r in range(*t))

out = []
W = out.append
imp = "import AMW.PCellHuff\n" + ("import AMW.AMT8Inst\n" if BENCH else "")
W(f"""{imp}
/-! ###### polytope cells for Q = {Q}: the instance layer (bridge-port, generated by amg/genpcell3.py)

Kernel functions unrolled on the curried state ({2 * Q} gap and {2 * NC} pair bounds, the mask); every proof is a link to
the generic layer `AMW.PCellGen` through `toCl : St → Cl`.  The walk is mvt-engine's canonical-Huffman encoding (HUFF.md),
decoded by `AMW.PCellHuff`.{chr(10) + "DECODE TEST: every minorant leaf's check is replaced by `true` (the Farkas leaves are checked); this file" + chr(10) + "certifies nothing." + chr(10) if DECODE else "  "}Engine, tables and per-term minorants: mvt-engine's MinCore on the AM
engine (pyramid oracle adapted from five-point-pyramid-2 by typh, convex basins after six-point-convex-basins-2 by typh,
Apache-2.0). ###### -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace AMW.Cert.{NAME}

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

def cN : ℕ := {CN}
/-- the multiplier quantum: `Y = SIG · Yq`, `Yq < 2^{QB}` (`2^-{SIGSH}` per unit g) -/
def SIG : ℕ := {SIG}

/-- the non-adjacent pairs, in pair order -/
def PR : List (ℕ × ℕ) := [{", ".join(f"({i}, {j})" for (i, j) in SUMS)}]
theorem hPR : PRok {Q} PR := by decide
/-- the gap weights and the terms `(i, j, a, k)` of the functional `Fg` (units 1/SA) -/
def BS : List ℕ := [{", ".join(str(x) for x in BW)}]
def TS : List Term := [{", ".join(f"({i}, {j}, {AW[(i, j)]}, {SUMS.index((i, j)) if j - i >= 2 else 0})" for (i, j) in ACT)}]
theorem hTS : TSok {Q} PR TS := by decide

/-- the canonical tables (HUFF.md §3): per table the count of each code length from 0, and the symbols in table order
(16-bit fields); a term's symbol is `κ · 2^14 + j1 · 2^7 + j2`, the axis `0 … {Q - 1}` a gap, `{Q} …` a pair (pair order),
the multiplier's `c` the pair's rank -/
""" + "\n".join(hdefs(nm(t), TTAB[t]) for t in ACT) + "\n" + hdefs("A", ATAB) + "\n" + hdefs("C", CTAB) + f"""

abbrev Covered : Cl → Prop := CovBy {Q} PR (Pg cN {Q} BS TS)

/-- the kernel state -/
structure St where
  ({ST} : ℕ)

def toCl (s : St) : Cl :=
  ⟨[{", ".join(f"s.l{r}" for r in range(Q))}], [{", ".join(f"s.u{r}" for r in range(Q))}],
   [{", ".join(f"s.A{nm(t)}" for t in SUMS)}], [{", ".join(f"s.B{nm(t)}" for t in SUMS)}]⟩
def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨{", ".join([x for r in range(Q) for x in (f"c.L.getD {r} 0", f"c.U.getD {r} 0")] + [x for k in range(NC) for x in (f"c.A.getD {k} 0", f"c.B.getD {k} 0")])}, m⟩

theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = {Q}) (h2 : c.U.length = {Q}) (h3 : c.A.length = {NC}) (h4 : c.B.length = {NC}) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]

abbrev ST : Type := {" → ".join(["ℕ"] * (NS + 1))}
/-- a continuation applied to a state -/
def U (k : ST) (s : St) : ℕ := k {" ".join(sv(v) for v in STV)}
def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
def zK : ST := fun {" ".join(["_"] * NS)} => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h

theorem ofCl_ok {{k : ST}} (hk : CovK k) {{c : Cl}} {{m : ℕ}} (h1 : c.L.length = {Q}) (h2 : c.U.length = {Q}) (h3 : c.A.length = {NC})
    (h4 : c.B.length = {NC}) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h

/-- a split node's two children (`cA` from `pos`, the bit after the axis code, then `cB`) cover the cell when the split lemma does -/
theorem sp_ok {{ih : WF}} (hih : WalkOK ih) {{s : St}} {{cA cB : Cl}} {{pos mA mB : ℕ}}
    (hc : Covered cA → Covered cB → Covered (toCl s))
    (h : Bool.rec (motive := fun _ => ℕ) (U (ih (U (ih pos) (ofCl cA mA))) (ofCl cB mB)) 0
      (Nat.beq (U (ih pos) (ofCl cA mA)) 0) ≠ 0)
    (hA : cA.L.length = {Q} ∧ cA.U.length = {Q} ∧ cA.A.length = {NC} ∧ cA.B.length = {NC})
    (hB : cB.L.length = {Q} ∧ cB.U.length = {Q} ∧ cB.A.length = {NC} ∧ cB.B.length = {NC}) : Covered (toCl s) := by
  cases hp : Nat.beq (U (ih pos) (ofCl cA mA)) 0
  · rw [hp] at h
    exact hc (ofCl_ok (hih _) hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 fun h0 => by rw [h0] at hp; exact absurd hp (by decide))
      (ofCl_ok (hih _) hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 h)
  · rw [hp] at h; exact absurd rfl h
""")

# ---- splits ----
W("-- (2) split nodes: gap r at the midpoint of [l_r, u_r]; pair t at the midpoint of its effective range")
axes = []
for r in range(Q):
    q = f"Nat.shiftRight (Nat.add l{r} u{r}) 1"
    W(short(f"""def gsplit{r} (ih : WF) (pos {ST} : ℕ) : ℕ :=
  forceR ({q}) fun q => let p := ih pos {st(**{f"u{r}": "q"})}
  Bool.rec (motive := fun _ => ℕ) (ih p {st(**{f"l{r}": "q"})}) 0 (Nat.beq p 0)"""))
    axes.append((f"gsplit{r}", f"(cov_gmid {r} (n := {Q}) rfl rfl (by decide))"))
for ci, t in enumerate(SUMS):
    n = nm(t)
    q = f"Nat.shiftRight (Nat.add (nmax A{n} {p(sl(t))}) (nmin B{n} {p(su(t))})) 1"
    W(short(f"""def ssplit{n} (ih : WF) (pos {ST} : ℕ) : ℕ :=
  forceR ({q}) fun q => let p := ih pos {st(**{f"B{n}": "q", "M": f"(Nat.lor M {1 << ci})"})}
  Bool.rec (motive := fun _ => ℕ) (ih p {st(**{f"A{n}": "q", "M": f"(Nat.lor M {1 << ci})"})}) 0 (Nat.beq p 0)"""))
    axes.append((f"ssplit{n}", f"(cov_smid {ci} (n := {NC}) rfl rfl (by decide))"))
if not DEFS:
    W(f"""section
variable {{ih : WF}} (hih : WalkOK ih) (pos : ℕ)
include hih
set_option hygiene false in
/-- a split node's link: unfold, then the generic midpoint split -/
macro "pc_spl " n:ident c:term : term =>
  `(fun s h => by simp only [U, $n:ident, forceR_eq] at h; exact sp_ok hih (pos := pos) $c h ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩)
""" + "\n".join(f"theorem {a}_ok : CovK ({a} ih pos) := pc_spl {a} {cov}" for (a, cov) in axes) + "\nend")
ax = "zK"
for k in reversed(range(len(axes))):
    ax = f"Bool.rec (motive := fun _ => ST) ({ax}) ({axes[k][0]} ih pos) (Nat.beq ax {k})"
W(f"""/-- a split node: axis `0 … {Q - 1}` a gap, `{Q} … {Q + NC - 1}` a pair (pair order) -/
def splitAx (ih : WF) (pos ax : ℕ) : ST :=
  {ax}""")
if not DEFS:
    pf = "zK_ok"
    for k in reversed(range(len(axes))):
        pf = f"brec_dep (fun _ => {pf}) (fun _ => {axes[k][0]}_ok hih pos)"
    W(f"""theorem splitAx_ok {{ih : WF}} (hih : WalkOK ih) (pos ax : ℕ) : CovK (splitAx ih pos ax) :=
  {pf}""")

# ---- bound tightening ----
W("-- (5) bound tightening, one pass per pair (Jacobi), then the continuation; `pos` when the effective range is empty")
for ci, t in enumerate(SUMS):
    n = nm(t); rs = list(range(*t))
    body = "".join(f"fb1 l{r} u{r} Le su Ue sl fun l{r}' u{r}' => " for r in rs)
    W(short(f"""def fb{n} (pos : ℕ) (k : ST) ({ST} : ℕ) : ℕ :=
  forceR ({sl(t)}) fun sl => forceR ({su(t)}) fun su => forceR (nmax A{n} sl) fun Le => forceR (nmin B{n} su) fun Ue =>
  Bool.rec (motive := fun _ => ℕ) ({body}k {st(**{v: v + "'" for r in rs for v in (f"l{r}", f"u{r}")})}) pos (Nat.blt Ue Le)"""))
def dtree(lo, b, leaf, mk):
    """the dispatch on the constraint index `c` (bits b-1 … 0), the indices `lo …` below; `leaf(i)` for i < NC"""
    if lo >= NC: return leaf(None)
    if b == 0: return leaf(lo)
    return mk(dtree(lo, b - 1, leaf, mk), dtree(lo + (1 << (b - 1)), b - 1, leaf, mk), b - 1)
DTK = dtree(0, CB, lambda i: f"fb{nm(SUMS[i])} pos k" if i is not None else "k",
            lambda a, b, j: f"Bool.rec (motive := fun _ => ST) ({a}) ({b}) (Nat.beq (Nat.land (Nat.shiftRight c {j}) 1) 1)")
rnds = "k"
for _ in range(NR): rnds = f"fbL pos ({rnds}) {NC} M"
W(f"""/-- one tightening pass of pair `c` -/
def fbD (c pos : ℕ) (k : ST) : ST :=
  {DTK}
/-- the passes of the pairs in the mask `m` (its set bits, lowest first: pair order), at most `fuel` of them -/
def fbL (pos : ℕ) (k : ST) (fuel : ℕ) : ℕ → ST :=
  Nat.rec (motive := fun _ => ℕ → ST) (fun _ => k)
    (fun _ ih m => Bool.rec (motive := fun _ => ST)
      (forceT (Nat.land m (Nat.sub m 1)) fun m' => fbD (Nat.log2 (Nat.sub m m')) pos (ih m')) k (Nat.beq m 0)) fuel
/-- the tightening of a node: {NR} rounds over the pairs ever split (the mask `M`; the others cannot tighten) -/
def fbN (pos : ℕ) (k : ST) : ST := {short(f"fun {ST} => {rnds} {ST}")}""")
if not DEFS:
    W(f"""theorem fb_ok {{k : ST}} (hk : CovK k) {{t : ℕ}} (ht : t < {NC}) {{s : St}} {{pos : ℕ}}
    {{m : ℕ}} (h : Bool.rec (motive := fun _ => ℕ) (U k (ofCl (fbC PR (toCl s) t) m)) pos (femp PR (toCl s) t) ≠ 0) :
    Covered (toCl s) := by
  intro g hg
  obtain ⟨he, hg'⟩ := fb_gen hPR rfl rfl ht hg
  rw [he] at h
  exact ofCl_ok hk ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) rfl rfl h g hg'""")
    W(f"""section
variable {{pos : ℕ}} {{k : ST}} (hk : CovK k)
include hk
set_option hygiene false in
/-- a tightening pass's link: unfold, then the generic pass -/
macro "pc_fbl " n:ident t:num : term =>
  `(fun _ h => by simp only [U, $n:ident, fb1, forceR_eq] at h; exact fb_ok hk (t := $t) (by decide) h)
""" + "\n".join(f"theorem fb{nm(t)}_ok : CovK (fb{nm(t)} pos k) := pc_fbl fb{nm(t)} {ci}" for ci, t in enumerate(SUMS)) + "\nend")
    DTP = dtree(0, CB, lambda i: f"fb{nm(SUMS[i])}_ok hk" if i is not None else "hk",
                lambda a, b, j: f"brec_dep (fun _ => {a}) (fun _ => {b})")
    rp = "hk"; rq = "k"
    for _ in range(NR): rp = f"fbL_ok ({rp}) pos {NC} s.M"; rq = f"fbL pos ({rq}) {NC} s.M"
    W(f"""theorem fbD_ok {{k : ST}} (hk : CovK k) (c pos : ℕ) : CovK (fbD c pos k) :=
  {DTP}
theorem fbL_ok {{k : ST}} (hk : CovK k) (pos : ℕ) : ∀ fuel m, CovK (fbL pos k fuel m)
  | 0, _ => hk
  | n + 1, _ => brec_dep (fun _ => by rw [forceT_eq]; exact fbD_ok (fbL_ok hk pos n _) _ _) fun _ => hk
theorem fbN_U {{pos : ℕ}} {{k : ST}} (s : St) : U (fbN pos k) s = U ({rq}) s := by unfold U fbN; rfl
theorem fbN_ok {{pos : ℕ}} {{k : ST}} (hk : CovK k) : CovK (fbN pos k) := fun s h => {rp} s (fbN_U s ▸ h)""")

# ---- multipliers ----
PV = [f"P{r}" for r in range(Q)]; SV = [f"S{r}" for r in range(Q)]
YF = ["o"] + PV + SV + ["Cp", "Cm"]
def yk(**kw): return "⟨" + ", ".join(kw.get(f, f"y.{f}") for f in YF) + "⟩"
upd = {f"P{r}": f"Nat.add y.P{r} (Nat.mul Ylo (ind (inr {r} i j)))" for r in range(Q)}
upd.update({f"S{r}": f"Nat.add y.S{r} (Nat.mul Yhi (ind (inr {r} i j)))" for r in range(Q)})
upd["Cp"] = "Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))"
upd["Cm"] = "Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0)))"
W(f"""-- (3) multipliers (HUFF.md §5.2): entries `[1][c code][side][Yq: qb bits]`, closed by `[0]`
structure YA where
  ({" ".join(YF)} : ℕ)

def MulOK (s : St) (y : YA) : Prop :=
  MulOKg {Q} PR (toCl s) [{", ".join(f"y.P{r}" for r in range(Q))}] [{", ".join(f"y.S{r}" for r in range(Q))}] y.Cp y.Cm

def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) {yk(o="(Nat.add o 1)")}
    (forceT ({hdecT("C", CTAB, "w", "(Nat.add o 1)")}) fun cl => forceT (Nat.land cl 65535) fun c =>
     forceT (Nat.add (Nat.add o 1) (Nat.shiftRight cl 16)) fun o1 =>
     Bool.rec (motive := fun _ => YA) {yk(o="(Nat.add o1 (Nat.add qb 1))")}
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih {yk(o="(Nat.add o1 (Nat.add qb 1))", **{k: f"({v})" for k, v in upd.items()})})
      (Nat.blt c {NC}))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)

def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel""")
if not DEFS:
    W(f"""theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, {", ".join(["0"] * (len(YF) - 1))}⟩ := fun _ _ => by simp

theorem ystep_ok (s : St) (qb w : ℕ) {{ih : YA → YA}} (hih : ∀ y, MulOK s y → MulOK s (ih y)) (y : YA) (h : MulOK s y) :
    MulOK s (ystep (toCl s).L (toCl s).A (toCl s).B qb w ih y) := by
  unfold ystep
  simp only [forceT_eq]
  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => h) fun hc => hih _ (mul_step hPR rfl rfl h (Nat.blt_eq.mp hc) _ _)

theorem ydec_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOK s y → MulOK s (ydec (toCl s).L (toCl s).A (toCl s).B qb w fuel y)
  | 0, _, h => h
  | n + 1, y, h => ystep_ok s qb w (ydec_ok s qb w n) y h""")

# ---- the leaf check: unrolled in mcheckG's exact shape (the bridge `mcheckP_ok` is definitional) ----
def F(t): return f"k{nm(t)} m{nm(t)} p{nm(t)} r{nm(t)}"
FL = " ".join(F(t) for t in ACT)
def isumK(items):
    """`isum` unrolled: `Nat.add (… (Nat.add 0 x0) …) x_{n-1}`; a `None` item is a term the indicator drops (`+ 0`)"""
    acc = "0"
    for x in items:
        if x is None: continue
        acc = f"Nat.add {p(acc)} ({x})"
    return acc
def iallK(items):
    acc = "true"
    for x in items: acc = f"({acc}) &&ₖ ({x})"
    return acc
def L0K(t): return f"s.l{t[0]}" if single(t) else p(sl(t, "s."))
def inT(t, r): return t[0] <= r < t[1]
def NgK(r):
    ws = isumK([f"Nat.mul {AW[t]} (mwT k{nm(t)} m{nm(t)})" if inT(t, r) else None for t in ACT])
    ls = isumK([f"Nat.mul {AW[t]} (mslK f {F(t)})" if inT(t, r) else None for t in ACT])
    return f"Nat.sub (Nat.add (Nat.mul 2000000000 ({ws})) P{r}) (Nat.add (Nat.add (Nat.mul 1024000000000 {BW[r]}) ({ls})) S{r})"
boxK = iallK([f"Nat.ble s.l{r} s.u{r}" for r in range(Q)])
termK = iallK([f"mokT R tD bD f {Le(t, 's.')} {Ue(t, 's.')} {F(t)}" for t in ACT])
lhsK = (f"Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add ({isumK([f'Nat.mul {AW[t]} (mcK f false {L0K(t)} {F(t)})' for t in ACT])}) Cp) "
        f"({isumK([f'Nat.mul (Nat.sub s.u{r} s.l{r}) ({NgK(r)})' for r in range(Q)])})))")
rhsK = (f"Nat.add (Nat.add (Nat.mul 10240000000000 ({isumK([f'Nat.mul {BW[r]} s.l{r}' for r in range(Q)])})) "
        f"(Nat.mul 32768 ({isumK([f'Nat.mul {AW[t]} (mvK top bk f {Le(t, chr(115) + chr(46))} (uc {Le(t, chr(115) + chr(46))} {Ue(t, chr(115) + chr(46))}) {F(t)})' for t in ACT])}))) "
        f"(Nat.mul 10 (Nat.add ({isumK([f'Nat.mul {AW[t]} (mcK f true {L0K(t)} {F(t)})' for t in ACT])}) Cm))")
W(f"""/-- (3) the minorant leaf on the polytope cell (`mcheckG` unrolled): per term its kind, weight and points on its
effective range; the accumulated multipliers `P, S, Cp, Cm` -/
def mcheckP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (s : St)
    ({FL} : ℕ) ({" ".join(PV + SV)} Cp Cm : ℕ) : Bool :=
  (({boxK}) &&ₖ ({termK})) &&ₖ (Nat.ble ({lhsK}) ({rhsK}))""")
if not DEFS:
    W(f"""theorem mcheckP_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{f : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}} (s : St)
    ({FL} : ℕ) ({" ".join(PV + SV)} Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s {FL} {" ".join(PV + SV)} Cp Cm = true) :
    mcheckG top bk tD bD f R {Q} BS TS cN (toCl s) [{", ".join(f"(k{nm(t)}, m{nm(t)}, p{nm(t)}, r{nm(t)})" for t in ACT)}]
      [{", ".join(PV)}] [{", ".join(SV)}] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq] at h; exact h""")

# ---- the leaf decoder ----
dec = []
for t in SUMS:
    n = nm(t)
    dec.append(f"forceR {Le(t, 's.')} fun L{n} => forceR {Ue(t, 's.')} fun U{n} =>")
dec.append("forceR 0 fun o0 =>")
for qn, t in enumerate(ACT):
    n = nm(t); Lx = f"s.l{t[0]}" if single(t) else f"L{n}"; Ux = f"s.u{t[0]}" if single(t) else f"U{n}"
    dec.append(f"forceR ({hdecT(n, TTAB[t], 'w', f'o{qn}')}) fun h{n} => dec4S {LB} h{n} w o{qn} {Lx} {Ux} fun k{n} m{n} p{n} r{n} o{qn + 1} =>")
CHK = "y.o" if DECODE else f"""Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD (pt3 pb) R s {FL} {" ".join("y." + x for x in YF[1:])})"""
W(f"""/-- the polytope minorant leaf (HUFF.md §5): the payload length when the check passes, else `0` -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  """ + "\n  ".join(dec) + f"""
  (fun y : YA => {CHK})
  (ydec (toCl s).L (toCl s).A (toCl s).B {QB} w {YFUEL} ⟨o{NA}, {", ".join(["0"] * (len(YF) - 1))}⟩)""")
if not DEFS:
    W(f"""theorem mleafP_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  unfold mleafP at h
  simp only [dec4S, forceR_eq] at h
  exact mcheckG_sound (f := pt3 pb) hlb hD hpt hR hPR hTS (ydec_ok s {QB} w {YFUEL} _ (MulOK_zero s _)) (mcheckP_ok _ {" ".join(["_"] * (4 * NA + 2 * Q + 2))} (brec_ne h))""")

# ---- the walk ----
box = " ".join(f"l{r} u{r}" for r in range(Q))
if BENCH:
    W(f"""/-- (bench) the AMT8 box leaf on the gap bounds -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun {ST} => AMW.Cert.AMT8.leafStep top bk tD bD pb R pos w {box}""")
else:
    YZ = ", ".join(["0"] * len(YF))
    FCHK = f"""Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [{", ".join(f"y.P{r}" for r in range(Q))}] [{", ".join(f"y.S{r}" for r in range(Q))}] {Q})) y.Cm)"""
    W(f"""/-- (kind 8) the Farkas leaf (HUFF.md §6): the multiplier list only (`Yq` in {QBF} bits), accepted when the multiplier form
is negative on the whole box -/
def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => {FCHK})
  (ydec (toCl s).L (toCl s).A (toCl s).B {QBF} w {YFUEL} ⟨{YZ}⟩)

/-- a leaf (bit 0 clear): the reflected half-space (`u{Q - 1} < l0`, no further bits), else bit 1 the kind (minorant leaf, or
Farkas leaf) with its payload from bit 2 -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun {ST} => Bool.rec (motive := fun _ => ℕ)
    (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨{", ".join(STV)}⟩)
        (fleaf (Nat.shiftRight w 2) ⟨{", ".join(STV)}⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1) (Nat.blt u{Q - 1} l0)""")
    if not DEFS:
        W(f"""theorem fleaf_ok (w : ℕ) (s : St) (h : fleaf w s ≠ 0) : Covered (toCl s) :=
  farkas_cov (ydec_ok s {QBF} w {YFUEL} _ (MulOK_zero s 0)) (brec_ne h)

theorem leafStep_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (pos w : ℕ) :
    CovK (leafStep top bk tD bD pb R pos w) := by
  intro s h
  have h' : Bool.rec (motive := fun _ => ℕ) (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)
      (fleaf (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) (Nat.add pos 1) (Nat.blt s.u{Q - 1} s.l0) ≠ 0 := h
  cases hs : Nat.blt s.u{Q - 1} s.l0
  · rw [hs, forceR_eq] at h'
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h'; exact h' rfl
    · rw [hk] at h'; exact fleaf_ok _ s fun h0 => by rw [h0] at h'; exact h' rfl
  · intro g hg
    right
    have h1 : g {Q - 1} ≤ (s.u{Q - 1} : ℝ) / SC := (hg.1 {Q - 1} (by norm_num)).2
    have h2 : (s.l0 : ℝ) / SC ≤ g 0 := (hg.1 0 (by norm_num)).1
    have : (s.u{Q - 1} : ℝ) / SC < (s.l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast Nat.blt_eq.mp hs) SC_pos
    show g {Q - 1} < g 0
    linarith""")
W(f"""/-- a node: bit `pos` selects split (`[1]`, then the axis codeword; the children from the bit after it) or leaf (`[0]`) -/
def node (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos (Nat.shiftRight bits pos))
    (forceT ({hdecT("A", ATAB, "bits", "(Nat.add pos 1)")}) fun al => splitAx ih (Nat.add (Nat.add pos 1) (Nat.shiftRight al 16)) (Nat.land al 65535))
    (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1)

/-- the walk: every node is first tightened (an empty node ends there, no bits) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => fbN pos (node top bk tD bD pb R bits ih pos)) fuel""")
if not DEFS:
    W(f"""theorem forceT_cov {{x : ℕ}} {{k : ℕ → ST}} (h : CovK (k x)) : CovK (forceT x k) := by rw [forceT_eq]; exact h

theorem walk_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => fbN_ok (brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
      forceT_cov (splitAx_ok (walk_ok hlb hD hpt hR bits n) _ _))

theorem covered_of_walk {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) (bits fuel e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)

/-- the adjacent term of each gap (its index in `TS`) -/
def ADJ : List ℕ := [{", ".join(str(ACT.index((r, r + 1))) for r in range(Q))}]
theorem hADJ : ∀ r < {Q}, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide

/-- (root) the certificate on every point with nonnegative gaps, from the per-gap covers (`coverChk`) and the walks over
the root cells (`rootCl`: a bad segment per gap, pair bounds absent) -/
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < {Q}, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < {Q}, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < {Q}, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : {Q} * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < {Q}, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl {Q} {NC} W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < {Q}, 0 ≤ g r) → Pg cN {Q} BS TS g :=
  root_cover hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun

/-- the root: every pair bound absent (`A = 0`, `B = W ≥ Σ u`) -/
theorem covered_box (s : St) (W : ℕ) (hA : ∀ k < {NC}, (toCl s).A.getD k 0 = 0) (hB : ∀ k < {NC}, (toCl s).B.getD k 0 = W)
    (hW : sumR (toCl s).U 0 {Q} ≤ W) (h : Covered (toCl s)) (g : ℕ → ℝ) (hb : InBox {Q} (toCl s) g) : Pg cN {Q} BS TS g :=
  h g (incell_root hPR hA hB hW hb)""")
W(f"\nend AMW.Cert.{NAME}\n")
txt = "\n\n".join(out)
P = (os.path.join(os.environ["PCOUT"], f"{NAME}.lean") if os.environ.get("PCOUT")
     else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW", f"{NAME}.lean"))
open(P, "w").write(txt)
print(P, "bytes", len(txt.encode()), "pairs", len(PAIRS), "constraints", NC, "active terms", NA, "SIG", SIG,
      "table entries", sum(len(TTAB[t]) for t in ACT), len(ATAB), len(CTAB))
