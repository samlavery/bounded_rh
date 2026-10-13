#!/usr/bin/env python3
"""(mvt-engine) genpcell4.py (bridge-port's, copied 2026-10-03) with CLOSE=1: the exact closure (TZ.md §5,
rootR8/AMW/PCellClose.lean) in place of T1.  Each split computes both children's closed states inline (`cupd`: per child
the 43 candidates that can bind, `forceR` each), the walk does no node tightening, and `walk bits fuel := fun pos =>
tm (walkC bits fuel pos)` closes the root box once (`tm`), so `walk`, `walk_ok` and `covered_of_walk` keep their
names and signatures (make8pc.py's walk theorems are unchanged).  Without CLOSE the output is genpcell4's.
Output: ROOT is a path relative to bench/window (e.g. rootR8), or $PCOUT.

(bridge-port) Polytope-cell instance layer with the T1 node tightening and the Z tangent extension (mvt-engine's
bench/eight/am8/TZ.md) on the canonical-Huffman walk (HUFF.md); the FBBT predecessor is genpcell3.py.  Emits
ROOT/AMW/{NAME}.lean (or $PCOUT/{NAME}.lean).

T1 (every node, before anything else): the 28 pair intervals written into the bounds (`matC`), the 56 triples in TZ.md's
order (`triC`), the re-clip by the box sums (`matC` again, TZ.md step 5), then one emptiness test on all 28 slots.  Sum splits at the raw midpoint `(A + B) >> 1`.  The leaf's
tangent check tries the derivative read, then the zero-order extension on ZN = 8 pieces (`mokTZ`).  The mask field `M` is
kept in the state and unused.

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

ROOT, FNAME, Q = sys.argv[1], sys.argv[2], int(sys.argv[3])
NAME = FNAME[:-4] if FNAME.endswith("Inst") else FNAME      # namespace AMW.Cert.NAME, file FNAME.lean
BENCH = "--bench" in sys.argv
DECODE = "--decode" in sys.argv
NPROOF = "--nproof" in sys.argv  # definitions only, the real leaf check (cost variants)
DEFS = BENCH or DECODE or NPROOF          # definitions only
TCHKV = os.environ.get("TCHKV", "")       # bench: "noz" drops the Z alternative, "nod" both side conditions (unsound)
CLOSE = os.environ.get("CLOSE") == "1"   # the exact closure in place of T1 (TZ.md §5)
BSPLIT = os.environ.get("BSPLIT") == "1"  # (with CLOSE, DATA) split layout [1][axis 5][mode 1]; mode 1 cuts at the region boundary
MD = "md " if BSPLIT else ""
NOREFL = os.environ.get("NOREFL") == "1"  # (with CLOSE, DFAST=3) no mirror symmetry: every leaf is checked, statement PgL
DFAST = int(os.environ.get("DFAST", "0"))  # (bridge-port, PCDF/PCDZ) 1: the derivative reads with their covers forced
                                         # (cache-shared, same value); 2: the pyramid reads too; 3: and the coarse-first sides
CSH = int(os.environ.get("CSH", "3"))      # (DFAST=3) the coarse end: a multiple of 2^j, 2^j about 1/2^CSH of the side
NR = int(os.environ.get("NR", "2"))
QB = int(os.environ.get("QB", "12"))
QBF = int(os.environ.get("QBF", "4"))
ZN = int(os.environ.get("ZN", "8"))
YFUEL = 42                      # at most one entry per (constraint, side)
SIGSH = int(os.environ.get("SIGSH", "14"))
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [(i, j) for (i, j) in PAIRS if j - i >= 2]
NC = len(SUMS)
if Q == 3 and not os.environ.get("DATA"):
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
    if os.environ.get("DATA"):
        DJ = json.load(open(os.environ["DATA"]))
        assert DJ["pairs"] == [f"{i},{j}" for (i, j) in PAIRS]
        AW = dict(zip(PAIRS, [int(x) for x in DJ["aN"]])); BW = [int(x) for x in DJ["bN"]]; CN = int(DJ["cN"])
        SAV = int(DJ["SA"]); PRM = DJ["params"]
        assert PRM["SIGSH"] == SIGSH and PRM["QB"] == QB and PRM["ZEXT"] == ZN and PRM["JSH"] == 5 and PRM["PLO"] == 33
        assert bool(PRM.get("BSPLIT", 0)) == BSPLIT, "BSPLIT must match the DATA's split layout"
        if BSPLIT: BNDV = [int(z) for z in PRM["BND"]]; BMG = int(PRM["BMARG"]); assert BNDV == sorted(set(BNDV))
elif os.environ.get("DATA"):             # any Q from the certificate data (truncated windows: Q = k)
    DJ = json.load(open(os.environ["DATA"]))
    assert DJ["pairs"] == [f"{i},{j}" for (i, j) in PAIRS] and len(DJ["bN"]) == Q
    AW = dict(zip(PAIRS, [int(x) for x in DJ["aN"]])); BW = [int(x) for x in DJ["bN"]]; CN = int(DJ["cN"])
    SAV = int(DJ["SA"]); PRM = DJ["params"]
    assert PRM["SIGSH"] == SIGSH and PRM["QB"] == QB and PRM["ZEXT"] == ZN and PRM["JSH"] == 5 and PRM["PLO"] == 33
    assert bool(PRM.get("BSPLIT", 0)) == BSPLIT, "BSPLIT must match the DATA's split layout"
    assert (DJ["settings"].get("NOREFL") == "1") == NOREFL, "NOREFL must match the DATA"
    if BSPLIT: BNDV = [int(z) for z in PRM["BND"]]; BMG = int(PRM["BMARG"]); assert BNDV == sorted(set(BNDV))
else:
    raise SystemExit("Q = 3 or 7, or DATA")
assert not NOREFL or (CLOSE and DFAST == 3), "NOREFL needs CLOSE and DFAST=3 (PCellNoRefl.mcheckGX_soundL)"
ACT = [t for t in PAIRS if AW[t] > 0]
NA = len(ACT)
SAV = globals().get("SAV", 100000000)
SIG = max(1, (1024 * 1000000000 * SAV) >> SIGSH)
FIXED = os.environ.get("FIXED") == "1" or bool(os.environ.get("DATA"))   # mvt-engine's fixed-width DATA layout
if FIXED: QBF = QB
CB = 5 if FIXED else max(1, (NC - 1).bit_length())   # the DATA layout writes 5-bit constraint codes

# ---- the canonical tables (HUFF.md §3, §7): per table `cs` (count per length from 0) and `sy` (symbols in table order),
# 16-bit fields ----
def canon(lengths):
    return sorted(([s_, l_] for s_, l_ in lengths.items()), key=lambda e: (e[1], e[0]))
if FIXED:
    TTAB = {}; ATAB = []; CTAB = []; LB = int(os.environ.get("LB", "8"))
    if os.environ.get("DATA"): LB = int(PRM["LB"])
elif os.environ.get("HT"):
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
SUPPRESS = [False]
def W(x):
    if not SUPPRESS[0]: out.append(x)
# GENI=1 (with CLOSE, BSPLIT, DFAST=3, DATA): a list-evaluated instance for small certificates.  One generic split
# (`splitC`: the closure children by `cupd` on lists, any axis, proved once by `cov_gsplitQ`/`cov_ssplitQ`), the root
# box sums by `matC` on lists, and the leaf by the generic `mcheckGX` on a generically decoded term list; the unrolled
# per-axis splits and the unrolled leaf check are not written.  Bytes fall about tenfold; the kernel is slower per node.
GENI = os.environ.get("GENI") == "1"
GENL = os.environ.get("GENL", "1" if GENI else "0") == "1"   # the leaf generic too (GENL=0 keeps the unrolled leaf)
LMAC = "local " if os.environ.get("LMAC") == "1" else ""   # module-local proof macros (no clash when instances share a file)
# GENK (with GENL): the generic leaf decodes in continuation form through `dec4F` on forced effective ranges (`decK`), so
# every field is a literal before `mcheckGX` reads it; `decAll`'s pair form leaves the decode unevaluated and re-read
GENK = GENL and os.environ.get("GENK") == "1"
GDEF = ""
if os.environ.get("DATA"):
    gs_ = " ".join(f"g{r}" for r in range(Q))
    bt = " + ".join(f"({BW[r]} / (SA:ℝ)) * g{r}" for r in range(Q))
    at = " + ".join(f"({AW[(i, j)]} / (SA:ℝ)) * wfun ({' + '.join(f'g{r}' for r in range(i, j))})" for (i, j) in PAIRS)
    xs_ = ", ".join(f"x{r}" for r in range(Q)); xv_ = " ".join(f"x{r}" for r in range(Q))
    GDEF = f"""
def SA : ℕ := {SAV}

/-- the weighted functional on the gaps, in real form (pair weights `a_ij` and pressures `b_r` over `SA`) -/
def G ({gs_} : ℝ) : ℝ :=
  {bt}
    + {at}

/-- the integer functional `Fg` on a tuple of gaps is `SA · G` -/
theorem Fg_G ({xv_} : ℝ) : Fg {Q} BS TS (fun r => [{xs_}].getD r 0) = (SA : ℝ) * G {xv_} := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring
"""
imp = ("import AMW.PCellNoRefl\n" if NOREFL else "") + (("import AMW.PCellCloseB\n" if BSPLIT else "import AMW.PCellClose\n") if CLOSE else "import AMW.PCellT1\n") + (("import AMW.PCDZ\n" if DFAST == 3 else "import AMW.PCDF\n") if DFAST else "") + ("" if FIXED else "import AMW.PCellHuff\n") + ("import AMW.AMT8Inst\n" if BENCH else "") + ("import AMW.PCellGK\n" if GENK else "")
def slot_of(i, j): return i if j == i + 1 else Q + SUMS.index((i, j))
SLV = [slot_of(a, b) if a < b else 0 for a in range(Q + 1) for b in range(Q + 1)]
SLDEF = (f"""
/-- the slot of the pair `(a, b)`, `a < b`, at `a · {Q + 1} + b`: gap `a` when `b = a + 1`, else `{Q}` + the pair's rank -/
def SL : List ℕ := [{", ".join(map(str, SLV))}]
theorem hSL : SLok {Q} PR SL := by decide
""" + (f"""
/-- the convex-region boundaries, sorted (the boundary split cuts at the one nearest the midpoint, ≥ BMARG = {BMG} inside) -/
def BND : List ℕ := [{", ".join(map(str, BNDV))}]
""" if BSPLIT else "") if CLOSE else "")
W(f"""{imp}
/-! ###### polytope cells for Q = {Q}: {"the instance layer with the exact closure and Z" + chr(10) + "(instance layer: bridge-port, amg/genpcell4.py; the closure splits, the closure walk and its chunk lemmas: mvt-engine," + chr(10) + "eight/am8/genpcellC.py, TZ.md §5)" if CLOSE else "the instance layer with T1 and Z (bridge-port, generated by amg/genpcell4.py)"}

Kernel functions unrolled on the curried state ({2 * Q} gap and {2 * NC} pair bounds, the mask); every proof is a link to
the generic layer `AMW.PCellGen` through `toCl : St → Cl`.  {"The walk is mvt-engine's fixed-width DATA layout (emit8pz.py)." if FIXED else "The walk is mvt-engine's canonical-Huffman encoding (HUFF.md), decoded by `AMW.PCellHuff`."}{chr(10) + "DECODE TEST: every minorant leaf's check is replaced by `true` (the Farkas leaves are checked); this file" + chr(10) + "certifies nothing." + chr(10) if DECODE else chr(10)}Engine, tables and per-term minorants: mvt-engine's MinCore on the AM
engine (pyramid oracle adapted from five-point-pyramid-2 by typh, Apache-2.0). ###### -/

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
{SLDEF}{GDEF}
/-- the canonical tables (HUFF.md §3): per table the count of each code length from 0, and the symbols in table order
(16-bit fields); a term's symbol is `κ · 2^14 + j1 · 2^7 + j2`, the axis `0 … {Q - 1}` a gap, `{Q} …` a pair (pair order),
the multiplier's `c` the pair's rank -/
""" + ("-- (fixed-width fields: no tables)" if FIXED else "\n".join(hdefs(nm(t), TTAB[t]) for t in ACT) + "\n" + hdefs("A", ATAB) + "\n" + hdefs("C", CTAB)) + f"""

abbrev Covered : Cl → Prop := CovBy {Q} PR ({"PgL" if NOREFL else "Pg"} cN {Q} BS TS)

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
W("-- (2) split nodes: gap r at the midpoint of [l_r, u_r]; pair t at the midpoint of its (persisted) bounds")
axes = []
def slotf(sl_):
    """the state fields (lo, hi) of slot sl_: gap sl_ < Q, else pair SUMS[sl_ - Q]"""
    return (f"l{sl_}", f"u{sl_}") if sl_ < Q else (f"A{nm(SUMS[sl_ - Q])}", f"B{nm(SUMS[sl_ - Q])}")
def sIJ(d): return (d, d + 1) if d < Q else SUMS[d - Q]
def cupd_new(F, s, t):
    """PCellClose.cupd on the child cell F (field -> its expression), edge s -> t, evaluated symbolically in the shape the
    generic definition reduces to: {field: new expression} for the bounds that get a candidate (the others are kept)"""
    def legP(x, y): return F[slotf(slot_of(x, y))[1]] if x < y else None
    def legN(x, y): return F[slotf(slot_of(y, x))[0]] if y < x else None
    def oadd(a_, b_): return b_ if a_ is None else (a_ if b_ is None else f"Nat.add {p(a_)} {p(b_)}")
    def path(leg, a_, b_): return oadd(oadd(leg(a_, s), leg(s, t)), leg(t, b_))
    def csub(P_, N_): return None if P_ is None else (P_ if N_ is None else f"Nat.sub {p(P_)} {p(N_)}")
    new = {}
    for d in range(Q + NC):
        a_, b_ = sIJ(d); lo, hi = slotf(d)
        if not (a_ == s or b_ == t):
            cl = csub(path(legN, b_, a_), path(legP, b_, a_))
            if cl is not None: new[lo] = f"nmax {p(F[lo])} {p(cl)}"
        if not (b_ == s or a_ == t):
            ch = csub(path(legP, a_, b_), path(legN, a_, b_))
            if ch is not None: new[hi] = f"nmin {p(F[hi])} {p(ch)}"
    return new
def cchild(fld, s, t, tag):
    """a child of a split: the split field `fld` := q, then the closure update; (forceR lines, state arguments, #candidates)"""
    F = {v: v for v in STV}; F[fld] = "q"
    new = cupd_new(F, s, t); lines = []; upd = {fld: "q"}
    for i_, (f_, ex) in enumerate(new.items()):
        lines.append(f"let k{tag}{i_} := {ex};" if LETC else f"forceR ({ex}) fun k{tag}{i_} =>"); upd[f_] = f"k{tag}{i_}"
    return lines, st(**upd), len(new)
SUPPRESS[0] = GENI
# LETC=1: the split's midpoint and candidates as `let` (zeta-reducible, so the link needs no `forceR_eq` rewriting and its
# proof term stays small); else `forceR` (strict, but the link's `simp … forceR_eq` proof is quadratic in the chain)
LETC = os.environ.get("LETC") == "1"
NCAND = []
if CLOSE:
    def csplit(name, qx, fA, eA, fB, eB):
        lA, sA, nA = cchild(fA, *eA, "a"); lB, sB, nB = cchild(fB, *eB, "b"); NCAND.extend([nA, nB])
        W(short(f"""def {name} (ih : WF) ({MD}pos {ST} : ℕ) : ℕ :=
  {f"let q := {qx};" if LETC else f"forceR ({qx}) fun q =>"}
  """ + "\n  ".join(lA) + f"""
  let p := ih pos {sA}
  Bool.rec (motive := fun _ => ℕ) (""" + "\n    ".join(lB) + f"""
    ih p {sB}) 0 (Nat.beq p 0)"""))
    for r in range(Q):
        qx = f"Nat.shiftRight (Nat.add l{r} u{r}) 1"
        if BSPLIT: qx = f"Bool.rec (motive := fun _ => ℕ) ({qx}) (bcutL BND {BMG} l{r} u{r}) (Nat.beq md 1)"
        csplit(f"gsplit{r}", qx, f"u{r}", (r, r + 1), f"l{r}", (r + 1, r))
        axes.append((f"gsplit{r}", f"(cov_gsplitQ hSL hPR {r} (qB BND {BMG} (toCl s) {r} md) rfl rfl (by decide))" if BSPLIT else
                     f"(cov_gmidC hSL hPR {r} rfl rfl (by decide))"))
    for ci, t in enumerate(SUMS):
        n = nm(t)
        qx = f"Nat.shiftRight (Nat.add A{n} B{n}) 1"
        if BSPLIT: qx = f"Bool.rec (motive := fun _ => ℕ) ({qx}) (bcutL BND {BMG} A{n} B{n}) (Nat.beq md 1)"
        csplit(f"ssplit{n}", qx, f"B{n}", t, f"A{n}", (t[1], t[0]))
        axes.append((f"ssplit{n}", f"(cov_ssplitQ hSL hPR {ci} (qBr BND {BMG} (toCl s) {ci} md) rfl rfl (by decide))" if BSPLIT else
                     f"(cov_rmidC hSL hPR {ci} rfl rfl (by decide))"))
for r in ([] if CLOSE else range(Q)):
    q = f"Nat.shiftRight (Nat.add l{r} u{r}) 1"
    W(short(f"""def gsplit{r} (ih : WF) (pos {ST} : ℕ) : ℕ :=
  forceR ({q}) fun q => let p := ih pos {st(**{f"u{r}": "q"})}
  Bool.rec (motive := fun _ => ℕ) (ih p {st(**{f"l{r}": "q"})}) 0 (Nat.beq p 0)"""))
    axes.append((f"gsplit{r}", f"(cov_gmid {r} (n := {Q}) rfl rfl (by decide))"))
for ci, t in ([] if CLOSE else enumerate(SUMS)):
    n = nm(t)
    q = f"Nat.shiftRight (Nat.add A{n} B{n}) 1"
    W(short(f"""def ssplit{n} (ih : WF) (pos {ST} : ℕ) : ℕ :=
  forceR ({q}) fun q => let p := ih pos {st(**{f"B{n}": "q"})}
  Bool.rec (motive := fun _ => ℕ) (ih p {st(**{f"A{n}": "q"})}) 0 (Nat.beq p 0)"""))
    axes.append((f"ssplit{n}", f"(cov_rmid {ci} (n := {NC}) rfl rfl (by decide))"))
if not DEFS:
    W(f"""section
variable {{ih : WF}} (hih : WalkOK ih) ({MD}pos : ℕ)
include hih
set_option hygiene false in
/-- a split node's link: unfold, then the generic midpoint split -/
{LMAC}macro "pc_spl " n:ident c:term : term =>
  `(fun s h => by simp only [U, $n:ident{"" if CLOSE and LETC else ", forceR_eq"}] at h; exact sp_ok hih (pos := pos) $c h ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩)
""" + "\n".join(f"theorem {a}_ok : CovK ({a} ih {MD}pos) := pc_spl {a} {cov}" for (a, cov) in axes) + "\nend")
ax = "zK"
for k in reversed(range(len(axes))):
    ax = f"Bool.rec (motive := fun _ => ST) ({ax}) ({axes[k][0]} ih {MD}pos) (Nat.beq ax {k})"
W(f"""/-- a split node: axis `0 … {Q - 1}` a gap, `{Q} … {Q + NC - 1}` a pair (pair order) -/
def splitAx (ih : WF) ({MD}pos ax : ℕ) : ST :=
  {ax}""")
if not DEFS:
    pf = "zK_ok"
    for k in reversed(range(len(axes))):
        pf = f"brec_dep (fun _ => {pf}) (fun _ => {axes[k][0]}_ok hih {MD}pos)"
    W(f"""theorem splitAx_ok {{ih : WF}} (hih : WalkOK ih) ({MD}pos ax : ℕ) : CovK (splitAx ih {MD}pos ax) :=
  {pf}""")

SUPPRESS[0] = False
if GENI:
    assert CLOSE and BSPLIT and FIXED and DFAST == 3
    FLD = " ".join(STV)
    CLV = f"⟨[{', '.join(f'l{r}' for r in range(Q))}], [{', '.join(f'u{r}' for r in range(Q))}], [{', '.join(f'A{nm(t)}' for t in SUMS)}], [{', '.join(f'B{nm(t)}' for t in SUMS)}]⟩"
    W(f"""-- (2) the split, generic: axis `0 … {Q - 1}` a gap, `{Q} … {Q + NC - 1}` a pair; the cut by mode (`qB`/`qBr`), both children closed (`cupd`)
def splitC (ih : WF) (md pos ax : ℕ) (c : Cl) (M : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) 0
      (let p := U (ih pos) (ofCl (cupd {Q} PR SL ⟨c.L, c.U, c.A, c.B.set (Nat.sub ax {Q}) (qBr BND {BMG} c (Nat.sub ax {Q}) md)⟩
          (pI PR (Nat.sub ax {Q})) (pJ PR (Nat.sub ax {Q}))) M)
       Bool.rec (motive := fun _ => ℕ) (U (ih p) (ofCl (cupd {Q} PR SL ⟨c.L, c.U, c.A.set (Nat.sub ax {Q}) (qBr BND {BMG} c (Nat.sub ax {Q}) md), c.B⟩
          (pJ PR (Nat.sub ax {Q})) (pI PR (Nat.sub ax {Q}))) M)) 0 (Nat.beq p 0))
      (Nat.blt ax {Q + NC}))
    (let p := U (ih pos) (ofCl (cupd {Q} PR SL ⟨c.L, c.U.set ax (qB BND {BMG} c ax md), c.A, c.B⟩ ax (ax + 1)) M)
     Bool.rec (motive := fun _ => ℕ) (U (ih p) (ofCl (cupd {Q} PR SL ⟨c.L.set ax (qB BND {BMG} c ax md), c.U, c.A, c.B⟩ (ax + 1) ax) M)) 0 (Nat.beq p 0))
    (Nat.blt ax {Q})
/-- a split node -/
def splitAx (ih : WF) (md pos ax : ℕ) : ST := fun {FLD} => splitC ih md pos ax {CLV} M""")
    if not DEFS:
        W(f"""theorem splitAx_ok {{ih : WF}} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) := by
  intro s h
  have h' : splitC ih md pos ax (toCl s) s.M ≠ 0 := h
  unfold splitC at h'
  cases hq : Nat.blt ax {Q}
  · rw [hq] at h'
    cases hr : Nat.blt ax {Q + NC}
    · rw [hr] at h'; exact absurd rfl h'
    · rw [hr] at h'
      have hk : ax - {Q} < {NC} := by
        have h1 := Nat.blt_eq.mp hr; have h2 : ¬ ax < {Q} := fun e => absurd (Nat.blt_eq.mpr e) (by rw [hq]; decide)
        omega
      exact sp_ok hih (cov_ssplitQ hSL hPR (ax - {Q}) (qBr BND {BMG} (toCl s) (ax - {Q}) md) rfl rfl hk) h'
        (cupd_len _ _ _ _ _ _) (cupd_len _ _ _ _ _ _)
  · rw [hq] at h'
    exact sp_ok hih (cov_gsplitQ hSL hPR ax (qB BND {BMG} (toCl s) ax md) rfl rfl (Nat.blt_eq.mp hq)) h'
      (cupd_len _ _ _ _ _ _) (cupd_len _ _ _ _ _ _)""")
# ---- T1 (TZ.md §1) ----
def slotf(sl_):
    """the state fields (lo, hi) of slot sl_: gap sl_ < Q, else pair SUMS[sl_ - Q]"""
    return (f"l{sl_}", f"u{sl_}") if sl_ < Q else (f"A{nm(SUMS[sl_ - Q])}", f"B{nm(SUMS[sl_ - Q])}")
def slot_of(i, j): return i if j == i + 1 else Q + SUMS.index((i, j))
TRIS = [(slot_of(i, k), slot_of(k, j), slot_of(i, j), (i, k, j)) for i in range(Q + 1) for j in range(i + 2, Q + 1) for k in range(i + 1, j)]
if not CLOSE: W("-- (5) T1: the pair intervals, the 56 triples, the re-clip by the box sums (TZ.md §1.3, steps 2, 3, 5), then one emptiness test on all 28 slots (`pos` when empty)")
mat = []; upd = {}
for t in SUMS:
    n = nm(t)
    mat.append(f"forceR (nmax A{n} {p(sl(t))}) fun A{n}' => forceR (nmin B{n} {p(su(t))}) fun B{n}' =>")
    upd[f"A{n}"] = f"A{n}'"; upd[f"B{n}"] = f"B{n}'"
if CLOSE: W("-- (5) the root: the box sums written into the pair bounds (`matC`), once, which closes the root box (TZ.md §5)")
if GENI: W(f"""def tm (k : ST) : ST := fun {FLD} => U k (ofCl (matC PR {CLV}) M)""")
else: W(short(f"""def tm (k : ST) ({ST} : ℕ) : ℕ :=
  """ + "\n  ".join(mat) + f"""
  k {st(**upd)}"""))
if CLOSE and not DEFS:
    W(f"""theorem tm_ok {{k : ST}} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2""")
for ti, (sa, sb, sd, (i, k, j)) in ([] if CLOSE else enumerate(TRIS)):
    a0, a1 = slotf(sa); b0, b1 = slotf(sb); d0, d1 = slotf(sd)
    W(short(f"""def tr{ti} (k : ST) ({ST} : ℕ) : ℕ :=
  forceR (nmax {d0} (Nat.add {a0} {b0})) fun D0 => forceR (nmin {d1} (Nat.add {a1} {b1})) fun D1 =>
  forceR (nmax {a0} (Nat.sub D0 {b1})) fun A0 => forceR (nmin {a1} (Nat.sub D1 {b0})) fun A1 =>
  forceR (nmax {b0} (Nat.sub D0 A1)) fun B0 => forceR (nmin {b1} (Nat.sub D1 A0)) fun B1 =>
  k {st(**{d0: "D0", d1: "D1", a0: "A0", a1: "A1", b0: "B0", b1: "B1"})}"""))
gch = "false"
for r in range(Q): gch = f"({gch} || Nat.blt u{r} l{r})"
pch = "false"
for t in SUMS: pch = f"({pch} || Nat.blt B{nm(t)} A{nm(t)})"
if not CLOSE: W(short(f"""def te (pos : ℕ) (k : ST) ({ST} : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (k {ST}) pos ({gch} || {pch})"""))
chain = "tm (te pos k)"; T1P = "tm_ok (te_ok hk pos)"
for ti in reversed(range(len(TRIS))): chain = f"tr{ti} ({chain})"; T1P = f"tr{ti}_ok ({T1P})"
if not CLOSE: W(f"""/-- T1 at a node, then the continuation -/
def T1 (pos : ℕ) (k : ST) : ST := tm ({chain})""")
if not DEFS and not CLOSE:
    W(f"""theorem te_ok {{k : ST}} (hk : CovK k) (pos : ℕ) : CovK (te pos k) := fun s h g hg => by
  have h' : Bool.rec (motive := fun _ => ℕ) (U k s) pos (gempG (toCl s) {Q} || pempG (toCl s) {NC}) ≠ 0 := h
  rw [gemp_false hg {Q} le_rfl, pemp_false hg {NC} le_rfl] at h'
  exact hk s h' g hg

theorem tm_ok {{k : ST}} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2

/-- a triple's link: the kernel step is `triC` on the slots `a b d` -/
theorem tri_ok {{k : ST}} (hk : CovK k) {{a b d : ℕ}} (ht : TriOk {Q} PR a b d) {{s : St}}
    (h : U k (ofCl (triC {Q} (toCl s) a b d) s.M) ≠ 0) : Covered (toCl s) := fun g hg => by
  have hl : ClLen {Q} {NC} (triC {Q} (toCl s) a b d) := triC_len (Q := {Q}) (n := {NC}) (c := toCl s) ⟨rfl, rfl, rfl, rfl⟩ a b d
  exact ofCl_ok hk hl.1 hl.2.1 hl.2.2.1 hl.2.2.2 h g (tri_gen ht ⟨rfl, rfl, rfl, rfl⟩ hg).2
section
variable {{k : ST}} (hk : CovK k)
include hk
set_option hygiene false in
/-- a triple step's link: unfold, then the generic triple -/
{LMAC}macro "pc_trl " n:ident a:num b:num d:num : term =>
  `(fun _ h => by simp only [U, $n:ident, forceR_eq] at h; exact tri_ok hk (a := $a) (b := $b) (d := $d) (by decide) h)
""" + "\n".join(f"theorem tr{ti}_ok : CovK (tr{ti} k) := pc_trl tr{ti} {sa} {sb} {sd}" for ti, (sa, sb, sd, _) in enumerate(TRIS)) + f"""
end
theorem T1_ok {{pos : ℕ}} {{k : ST}} (hk : CovK k) : CovK (T1 pos k) :=
  tm_ok ({T1P})""")

# ---- multipliers ----
YC = (f"(forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) {(1 << CB) - 1}) fun c => forceT (Nat.add o {1 + CB}) fun o1 =>" if FIXED else
      f"""(forceT ({hdecT("C", CTAB, "w", "(Nat.add o 1)")}) fun cl => forceT (Nat.land cl 65535) fun c =>
     forceT (Nat.add (Nat.add o 1) (Nat.shiftRight cl 16)) fun o1 =>""")
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
    {YC}
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

SUPPRESS[0] = GENL
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
    for x in items: acc = f"Bool.rec (motive := fun _ => Bool) false ({x}) ({acc})"
    return acc
def L0K(t): return f"s.l{t[0]}" if single(t) else p(sl(t, "s."))
def inT(t, r): return t[0] <= r < t[1]
def NgK(r):
    ws = isumK([f"Nat.mul {AW[t]} (mwT k{nm(t)} m{nm(t)})" if inT(t, r) else None for t in ACT])
    ls = isumK([f"Nat.mul {AW[t]} (mslK f {F(t)})" if inT(t, r) else None for t in ACT])
    return f"Nat.sub (Nat.add (Nat.mul 2000000000 ({ws})) P{r}) (Nat.add (Nat.add (Nat.mul 1024000000000 {BW[r]}) ({ls})) S{r})"
boxK = iallK([f"Nat.ble s.l{r} s.u{r}" for r in range(Q)])
MOKN = "mokTZb" if TCHKV else {0: "mokTZ", 1: "mokTZF", 2: "mokTZG", 3: "mokTZC"}[DFAST]
MVKN = "mvKF" if DFAST >= 2 else "mvK"
termK = iallK([f"{MOKN} R top bk tD bD f {ZN}{' ' + str(CSH) if DFAST == 3 and not TCHKV else ''} {Le(t, 's.')} {Ue(t, 's.')} {F(t)}" for t in ACT])
if TCHKV:
    zR = "true" if TCHKV in ("noz", "nod") else "zside top bk (lo32 X) (hi32 (hi32 X)) p (rgB R k) U n true"
    zL = "true" if TCHKV in ("noz", "nod") else "zside top bk (lo32 X) (lo32 (hi32 X)) p L (rgA R k) n false"
    dR = "true" if TCHKV == "nod" else "(Nat.ble 1 (lo32 EU) && Nat.ble 4000000000 (Nat.add (lo32 EU) (hi32 (hi32 X))))"
    dL = "true" if TCHKV == "nod" else "(Nat.ble 1 (hi32 ED) && Nat.ble 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X))))"
    W(f"""/-- (bench variant {TCHKV}, unsound) the tangent check with sides replaced -/
def tcheckZb (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (n L U p X EU ED : ℕ) : Bool :=
  forceB (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
    Nat.blt k 16 && Nat.ble (rgA R k) p && Nat.ble p (rgB R k) && Nat.ble L p && Nat.ble p U
      && Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))
      && (Nat.ble U (rgB R k) || {dR} || {zR})
      && (Nat.ble (rgA R k) L || {dL} || {zL})
def tcheckPZb (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (n L U p X EU ED : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tcheckZb R top bk n L U p X EU ED)
    (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) (Nat.beq L U && Nat.beq L p)
def mokTZb (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (zn L U k m p r : ℕ) : Bool :=
  Nat.ble m 1024 && ((Nat.beq (mw1 k m) 0 || tcheckPZb R top bk zn L U p (f p) (treadU R tD bD U p) (treadD R tD bD L p))
    && (Nat.beq (mw2 k m) 0 || tcheckPZb R top bk zn L U r (f r) (treadU R tD bD U r) (treadD R tD bD L r)))""")
lhsK = (f"Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add ({isumK([f'Nat.mul {AW[t]} (mcK f false {L0K(t)} {F(t)})' for t in ACT])}) Cp) "
        f"({isumK([f'Nat.mul (Nat.sub s.u{r} s.l{r}) ({NgK(r)})' for r in range(Q)])})))")
rhsK = (f"Nat.add (Nat.add (Nat.mul 10240000000000 ({isumK([f'Nat.mul {BW[r]} s.l{r}' for r in range(Q)])})) "
        f"(Nat.mul 32768 ({isumK([f'Nat.mul {AW[t]} ({MVKN} top bk f {Le(t, chr(115) + chr(46))} (uc {Le(t, chr(115) + chr(46))} {Ue(t, chr(115) + chr(46))}) {F(t)})' for t in ACT])}))) "
        f"(Nat.mul 10 (Nat.add ({isumK([f'Nat.mul {AW[t]} (mcK f true {L0K(t)} {F(t)})' for t in ACT])}) Cm))")
W(f"""/-- (3) the minorant leaf on the polytope cell (`mcheckG` unrolled): per term its kind, weight and points on its
effective range; the accumulated multipliers `P, S, Cp, Cm` -/
def mcheckP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (s : St)
    ({FL} : ℕ) ({" ".join(PV + SV)} Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.ble ({lhsK}) ({rhsK})) (Bool.rec (motive := fun _ => Bool) false ({termK}) ({boxK}))""")
if not DEFS:
    W(f"""theorem mcheckP_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{f : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}} (s : St)
    ({FL} : ℕ) ({" ".join(PV + SV)} Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s {FL} {" ".join(PV + SV)} Cp Cm = true) :
    {f"mcheckGX (mokTZC R top bk tD bD f {ZN} {CSH}) top bk f" if DFAST == 3 else f"mcheckGZ top bk tD bD f R {ZN}"} {Q} BS TS cN (toCl s) [{", ".join(f"(k{nm(t)}, m{nm(t)}, p{nm(t)}, r{nm(t)})" for t in ACT)}]
      [{", ".join(PV)}] [{", ".join(SV)}] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq{["", ", mokTZF_eq", ", mokTZG_eq, mvKF_eq", ", mvKF_eq"][DFAST]}] at h; exact h""")

# ---- the leaf decoder ----
dec = []
for t in SUMS:
    n = nm(t)
    dec.append(f"forceR {Le(t, 's.')} fun L{n} => forceR {Ue(t, 's.')} fun U{n} =>")
dec.append("forceR 0 fun o0 =>")
for qn, t in enumerate(ACT):
    n = nm(t); Lx = f"s.l{t[0]}" if single(t) else f"L{n}"; Ux = f"s.u{t[0]}" if single(t) else f"U{n}"
    if FIXED: dec.append(f"dec4F {LB} w o{qn} {Lx} {Ux} fun k{n} m{n} p{n} r{n} o{qn + 1} =>")
    else: dec.append(f"forceR ({hdecT(n, TTAB[t], 'w', f'o{qn}')}) fun h{n} => dec4S {LB} h{n} w o{qn} {Lx} {Ux} fun k{n} m{n} p{n} r{n} o{qn + 1} =>")
PTFN = "pb" if os.environ.get("DATA") else "(pt3 pb)"           # the point function: sparse (DATA) or the block table
PTSD = "PTF pb" if os.environ.get("DATA") else "PT3Sound pb"
CHK = "y.o" if DECODE else f"""Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD {PTFN} R s {FL} {" ".join("y." + x for x in YF[1:])})"""
W(f"""/-- the polytope minorant leaf (HUFF.md §5): the payload length when the check passes, else `0` -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  """ + "\n  ".join(dec) + f"""
  (fun y : YA => {CHK})
  (ydec (toCl s).L (toCl s).A (toCl s).B {QB} w {YFUEL} ⟨o{NA}, {", ".join(["0"] * (len(YF) - 1))}⟩)""")
if not DEFS:
    W(f"""theorem mleafP_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  unfold mleafP at h
  simp only [{"dec4F" if FIXED else "dec4S"}, forceR_eq] at h
  exact {("mcheckGX_soundL" if NOREFL else "mcheckGX_sound") + " (f := " + PTFN + ") (mtermTZC hlb hD hpt hR (by decide : 0 < " + str(ZN) + "))" if DFAST == 3 else "mcheckGZ_sound (f := " + PTFN + ") hlb hD hpt hR (by decide : 0 < " + str(ZN) + ")"} hPR hTS (ydec_ok s {QB} w {YFUEL} _ (MulOK_zero s _)) (mcheckP_ok _ {" ".join(["_"] * (4 * NA + 2 * Q + 2))} (brec_ne h))""")

SUPPRESS[0] = False
YLIT = f"""[{", ".join(f"y.P{r}" for r in range(Q))}] [{", ".join(f"y.S{r}" for r in range(Q))}] y.Cp y.Cm"""
if GENK:
    W(f"""/-- (generic, forced) every term's fields in term order, read by `dec4F` on its forced effective range and passed on
in continuation form, so each field is a literal before the leaf check reads it -/
def decK (w : ℕ) (c : Cl) : List ℕ → ℕ → (List Term → ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => ℕ → (List Term → ℕ → ℕ) → ℕ) (fun o k => k [] o)
    (fun n _ ih o k => forceR (eL TS c n) fun L => forceR (eU TS c n) fun U =>
      dec4F {LB} w o L U fun a m p r o' => ih o' fun FS o2 => k ((a, m, p, r) :: FS) o2)
/-- the minorant leaf (generic): forced decode, multipliers, then the kind-aware `mcheckGXK` with the coarse-first term
check -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  decK w (toCl s) (List.range TS.length) 0 fun FS o =>
    (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
      (mcheckGXK (mokTZC R top bk tD bD pb {ZN} {CSH}) top bk pb {Q} BS TS cN (toCl s) FS {YLIT}))
    (ydec (toCl s).L (toCl s).A (toCl s).B {QB} w {YFUEL} ⟨o, {", ".join(["0"] * (len(YF) - 1))}⟩)""")
    if not DEFS:
        W(f"""theorem decK_cons (w : ℕ) (c : Cl) (n : ℕ) (l : List ℕ) (o : ℕ) (k : List Term → ℕ → ℕ) :
    decK w c (n :: l) o k = forceR (eL TS c n) fun L => forceR (eU TS c n) fun U =>
      dec4F {LB} w o L U fun a m p r o' => decK w c l o' fun FS o2 => k ((a, m, p, r) :: FS) o2 := rfl
/-- the decoder needs no proof: whatever it decodes, an accepted leaf accepted some term list -/
theorem decK_ex (w : ℕ) (c : Cl) : ∀ (l : List ℕ) (o : ℕ) (k : List Term → ℕ → ℕ),
    decK w c l o k ≠ 0 → ∃ FS o', k FS o' ≠ 0
  | [], o, _, h => ⟨[], o, h⟩
  | n :: l, o, k, h => by
    rw [decK_cons] at h
    simp only [dec4F, forceR_eq] at h
    obtain ⟨_, _, h'⟩ := decK_ex w c l _ _ h
    exact ⟨_, _, h'⟩
theorem mleafP_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  obtain ⟨_, _, h'⟩ := decK_ex w (toCl s) _ _ _ h
  have h2 := brec_ne h'
  rw [mcheckGXK_eq] at h2
  exact {"mcheckGX_soundL" if NOREFL else "mcheckGX_sound"} (f := {PTFN}) (mtermTZC hlb hD hpt hR (by decide : 0 < {ZN})) hPR hTS
    (ydec_ok s {QB} w {YFUEL} _ (MulOK_zero s _)) h2""")
elif GENL:
    W(f"""/-- (generic) one term's fixed-width fields at bit `o`, as `dec4F` reads them: the term `(κ, m, p, r)` and the next bit -/
def fld4 (w o L U : ℕ) : Term × ℕ :=
  ((Nat.land (Nat.shiftRight w o) 3,
    Nat.shiftLeft (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0
        (Nat.land (Nat.shiftRight w (Nat.add o 16)) {(1 << LB) - 1}) (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 3))
      (Nat.land (Nat.shiftRight w (Nat.add o 9)) {(1 << LB) - 1}) (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 2)) {10 - LB},
    Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 127)) 0 (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 0),
    Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 9)) 127)) (Nat.beq (Nat.land (Nat.shiftRight w o) 3) 3)),
   Nat.add o (plenF {LB} (Nat.land (Nat.shiftRight w o) 3)))
/-- (generic) every term's fields in term order, each on its effective range -/
def decAll (w : ℕ) (c : Cl) : List ℕ → ℕ → List Term × ℕ :=
  List.rec (motive := fun _ => ℕ → List Term × ℕ) (fun o => ([], o))
    (fun n _ ih o => (fun t : Term × ℕ => (fun r : List Term × ℕ => (t.1 :: r.1, r.2)) (ih t.2)) (fld4 w o (eL TS c n) (eU TS c n)))
/-- the minorant leaf (generic): decode, multipliers, then `mcheckGX` with the coarse-first term check -/
def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  (fun d : List Term × ℕ => (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
      (mcheckGX (mokTZC R top bk tD bD pb {ZN} {CSH}) top bk pb {Q} BS TS cN (toCl s) d.1
        [{", ".join(f"y.P{r}" for r in range(Q))}] [{", ".join(f"y.S{r}" for r in range(Q))}] y.Cp y.Cm))
    (ydec (toCl s).L (toCl s).A (toCl s).B {QB} w {YFUEL} ⟨d.2, {", ".join(["0"] * (len(YF) - 1))}⟩))
  (decAll w (toCl s) (List.range TS.length) 0)""")
    if not DEFS:
        W(f"""theorem mleafP_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) :=
  {"mcheckGX_soundL" if NOREFL else "mcheckGX_sound"} (f := {PTFN}) (mtermTZC hlb hD hpt hR (by decide : 0 < {ZN})) hPR hTS
    (ydec_ok s {QB} w {YFUEL} _ (MulOK_zero s _)) (brec_ne h)""")
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
""" + (f"""  fun {ST} =>
    forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨{", ".join(STV)}⟩)
        (fleaf (Nat.shiftRight w 2) ⟨{", ".join(STV)}⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)""" if NOREFL else f"""  fun {ST} => Bool.rec (motive := fun _ => ℕ)
    (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨{", ".join(STV)}⟩)
        (fleaf (Nat.shiftRight w 2) ⟨{", ".join(STV)}⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1) (Nat.blt u{Q - 1} l0)"""))
    if not DEFS:
        W(f"""theorem fleaf_ok (w : ℕ) (s : St) (h : fleaf w s ≠ 0) : Covered (toCl s) :=
  farkas_cov (ydec_ok s {QBF} w {YFUEL} _ (MulOK_zero s 0)) (brec_ne h)

theorem leafStep_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (pos w : ℕ) :
    CovK (leafStep top bk tD bD pb R pos w) := by
  intro s h
""" + (f"""  have h' : forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)
      (fleaf (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) (fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) ≠ 0 := h
  rw [forceR_eq] at h'
  cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
  · rw [hk] at h'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h'; exact h' rfl
  · rw [hk] at h'; exact fleaf_ok _ s fun h0 => by rw [h0] at h'; exact h' rfl""" if NOREFL else f"""  have h' : Bool.rec (motive := fun _ => ℕ) (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)
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
    linarith"""))
WIN = int(os.environ.get("WIN", "0"))          # leaf window: the leaf reads a WIN-bit slice of the walk (0: the whole rest)
LEAFW = f"(Nat.land (Nat.shiftRight bits pos) WMASK)" if WIN else "(Nat.shiftRight bits pos)"
if WIN: W(f"/-- the leaf's window: a leaf word is at most {WIN} bits, so its fields are read from a {WIN}-bit slice -/\ndef WMASK : ℕ := {hex((1 << WIN) - 1)}")
NODESPLIT = ((f"(splitAx ih (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 6) 1) (Nat.add pos 7) (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 31))" if BSPLIT else
              f"(splitAx ih (Nat.add pos {1 + 5}) (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 31))") if FIXED else
             f"""(forceT ({hdecT("A", ATAB, "bits", "(Nat.add pos 1)")}) fun al => splitAx ih (Nat.add (Nat.add pos 1) (Nat.shiftRight al 16)) (Nat.land al 65535))""")
W(f"""/-- a node: bit `pos` selects split (`[1]`, then the axis codeword; the children from the bit after it) or leaf (`[0]`) -/
def node (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos {LEAFW})
    {NODESPLIT}
    (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1)

""" + (f"""/-- the walk on closed cells: no node tightening, the splits close their children (TZ.md §5) -/
def walkC (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => node top bk tD bD pb R bits ih pos) fuel

/-- the walk from a root box: the box sums close it (`tm`, once), then `walkC` -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits fuel : ℕ) : WF :=
  fun pos => tm (walkC top bk tD bD pb R bits fuel pos)""" if CLOSE else f"""/-- the walk: every node is first tightened (an empty node ends there, no bits) -/
def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => T1 pos (node top bk tD bD pb R bits ih pos)) fuel"""))
CHUNKL = ""
if os.environ.get("DATA") and not DEFS and not GENI:
    eqc = " && ".join(f"Nat.beq a.{v} b.{v}" for v in STV)
    nested = "h0"
    for i_ in range(1, len(STV)): nested = f"⟨{nested}, h{i_}⟩"
    CHUNKL = f"""/-- (chunked walks) field-wise equality of two states -/
def stEq (a b : St) : Bool := {eqc}
theorem St_eq {{a b : St}} (h : stEq a b = true) : a = b := by
  cases a; cases b
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain {nested} := h
  subst_vars; rfl
/-- the continuation that accepts exactly the state `t` -/
def kEq (t : St) : ST := fun {ST} => Bool.rec (motive := fun _ => ℕ) 0 1 (stEq ⟨{", ".join(STV)}⟩ t)
theorem kEq_ok {{t : St}} (h : Covered (toCl t)) : CovK (kEq t) := fun s hs => by
  have e : U (kEq t) s = Bool.rec (motive := fun _ => ℕ) 0 1 (stEq s t) := rfl
  rw [e] at hs
  cases hb : stEq s t
  · rw [hb] at hs; exact absurd rfl hs
  · rw [St_eq hb]; exact h
""" + (f"""/-- a chunked root: `tm` takes the root box `s` to its closed state `t` (computed) -/
theorem tm_to {{s t : St}} (hT : U (tm (kEq t)) s = 1) (h : Covered (toCl t)) : Covered (toCl s) :=
  tm_ok (kEq_ok h) s (by rw [hT]; decide)
/-- a chunk boundary's split on gap `r` at its midpoint, the children closed (`cupd`) -/
theorem gsplit_to (r : ℕ) (hr : r < {Q}) {{t sA sB : St}}
    (eA : toCl sA = cupd {Q} PR SL ⟨(toCl t).L, (toCl t).U.set r (qG (toCl t) r), (toCl t).A, (toCl t).B⟩ r (r + 1))
    (eB : toCl sB = cupd {Q} PR SL ⟨(toCl t).L.set r (qG (toCl t) r), (toCl t).U, (toCl t).A, (toCl t).B⟩ (r + 1) r)
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_gmidC hSL hPR r rfl rfl hr (eA ▸ hA) (eB ▸ hB)
/-- a chunk boundary's split on pair `k` at the raw midpoint of its bounds, the children closed (`cupd`) -/
theorem ssplit_to (k : ℕ) (hk : k < {NC}) {{t sA sB : St}}
    (eA : toCl sA = cupd {Q} PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A, (toCl t).B.set k (qR (toCl t) k)⟩ (pI PR k) (pJ PR k))
    (eB : toCl sB = cupd {Q} PR SL ⟨(toCl t).L, (toCl t).U, (toCl t).A.set k (qR (toCl t) k), (toCl t).B⟩ (pJ PR k) (pI PR k))
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_rmidC hSL hPR k rfl rfl hk (eA ▸ hA) (eB ▸ hB)
""" if CLOSE else f"""/-- a chunk boundary: T1 takes `s` to `t` (computed), so `t` covered gives `s` covered -/
theorem t1_to {{s t : St}} (hT : U (T1 0 (kEq t)) s = 1) (h : Covered (toCl t)) : Covered (toCl s) :=
  T1_ok (pos := 0) (kEq_ok h) s (by rw [hT]; decide)
/-- a chunk boundary's split on gap `r` at its midpoint -/
theorem gsplit_to (r : ℕ) (hr : r < {Q}) {{t sA sB : St}}
    (eA : toCl sA = ⟨(toCl t).L, (toCl t).U.set r (qG (toCl t) r), (toCl t).A, (toCl t).B⟩)
    (eB : toCl sB = ⟨(toCl t).L.set r (qG (toCl t) r), (toCl t).U, (toCl t).A, (toCl t).B⟩)
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_gmid r (n := {Q}) rfl rfl hr (eA ▸ hA) (eB ▸ hB)
/-- a chunk boundary's split on pair `k` at the raw midpoint of its bounds -/
theorem ssplit_to (k : ℕ) (hk : k < {NC}) {{t sA sB : St}}
    (eA : toCl sA = ⟨(toCl t).L, (toCl t).U, (toCl t).A, (toCl t).B.set k (qR (toCl t) k)⟩)
    (eB : toCl sB = ⟨(toCl t).L, (toCl t).U, (toCl t).A.set k (qR (toCl t) k), (toCl t).B⟩)
    (hA : Covered (toCl sA)) (hB : Covered (toCl sB)) : Covered (toCl t) :=
  cov_rmid k (n := {NC}) rfl rfl hk (eA ▸ hA) (eB ▸ hB)
""") + f"""/-- a walk from any bit position -/
theorem covered_of_walkP {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (bits fuel pos e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel pos s (h ▸ he)
"""
if not DEFS:
    W(f"""theorem forceT_cov {{x : ℕ}} {{k : ℕ → ST}} (h : CovK (k x)) : CovK (forceT x k) := by rw [forceT_eq]; exact h

""" + (f"""theorem walkC_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walkC top bk tD bD pb R bits fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => show CovK (node top bk tD bD pb R bits (walkC top bk tD bD pb R bits n) pos) from
      brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
      {("(splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _ _)" if BSPLIT else "(splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _)") if FIXED else "forceT_cov (splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _)"}

theorem walk_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) :=
  fun fuel pos => tm_ok (walkC_ok hlb hD hpt hR bits fuel pos)
""" if CLOSE else f"""theorem walk_ok {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => T1_ok (brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
      {"(splitAx_ok (walk_ok hlb hD hpt hR bits n) _ _)" if FIXED else "forceT_cov (splitAx_ok (walk_ok hlb hD hpt hR bits n) _ _)"})
""") + f"""
theorem covered_of_walk {{top : ℕ}} {{bk : ℕ → ℕ}} {{tD : ℕ}} {{bD : ℕ → ℕ}} {{pb : ℕ → ℕ}} {{R : ℕ × ℕ × List (List ℕ)}}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : {PTSD}) (hR : rgOk R = true) (bits fuel e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)

{CHUNKL}
/-- the adjacent term of each gap (its index in `TS`) -/
def ADJ : List ℕ := [{", ".join(str(ACT.index((r, r + 1))) for r in range(Q))}]
theorem hADJ : ∀ r < {Q}, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide

/-- (root) the certificate on every point with nonnegative gaps, from the per-gap covers (`coverChk`) and the walks over
the root cells (`rootCl`: a bad segment per gap, pair bounds absent) -/
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < {Q}, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < {Q}, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < {Q}, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : {Q} * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < {Q}, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl {Q} {NC} W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < {Q}, 0 ≤ g r) → {"PgL" if NOREFL else "Pg"} cN {Q} BS TS g :=
  {"root_coverL" if NOREFL else "root_cover"} hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun

/-- the root: every pair bound absent (`A = 0`, `B = W ≥ Σ u`) -/
theorem covered_box (s : St) (W : ℕ) (hA : ∀ k < {NC}, (toCl s).A.getD k 0 = 0) (hB : ∀ k < {NC}, (toCl s).B.getD k 0 = W)
    (hW : sumR (toCl s).U 0 {Q} ≤ W) (h : Covered (toCl s)) (g : ℕ → ℝ) (hb : InBox {Q} (toCl s) g) : {"PgL" if NOREFL else "Pg"} cN {Q} BS TS g :=
  h g (incell_root hPR hA hB hW hb)""")
W(f"\nend AMW.Cert.{NAME}\n")
txt = "\n\n".join(out)
P = (os.path.join(os.environ["PCOUT"], f"{FNAME}.lean") if os.environ.get("PCOUT")
     else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "window", ROOT, "AMW", f"{FNAME}.lean"))
if os.path.exists(P) and os.environ.get("OVERWRITE") != "1": raise SystemExit(f"{P} exists (OVERWRITE=1 to replace)")
open(P, "w").write(txt)
print(P, "bytes", len(txt.encode()), "pairs", len(PAIRS), "constraints", NC, "active terms", NA, "SIG", SIG,
      "table entries", sum(len(TTAB.get(t, [])) for t in ACT), len(ATAB), len(CTAB), "FIXED" if FIXED else "",
      f"closure candidates per child: min {min(NCAND)} max {max(NCAND)} mean {sum(NCAND) / len(NCAND):.1f}" if NCAND else "")
