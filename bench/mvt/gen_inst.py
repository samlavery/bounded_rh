"""Computational part of the instance (five gaps): functional `G`, zero-order leaf test `leafOK` (as the accepted
certificate), mean-value leaf test `mleafOK`, the walk with a per-leaf test flag.  Shared by the benchmark and the
checker generator."""

Q = 5
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SC = 1 << 15; U = 10**10; U1 = 10**9; KU1 = 2 * U1; RU = U // U1
CO = [f"l{r} u{r}" for r in range(Q)]; COORDS = " ".join(CO)
V = [f"g{r}" for r in range(Q)]
TS = [[t for t, (i, j) in enumerate(PAIRS) if i <= r < j] for r in range(Q)]
DMIN = 5        # the derivative tables are not refined below this level
CORNER = "lean"  # centre rule of the sizing model (size_m.make_pick)
PED = 4         # cover level of the derivative reads: bit length of (hi - lo) >>> PED
JC = 4          # centre: the midpoint rounded down to a multiple of 2^JC when that stays in the box

def nsum(kind, i, j):
    e = f"{kind}{i}"
    for r in range(i + 1, j): e = f"(Nat.add {e} {kind}{r})"
    return e

def nadd(xs):
    e = xs[0]
    for x in xs[1:]: e = f"(Nat.add {e} {x})"
    return e

def br(c, t, e, mot="ℕ"): return f"Bool.rec (motive := fun _ => {mot}) ({e}) ({t}) ({c})"

def centre_py(l, u):
    m = (l + u) >> 1; mm = (m >> JC) << JC
    return mm if mm >= l else m

def pick_py(l, u, P, N):
    if P >= N:
        mm = ((l + (1 << JC) - 1) >> JC) << JC
        return mm if mm <= u else l
    mm = (u >> JC) << JC
    return mm if mm >= l else u

def inst_defs(NAME, SA, aN, bN, cN, ORDER, TBL="(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ)",
              TARGS="top bk tD bD pb"):
    C = cN * SC * U
    lin = "(Nat.add " * (Q - 1) + f"(Nat.mul {bN[0]} l0)" + "".join(f" (Nat.mul {bN[r]} l{r}))" for r in range(1, Q))
    body = f"Nat.ble {C} s{len(PAIRS)}"
    for k in range(len(PAIRS) - 1, -1, -1):
        t = ORDER[k]; i, j = PAIRS[t]
        term = f"Nat.mul {aN[t] * SC} (lb top bk {nsum('l', i, j)} {nsum('u', i, j)})"
        body = f"let s{k + 1} := Nat.add s{k} ({term})\n  " + (f"ee {C} s{k + 1} (\n  {body})" if k < len(PAIRS) - 1 else body)
    LEAF = f"let s0 := Nat.mul {lin} {U}\n  ee {C} s0 (\n  {body})"
    # ---- mean-value test ----
    AR = [sum(aN[t] for t in TS[r]) for r in range(Q)]
    conds = []
    for r in range(Q):
        conds.append(f"Nat.ble l{r} m{r}"); conds.append(f"Nat.ble m{r} u{r}")
    for t in range(len(PAIRS)):
        conds.append(f"Nat.ble 1 p{t}"); conds.append(f"Nat.ble 1 q{t}")
    def PosN(r, q="q{t}"): return f"(Nat.sub {U1 * bN[r] + KU1 * AR[r]} {nadd([f'(Nat.mul {aN[t]} {q.format(t=t)})' for t in TS[r]])})"
    def NegN(r, p="p{t}"): return f"(Nat.sub {KU1 * AR[r]} {nadd([str(U1 * bN[r])] + [f'(Nat.mul {aN[t]} {p.format(t=t)})' for t in TS[r]])})"
    pen = []
    for r in range(Q):
        pen.append(f"(Nat.mul (Nat.sub m{r} l{r}) P{r})")
        pen.append(f"(Nat.mul (Nat.sub u{r} m{r}) N{r})")
    rhs = f"(Nat.add {C} (Nat.mul {RU} {nadd(pen)}))"
    linm = nadd([f"(Nat.mul {bN[r]} m{r})" for r in range(Q)])
    pts = nadd([f"(Nat.mul {aN[t]} (ptv pb {nsum('m', i, j)}))" for t, (i, j) in enumerate(PAIRS)])
    lhs = f"(Nat.add (Nat.mul {U} {linm}) (Nat.mul {SC} {pts}))"
    cexpr = conds[0]
    for c in conds[1:]: cexpr = f"({cexpr} && {c})"
    MCORE = f"{cexpr} && Nat.ble {rhs} {lhs}"
    M = []
    for t, (i, j) in enumerate(PAIRS):
        M.append(f"forceB (lb2 tD bD {nsum('l', i, j)} {nsum('u', i, j)}) fun e{t} =>")
    for r in range(Q):
        M.append(f"forceB {PosN(r, '(hi32 e{t})')} fun P{r} =>")
        M.append(f"forceB {NegN(r, '(lo32 e{t})')} fun N{r} =>")
    for r in range(Q):
        M.append(f"forceB (pick l{r} u{r} P{r} N{r}) fun m{r} =>")
    MARGS = " ".join(f"m{r}" for r in range(Q)) + " " + " ".join(f"p{t} q{t}" for t in range(len(PAIRS))) + " " + " ".join(f"P{r} N{r}" for r in range(Q))
    CALL = " ".join(f"m{r}" for r in range(Q)) + " " + " ".join(f"(lo32 e{t}) (hi32 e{t})" for t in range(len(PAIRS))) + " " + " ".join(f"P{r} N{r}" for r in range(Q))
    MLEAF = "\n  ".join(M) + f"\n  mcore pb {COORDS} {CALL}"
    def args_with(ax, which, val):
        cs = COORDS.split(); cs[2 * ax + (1 if which == "u" else 0)] = val; return " ".join(cs)
    def split_def(ax):
        return (f"/-- a split on gap {ax}: the lower half (`u{ax} := q`) from `pos + 4`, then the upper half from where it ends -/\n"
                f"def split{ax} (ih : WF) (pos {COORDS} : ℕ) : ℕ :=\n"
                f"  forceR (Nat.shiftRight (Nat.add l{ax} u{ax}) 1) fun q =>\n  let p := ih (Nat.add pos 4) {args_with(ax, 'u', 'q')}\n  "
                + br("Nat.beq p 0", "0", f"ih p {args_with(ax, 'l', 'q')}") + "\n")
    SPLITS = "\n".join(split_def(ax) for ax in range(Q))
    SPLITAX = f"split{Q-1} ih pos {COORDS}"
    for ax in range(Q - 2, -1, -1):
        SPLITAX = br(f"Nat.beq ax {ax}", f"split{ax} ih pos {COORDS}", SPLITAX)
    TEST = br("Nat.beq fl 1", f"mleafOK tD bD pb {COORDS}", f"leafOK top bk {COORDS}", "Bool")
    LEAFB = br(f"Nat.ble (Nat.add u{Q-1} 1) l0", "Nat.add pos 2", br(TEST, "Nat.add pos 2", "0"))
    MOT = " → ".join(["ℕ"] * (2 * Q + 2))
    return f"""
noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.{NAME}

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.PyrD

def SA : ℕ := {SA}
def cN : ℕ := {cN}

/-- the weighted functional on the gaps, in real form -/
def G ({' '.join(V)} : ℝ) : ℝ :=
  {' + '.join(f'({bN[r]} / (SA:ℝ)) * {V[r]}' for r in range(Q))}
    + {' + '.join(f'({aN[t]} / (SA:ℝ)) * wfun ({" + ".join(V[i:j])})' for t, (i, j) in enumerate(PAIRS))}

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the zero-order leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and
the running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) ({COORDS} : ℕ) : Bool :=
  {LEAF}

/-- the centre of `[l, u]` for the mean-value expansion (any value is sound: the test checks `l ≤ m ≤ u`): the lower
end when the gap's bound `Pos` on the positive part of the derivative is at least the bound `Neg` on its negative part,
else the upper end; each rounded to a multiple of `2^{JC}` when that stays in the interval -/
def pick (l u P N : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Nat.shiftLeft (Nat.shiftRight u {JC}) {JC}) fun mm =>
      Bool.rec (motive := fun _ => ℕ) u mm (Nat.ble l mm))
    (forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add l {(1 << JC) - 1}) {JC}) {JC}) fun mm =>
      Bool.rec (motive := fun _ => ℕ) l mm (Nat.ble mm u))
    (Nat.ble N P)

/-- the mean-value inequality at the centre `m`, given the derivative bounds `p_t`, `q_t` and the per-gap bounds
`P_r`, `N_r` -/
def mcore (pb : ℕ → ℕ) ({COORDS} : ℕ) ({MARGS} : ℕ) : Bool :=
  {MCORE}

/-- the mean-value leaf test at the centre `m` chosen by `pick`:
`cN·SC·U + (U/U1)·Σ_r ((m_r − l_r)·Pos_r + (u_r − m_r)·Neg_r) ≤ U·Σ b_r m_r + SC·Σ a_t v_t`, with `v_t` the point
bound of `w` at `s_t(m)`, `Pos_r = U1 b_r + KU1 A_r − Σ_(t∋r) a_t q_t` and `Neg_r = KU1 A_r − U1 b_r − Σ_(t∋r) a_t p_t`
(truncated at 0), `p_t`, `q_t` the bounds of `w' + 2` and `2 − w'` on the pair-sum interval (the halves of one read of
the pair pyramid, nonzero) -/
def mleafOK (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) ({COORDS} : ℕ) : Bool :=
  {MLEAF}

/-- the type of a walk continuation: position and the ten coordinates to the end position (`0` = failure) -/
abbrev WF : Type := {MOT}

{SPLITS}
/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax {COORDS} : ℕ) : ℕ :=
  {SPLITAX}

/-- a leaf (two bits: `0`, then the test flag `fl`): in the reflected half-space, or the flagged leaf test -/
def leafStep {TBL} (pos fl {COORDS} : ℕ) : ℕ :=
  {LEAFB}

/-- the bisection walk over the ten box coordinates (`Nat.rec` on the fuel): the node code is
`(bits >>> pos) &&& 15` (bit 0 split, bits 1..3 axis; a leaf is bit 0 clear and bit 1 its test flag); the position
after the subtree, `0` on failure -/
def walk {TBL} (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun {' '.join(['_'] * (2 * Q + 1))} => 0)
    (fun _ ih pos {COORDS} =>
      let w := Nat.land (Nat.shiftRight bits pos) 15
      Bool.rec (motive := fun _ => ℕ) (leafStep {TARGS} pos (Nat.land (Nat.shiftRight w 1) 1) {COORDS}) (splitAx ih pos (Nat.shiftRight w 1) {COORDS}) (Nat.beq (Nat.land w 1) 1))
    fuel
"""

def walk_code(nd, out):
    """bits of a subtree: split = 1 + axis (3 bits); leaf = 0 + flag"""
    if nd[0] == 'leaf':
        out.append(0); out.append(1 if nd[2] == 2 else 0)
    else:
        out.append(1); out.extend([(nd[2] >> i) & 1 for i in range(3)]); walk_code(nd[4], out); walk_code(nd[5], out)
