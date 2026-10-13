#!/usr/bin/env python3
"""(τ variant of window-scope's assemble_am.py: --tau uses the band profile, c(m−q) ≤ (q+1)/q, through
AMW.BrTau and the profile module; method line and AMTOPA/Gebendorfer credits in the header)
Assemble ONE Lean file from the AMW layer (root/AMW/*.lean: window, moments, constant, admissibility, zero and
prime side, the bridge port BrA/BrB/BrC retargeted to the AM window, AMTail) and a tail.

usage: python3 assemble_am.py OUT.lean [--mtcert SRC.lean] [--cert FILE] [--exclude M1,M2] [--cnum N --cden D --m M]

* imports of all modules are hoisted and de-duplicated (AMW.* imports dropped), `ChallengeDeps.CandidateSpec` first;
* modules are concatenated in dependency order (topological sort on `import AMW.X`); every scope a module leaves
  open (`noncomputable section`, `section`, `namespace`) is closed at its end;
* --exclude: modules to leave out (with everything that imports them), e.g. the certificate's own modules when
  measuring the layer alone;
* --mtcert SRC: (stage-H stand-in) append SevW10D's checker layers and certificate data (from the
  `ThreePoint/Base` marker to the `submission layer` marker of SRC) with its kernel renamed
  Kfun/kfun/wfun/F -> KfunMT/kfunMT/wfunMT/FMT (defined in a prelude), so it cannot touch the AM bridge; the scored
  theorems reference its `SevW10DData.cert`, so build, module replay, export, nanoda and closure replay all pay for
  a SevW10D-sized certificate;
* --cert FILE: append FILE verbatim (the real AM certificate, which must prove `RiemannFail.cert_AM : CertHyp`);
  then the scored theorems are unconditional.  Without --cert they take `hCert : RiemannFail.CertHyp`.
Reads ROOT/AMW (--root, default root) and SRC only; writes OUT only."""
import os, re, sys, math, argparse

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
EDGE_TAIL_READY = True       # the edge tail is wired to bridge-port's BrEdge API (am_dyadic_n_edge)

ap = argparse.ArgumentParser()
ap.add_argument('out')
ap.add_argument('--root', default='root')               # the layer's root under bench/window (root, rootR, rootR7)
ap.add_argument('--mtcert', default=None)
ap.add_argument('--cert', default=None)
ap.add_argument('--cnum', type=int, default=78927)      # c = cnum/cden (bridge-port's compiled AMTail instance)
ap.add_argument('--cden', type=int, default=10**7)
ap.add_argument('--m', type=int, default=132)
ap.add_argument('--exclude', default='')
ap.add_argument('--roots', default='')                  # keep only these modules and their import closure
ap.add_argument('--final6', default=None)               # NAME: the real n-point tail on AMW.Cert.NAME_cert_full
ap.add_argument('--npts', type=int, default=6)          # n for --final6 (G over g0..g_{n-2}, cert_full over n-1 gaps)
ap.add_argument('--tau', action='store_true')               # band profile: c(m−q) ≤ (q+1)/q (AMW.BrTau)
ap.add_argument('--kappa', default=None)                # NUM/DEN (default: 7-digit floor of the proved constant)
ap.add_argument('--profmod', default='BrProf')          # the module proving `band_profile_holds` (bridge-port)
ap.add_argument('--csrc', default=None)                 # the certificate's credit lines (required at n = 8)
ap.add_argument('--sqrt', action='store_true')          # √ band branch tail (module --sqrtmod)
ap.add_argument('--sqrtmod', default='BrSqrtWS')        # window-scope's clean-room √ module (gtau / Phi_g / am_dyadic_n_g)
ap.add_argument('--edge', default=None)                 # edge-window certificates E4,E5,… (their Inst/Data modules)
ap.add_argument('--edgemods', default='')               # the edge Lean chain (bridge-port's BrEdge* modules)
args = ap.parse_args()
if args.sqrt:
    args.tau = True                                     # the √ chain sits on the band profile: same credits
SRC = os.path.join(HERE, args.root, 'AMW')

mods = {}
for fn in sorted(os.listdir(SRC)):
    if fn.endswith('.lean'):
        mods[fn[:-5]] = open(os.path.join(SRC, fn), encoding='utf-8').read()

def deps(text):
    return re.findall(r'^import AMW\.(\w+)\s*$', text, re.M)

# drop excluded modules and everything that (transitively) imports them
drop = set()
for x in filter(None, args.exclude.split(',')):          # `G*` = every module whose name starts with G
    drop |= {k for k in mods if k.startswith(x[:-1])} if x.endswith('*') else {x}
changed = True
while changed:
    changed = False
    for k, t in mods.items():
        if k not in drop and any(d in drop for d in deps(t)):
            drop.add(k); changed = True
for k in drop:
    mods.pop(k, None)
if args.roots:
    keep, todo = set(), list(filter(None, args.roots.split(',')))
    while todo:
        r = todo.pop()
        if r in keep: continue
        if r not in mods: raise SystemExit('missing root/dependency AMW.' + r)
        keep.add(r); todo.extend(deps(mods[r]))
    drop |= set(mods) - keep
    mods = {k: v for k, v in mods.items() if k in keep}

order, seen = [], set()
def visit(m, stack=()):
    if m in seen: return
    if m in stack: raise SystemExit('import cycle at ' + m)
    for d in deps(mods[m]):
        if d not in mods: raise SystemExit(f'{m} imports missing AMW.{d}')
        visit(d, stack + (m,))
    seen.add(m); order.append(m)
for m in sorted(mods): visit(m)

imports = ['ChallengeDeps.CandidateSpec']
def add_import(i):
    if i not in imports: imports.append(i)

KW_OPEN = re.compile(r'^(noncomputable\s+)?section\b\s*(\S*)\s*$')
KW_NS = re.compile(r'^namespace\s+(\S+)\s*$')
KW_END = re.compile(r'^end\b\s*(\S*)\s*$')

def body_of(name, text):
    out, stack, in_comment = [], [], 0
    for ln in text.split('\n'):
        if in_comment == 0 and re.match(r'^import\s+\S+\s*$', ln):
            i = ln.split()[1]
            if not i.startswith('AMW.'): add_import(i)
            continue
        if re.match(r'^module\b', ln): continue
        opens, closes = ln.count('/-'), ln.count('-/')
        if in_comment == 0:
            mo, mn, me = KW_OPEN.match(ln), KW_NS.match(ln), KW_END.match(ln)
            if mo: stack.append(mo.group(2))
            elif mn: stack.append(mn.group(1))
            elif me and stack: stack.pop()
        in_comment = max(0, in_comment + opens - closes)
        out.append(ln)
    while stack:
        out.append(('end ' + stack.pop()).rstrip())
    return f'\n/-! ###### AMW module: {name} ###### -/\n\n' + '\n'.join(out).strip('\n') + '\n'

# a `macro "NAME "` declared (globally) in several kept modules is ambiguous once the modules share one file: each
# defining module gets its own copy, `NAME_<module>`, renamed at its declaration and its uses in that module only
# (no module uses another module's macro; checked here)
MAC = re.compile(r'^(?:local )?macro "(\w+) "', re.M)     # a `local macro` still clashes with a global one
macdef = {}
for m in order:
    for nm in MAC.findall(mods[m]):
        macdef.setdefault(nm, []).append(m)
for nm, ms in macdef.items():
    if len(ms) > 1:
        users = [m for m in order if m not in ms and re.search(r'(?<![\w.])' + nm + r'(?![\w])', mods[m])]
        assert not users, (nm, 'used outside its defining modules', users)
        for m in ms:
            mods[m] = re.sub(r'(?<![\w.])' + nm + r'(?![\w])', f'{nm}_{m}', mods[m])
        print(f'macro {nm}: renamed per module in {ms}')
bodies = [body_of(m, mods[m]) for m in order]

# ---------------------------------------------------------------- optional: the MT certificate as a cost stand-in
mt = ''
if args.mtcert:
    L = open(args.mtcert, encoding='utf-8').read().split('\n')
    i0 = next(i for i, l in enumerate(L) if 'source module: ThreePoint/Base.lean' in l)
    i1 = next(i for i, l in enumerate(L) if 'submission layer: constant-independent part' in l)
    blk = '\n'.join(L[i0:i1])
    for a, b in (('Kfun', 'KfunMT'), ('kfun', 'kfunMT'), ('wfun', 'wfunMT')):
        blk = re.sub(r"(?<![\w.'])" + a + r"(?![\w'])", b, blk)
    blk = re.sub(r"(?<![\w.'])F 4 ", 'FMT 4 ', blk)
    blk = re.sub(r"(?<=\[)F(?=,)", 'FMT', blk)          # `simp only [F, …]`
    prelude = '''
/-! ###### stand-in: the MT kernel for SevW10D's certificate block (renamed; independent of the AM bridge) ###### -/

noncomputable section

namespace Zeta23Ext.Bridge

def KfunMT (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)

def kfunMT (x : ℝ) : ℝ := KfunMT x / KfunMT 0

def wfunMT (x : ℝ) : ℝ := kfunMT x ^ 2

def FMT (n p : ℕ) (g : Fin (n - 1) → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfunMT (ptsN n g j - ptsN n g i)
        else 0

end Zeta23Ext.Bridge

end
'''
    mt = prelude + '\n' + blk + '\n'

# ---------------------------------------------------------------- the tail
c = f'(({args.cnum} : ℝ) / {args.cden})'
m = args.m
anchor = ('  have _hmt := Zeta23Ext.Bridge.ThreePoint.SevW10DData.cert\n' if args.mtcert else '')
cond = args.cert is None
hyp = ' (hCert : CertHyp)' if cond else ''
arg = ' hCert' if cond else ' cert_AM'
tail = f'''
/-! ###### tail: the n = 7 AM bound (AMTOPA weights `AMW.WAMT`, `AMW.am_dyadic`) ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW

/-- the certificate statement: `c ≤ Fw WAMT g` on the nonnegative orthant (`Fw` over `wfun = AMW.wfunAM`). -/
def CertHyp : Prop := ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → {c} ≤ Fw WAMT g

theorem kappa_le : candidateKappa ≤ Phi_w' 7 {c} {m} WAMT.B := by
  rw [WAMT_B]
  exact Phi_w'_ge (by norm_num) (by norm_num) (by unfold candidateKappa; norm_num)
'''
if args.cert:
    tail += '\nend RiemannFail\n\nend\n' + open(args.cert, encoding='utf-8').read() + \
        '\nnoncomputable section\n\nnamespace RiemannFail\n\nopen Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW\n'
tail += f'''
theorem dyadic{hyp} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
{anchor}  exact am_dyadic WAMT_adm (by norm_num) WAMT_bmin (by norm_num) (m := {m}) (by norm_num) (by norm_num)
    kappa_le{arg}

theorem cumulative{hyp} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (dyadic{' hCert' if cond else ''})

theorem strict : currentRecordKappa < candidateKappa := by
  unfold currentRecordKappa candidateKappa
  norm_num

end RiemannFail

end

/-! ###### the three scored theorems ###### -/

noncomputable section

/-- The submitted bound is strictly larger than the current formal record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa :=
  RiemannFail.strict

/-- The candidate proves a larger unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound{' (hCert : RiemannFail.CertHyp)' if cond else ''} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  RiemannFail.dyadic{' hCert' if cond else ''}

/-- The same unconditional bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative{' (hCert : RiemannFail.CertHyp)' if cond else ''} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  RiemannFail.cumulative{' hCert' if cond else ''}

end

#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
'''

head = ('/-\nAMW assembly: the AMTOPA-window bridge layer (AMW window, moments, constant, admissibility, zero side, prime\n'
        'side; the Zeta23Ext bridge retargeted to the AM window; AMTail)'
        + (' + SevW10D\'s certificate block as a cost stand-in' if args.mtcert else '')
        + (', the certificate taken as a hypothesis of the scored theorems (budget measurement only).'
           if cond else ', the AM certificate and the scored theorems.')
        + '\nModules: ' + ', '.join(order) + '.\n-/\n')

# ---------------------------------------------------------------- the real six-point tail (--final6 NAME)
if args.final6:
    from fractions import Fraction as Fr
    NAME = args.final6
    N = args.npts; Q = N - 1
    WD = {4: 'four', 5: 'five', 6: 'six', 7: 'seven', 8: 'eight'}
    nw, qw = WD[N], WD[Q]
    inst = mods[NAME + 'Inst']
    SA = int(re.search(r'^def SA : ℕ := (\d+)', inst, re.M).group(1))
    CN = int(re.search(r'^def cN : ℕ := (\d+)', inst, re.M).group(1))
    gargs = ' '.join(f'g{r}' for r in range(Q))
    gdef = re.search(r'^def G \(' + gargs + r' : ℝ\) : ℝ :=\n(.*?)\n\n', inst, re.M | re.S).group(1)
    bnum = [0] * Q
    for v, r in re.findall(r'\((\d+) / \(SA:ℝ\)\) \* g(\d)', gdef):
        bnum[int(r)] = int(v)
    a6 = {}
    for v, inside in re.findall(r'\((\d+) / \(SA:ℝ\)\) \* wfun \(([^)]*)\)', gdef):
        idx = [int(x) for x in re.findall(r'g(\d)', inside)]
        assert idx == list(range(idx[0], idx[-1] + 1)), inside
        a6[(idx[0], idx[-1] + 1)] = int(v)
    assert len(a6) == N * Q // 2 and all(bnum), (len(a6), bnum)
    for s in range(1, N):   # admissibility: every span sums to at most 2
        assert sum(v for (i, j), v in a6.items() if j - i == s) <= 2 * SA, s
    hn, hd = re.search(r'^theorem HW_ge : \((\d+) / 10 \^ (\d+) : ℝ\) ≤ HW', mods['Floor'], re.M).groups()
    H = Fr(int(hn), 10**int(hd)); B = Fr(sum(bnum), SA); C = Fr(CN, SA)
    Hdec = '0.' + hn.zfill(int(hd)) if H < 1 else str(float(H))   # the floor's exact decimal (never rounded up)
    tailH = re.search(r'≤ (\d+) / 10 \^ (\d+) - B \* \(\(m : ℝ\) - 5\)', mods['AMTail']).groups()
    assert Fr(int(tailH[0]), 10**int(tailH[1])) == H, (tailH, H)
    # edge windows (--edge E4,E5,E6): truncated windows at both block ends, each with its own certificate
    # `AMW.Cert.E_cert_full` for the main weights restricted to k < Q gaps; every edge certificate serves the right end
    # (gaps 0..k−1) and, by the reflection symmetry of the weights (checked here), the left end
    EDGES = []                                  # (name, k, SA_e, CN_e, b_e, a_e, c_e, B_e)
    EXC = EXB = Fr(0)
    if args.edge:
        for r in range(Q):
            assert bnum[r] == bnum[Q - 1 - r], ('pressures not reflection-symmetric', r)
        for (i, j), v in a6.items():
            assert a6.get((N - 1 - j, N - 1 - i)) == v, ('pair weights not reflection-symmetric', i, j)
        for en in args.edge.split(','):
            einst = mods[en + 'Inst']
            eSA = int(re.search(r'^def SA : ℕ := (\d+)', einst, re.M).group(1))
            eCN = int(re.search(r'^def cN : ℕ := (\d+)', einst, re.M).group(1))
            hdr = re.search(r'^def G \(((?:g\d+ )*g\d+) : ℝ\) : ℝ :=\n(.*?)\n\n', einst, re.M | re.S)
            k = len(hdr.group(1).split())
            assert k < Q, (en, k)
            eb = [0] * k
            for v, r in re.findall(r'\((\d+) / \(SA:ℝ\)\) \* g(\d)', hdr.group(2)):
                eb[int(r)] = int(v)
            ea = {}
            for v, inside in re.findall(r'\((\d+) / \(SA:ℝ\)\) \* wfun \(([^)]*)\)', hdr.group(2)):
                idx = [int(x) for x in re.findall(r'g(\d)', inside)]
                assert idx == list(range(idx[0], idx[-1] + 1)), inside
                ea[(idx[0], idx[-1] + 1)] = int(v)
            # the edge functional is the main one restricted to points 0..k (exact rational equality)
            for r in range(k):
                assert Fr(eb[r], eSA) == Fr(bnum[r], SA), (en, 'pressure', r)
            want = {(i, j): v for (i, j), v in a6.items() if j <= k}
            assert {p for p, v in ea.items() if v} == {p for p, v in want.items() if v}, (en, 'pair set')
            for p, v in want.items():
                assert Fr(ea.get(p, 0), eSA) == Fr(v, SA), (en, 'pair', p)
            ce, Be = Fr(eCN, eSA), Fr(sum(eb), eSA)
            EDGES.append((en, k, eSA, eCN, eb, ea, ce, Be))
        sides = 2                                   # each edge certificate is used at both ends
        EXC = sides * sum(e[6] for e in EDGES)
        EXB = sides * sum(e[7] for e in EDGES)
        for e in EDGES:
            print(f'edge {e[0]}: k {e[1]} c_k {float(e[6]):.9f} B_k {float(e[7]):.9f} (κ·c−B {float(Fr(6734832, 10**7) * e[6] - e[7]):+.2e})')
        assert args.sqrt, 'edge windows are wired for the √ tail only'
    cAMn = [int(x) for x in re.findall(r'^  \| \d+ => (-?\d+)$', mods['Window'], re.M)]
    AMTOPA = [1000000000, 12378982, -12602495, 4164033, 5741405, -1724025, 6219280, -8047828, 6321519, -5241981,
              -892658, 560544, -431207]
    TYPH7 = [1000000000, 12497829, -14424455, 2621498, 7207519, -2561956, 6199418, -7197280, 4324511, -5325091,
             -309374, 443802, -310460]
    if cAMn == AMTOPA:
        wtitle = 'AMTOPA window (the window of zeta-exact-pressure, first 13 terms)'
        wcoef = "AMTOPA's coefficients"
        wsrc = '* the window: AMTOPA, zeta-exact-pressure (candidate.json, first 13 terms);'
    elif cAMn == TYPH7:
        wtitle = "window of typh's seven-point-optimised-window (AMTOPA's 13-term cosine family)"
        wcoef = "typh's coefficients, c_j = " + ', '.join(str(x) for x in cAMn) + ' over 10⁹'
        wsrc = ("* the window coefficients: seven-point-optimised-window by typh (Apache-2.0), in the 13-term cosine family\n"
                "  of AMTOPA, zeta-exact-pressure; pair weights and pressures re-solved here (LP);")
    else:
        wtitle = f"R window (AMTOPA's 13-term cosine family, corrections re-optimised for the {nw}-point bound)"
        wcoef = 'c_j = ' + ', '.join(str(x) for x in cAMn) + ' over 10⁹'
        wsrc = ("* the window family (ω₀ = √2, ω_j = 2πj, 13 terms): AMTOPA, zeta-exact-pressure; the twelve corrections\n"
                f"  re-optimised here for the weighted {nw}-point bound (LP for the weights, cutting-plane ascent for the window);")
    if args.sqrt:
        # √ band branch: Φ_g(m) = (H − B(m−q)/m)/(1 − g_τ(c(m−q))/m), g_τ(E) = E (E ≤ τ), 2√(τE) − τ (E > τ); no cap
        # on m.  The proof reads √(τE) through a 12-digit rational floor SLO (SLO² ≤ τE), so m is chosen, and Φ
        # certified, on the floored value.
        import math
        TAU = Fr(N, Q)
        def sq_floor(m):
            E = C * (m - Q) + EXC                  # with edge windows: the block energy floor c(m−q) + Σ c_t
            if E <= TAU:
                return E, None, E
            x = TAU * E
            slo = Fr(math.isqrt(x.numerator * 10**24 // x.denominator), 10**12)
            assert slo * slo <= x
            return E, slo, 2 * slo - TAU
        def phi_lo(m):
            E, slo, A = sq_floor(m)
            return (H - (B * (m - Q) + EXB) / m) / (1 - A / m)
        M = max(range(2 * N, 1000), key=phi_lo)
        ESQ, SLO, AEFF = sq_floor(M)
        PHI = phi_lo(M)
    else:
        CAP = Fr(Q + 1, Q) if args.tau else Fr(1)
        M = max(mm for mm in range(2 * N, 100000) if C * (mm - Q) <= CAP)
        PHI = (H - B * Fr(M - Q, M)) / (1 - C * Fr(M - Q, M))
    if args.kappa:
        kn, kd = map(int, args.kappa.split('/'))
    else:
        kd = 10**7; kn = (PHI.numerator * kd) // PHI.denominator
    K = Fr(kn, kd)
    assert K <= PHI, (float(K), float(PHI))
    if args.edge:
        base = max(((H - B * Fr(mm - Q, mm)) / (1 - (lambda E: E if E <= Fr(N, Q) else
                    2 * Fr(math.isqrt(int(Fr(N, Q) * E * 10**24)), 10**12) - Fr(N, Q))(C * (mm - Q)) / mm), mm)
                   for mm in range(2 * N, 400))
        print(f'edge: m {M}, A = c(m−q) + Σc_t = {float(ESQ):.9f}, Σ B_t = {float(EXB):.9f}, '
              f'√ floor {SLO.numerator}/{SLO.denominator}' if SLO is not None else f'edge: m {M}, A {float(ESQ):.9f}')
        print(f'edge: Φ_edge {float(PHI):.10f}  κ {kn}/{kd}  (no-edge best Φ {float(base[0]):.10f} at m {base[1]}; '
              f'gain {float(PHI - base[0]):+.2e})')
        if not EDGE_TAIL_READY:
            sys.exit('edge: numbers only; the tail glue waits for the BrEdge API (bridge-port)')
    bmin = min(bnum)
    an = []
    W = f'W{N}'; aW = f'aW{N}'; bW = f'bW{N}'
    gs = ' '.join(f'(g {r})' for r in range(Q)); hgs = ' '.join(f'(hg {r})' for r in range(Q))
    fs = ' + '.join(f'f {r}' for r in range(Q))
    L = [f'\n/-! ###### tail: the AM {nw}-point bound from the certificate `AMW.Cert.{NAME}_cert_full` ###### -/\n',
         'noncomputable section\n\nnamespace RiemannFail\n\nopen Filter\n'
         'open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW\n',
         f'/-- the pair weights `a_ij` (zero unless `i < j`), over `{SA}` -/\ndef {aW} : Fin {N} → Fin {N} → ℝ']
    for (i, j), v in sorted(a6.items()):
        L.append(f'  | {i}, {j} => ({v} : ℝ) / {SA}')
    L.append('  | _, _ => 0\n')
    L.append(f'/-- the per-gap pressures, over `{SA}` -/\ndef {bW} : Fin {Q} → ℝ')
    for r, v in enumerate(bnum):
        L.append(f'  | {r} => ({v} : ℝ) / {SA}')
    L.append(f'\ndef {W} : WCert {N} := ⟨{aW}, {bW}⟩\n')
    for i in range(N):
        for j in range(N):
            rhs = f'({a6[(i, j)]} : ℝ) / {SA}' if (i, j) in a6 else '0'
            L.append(f'theorem {aW}_{i}_{j} : {aW} {i} {j} = {rhs} := rfl')
            an.append(f'{aW}_{i}_{j}')
    for r, v in enumerate(bnum):
        L.append(f'theorem {bW}_{r} : {bW} {r} = ({v} : ℝ) / {SA} := rfl')
    bn = ', '.join(f'{bW}_{r}' for r in range(Q)); ann = ', '.join(an)
    L.append(f'\ntheorem {W}_B : {W}.B = ({sum(bnum)} : ℝ) / {SA} := by\n  show (∑ r : Fin {Q}, {bW} r) = _\n'
             f'  norm_num [Fin.sum_univ_{qw}, {bn}]\n')
    L.append(f'theorem {W}_a_nonneg : ∀ i j, 0 ≤ {W}.a i j := by\n  intro i j\n  unfold {W}\n  match i, j with')
    for i in range(N):
        for j in range(N):
            L.append(f'  | {i}, {j} => show (0:ℝ) ≤ {aW} {i} {j}; norm_num [{aW}_{i}_{j}]')
    L.append(f'\ntheorem {W}_bmin : ∀ r, (({bmin} : ℝ) / {SA}) ≤ {W}.b r := by\n  intro r\n  unfold {W}\n  match r with')
    for r in range(Q):
        L.append(f'  | {r} => show (({bmin} : ℝ) / {SA}) ≤ {bW} {r}; norm_num [{bW}_{r}]')
    L.append(f'\ntheorem {W}_capacity : ∀ s : ℕ, {W}.spanMass s ≤ 2 := by\n  intro s\n  unfold WCert.spanMass {W}\n'
             f'  rcases lt_or_ge s {N} with hs | hs\n'
             f'  · interval_cases s <;> simp (config := {{ decide := true }}) only [Fin.sum_univ_{nw}, {ann}, if_true, if_false] <;> norm_num\n'
             f'  · have h0 : ∀ i j : Fin {N}, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by\n'
             '      intro i j ⟨_, h⟩\n      have := j.2\n      omega\n'
             '    simp only [h0, if_false, Finset.sum_const_zero]\n    norm_num\n')
    L.append(f'theorem {W}_adm : {W}.Adm := ⟨{W}_a_nonneg, fun r => le_trans (by norm_num) ({W}_bmin r), {W}_capacity⟩\n')
    if EDGES:
        # the reflection symmetry of the pair weights (the `hsym` hypothesis of BrEdge): 64 literal cases, each `rfl`
        # (kernel ≈ 50 ms; the weights' symmetry is checked on the parsed data above, so every case is syntactic)
        L.append(f'/-- the pair weights are symmetric under the reflection `i ↦ {N - 1} − i` of the points -/\n'
                 f'theorem {W}_hsym : ∀ a b : Fin {N}, {W}.a a b = {W}.a b.rev a.rev := by\n'
                 f'  intro a b\n  fin_cases a <;> fin_cases b <;> rfl\n')
    L.append(f'private lemma sum{Q} (f : Fin ({N} - 1) → ℝ) : ∑ i, f i = {fs} := by\n'
             f'  show ∑ i : Fin {Q}, f i = {fs}\n  exact Fin.sum_univ_{qw} f\n')
    L.append(f'/-- the certificate\'s kernel is the bridge\'s (both are `AMW.wfunAM`) -/\n'
             f'theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl\n')
    L.append(f'/-- `Fw {W}` written out on the gaps: it is the certificate\'s functional `{NAME}.G`. -/\n'
             f'theorem Fw_{W} (g : Fin ({N} - 1) → ℝ) :\n'
             f'    Fw {W} g = AMW.Cert.{NAME}.G {gs} := by\n'
             f'  show (∑ r : Fin {Q}, {bW} r * g r) + (∑ i : Fin {N}, ∑ j : Fin {N}, if (i : ℕ) < (j : ℕ) then '
             f'{aW} i j * wfun (ptsN {N} g j - ptsN {N} g i) else 0) = _\n'
             f'  unfold AMW.Cert.{NAME}.G ptsN\n'
             f'  simp only [cert_wfun_eq, sum{Q}, Fin.sum_univ_{nw}, Fin.sum_univ_{qw}, Fin.isValue, {ann}, {bn}]\n'
             f'  norm_num [AMW.Cert.{NAME}.SA]\n  try ring\n')
    c6 = f'(({CN} : ℝ) / {SA})'
    L.append(f'/-- **the certificate**: `c ≤ Fw {W} g` on the nonnegative orthant -/\n'
             f'theorem cert_AM : ∀ g : Fin {Q} → ℝ, (∀ i, 0 ≤ g i) → {c6} ≤ Fw {W} g := by\n'
             f'  intro g hg\n  rw [Fw_{W}]\n'
             f'  have h := AMW.Cert.{NAME}_cert_full {gs} {hgs}\n'
             f'  simp only [AMW.Cert.{NAME}.cN, AMW.Cert.{NAME}.SA] at h\n  push_cast at h\n  exact h\n')
    phige = "Phi_w'_ge6" if N == 6 else f"Phi_w'_ge_n (n := {N})"
    dyad = (f'am_dyadic_n_τ band_profile_holds (n := {N}) (by norm_num) {W}_adm' if args.tau else
            f'am_dyadic6 {W}_adm' if N == 6 else f'am_dyadic_n (n := {N}) (by norm_num) {W}_adm')
    if EDGES:
        # the edge tail: an instantiation of bridge-port's AMW.am_dyadic_n_edge (BrEdgeChain).  Per edge certificate E
        # with k gaps: the entries of `W.pre k` as `rfl` lemmas (no Fin.mk normalisation needed), `Fw (W.pre k) = E.G`,
        # and the link `cE ≤ Fw (W.pre k) g` from `E_cert_full`; then the floors `ctE`, the set `SE`, `edgeA`/`edgeP`
        # as literals, and the final step `Phi_g_edge_ge_sqrt` with the rational floor SLO
        KW = {3: 'three', 4: 'four', 5: 'five', 6: 'six', 7: 'seven', 8: 'eight'}
        for (en, k, eSA, eCN, eb, ea, ce, Be) in EDGES:
            fk = ' + '.join(f'f {r}' for r in range(k))
            L.append(f'private lemma sumE{k}a (f : Fin ({k + 1} - 1) → ℝ) : ∑ i, f i = {fk} := by\n'
                     f'  show ∑ i : Fin {k}, f i = {fk}\n  exact Fin.sum_univ_{KW[k]} f\n'
                     f'private lemma sumE{k}b (f : Fin ({k} + 1 - 1) → ℝ) : ∑ i, f i = {fk} := by\n'
                     f'  show ∑ i : Fin {k}, f i = {fk}\n  exact Fin.sum_univ_{KW[k]} f\n')
            pl = []
            for i in range(k + 1):
                for j in range(i + 1, k + 1):
                    L.append(f'theorem pre{k}_a_{i}_{j} : ({W}.pre {k}).a {i} {j} = ({a6[(i, j)]} : ℝ) / {SA} := rfl')
                    pl.append(f'pre{k}_a_{i}_{j}')
            for r in range(k):
                L.append(f'theorem pre{k}_b_{r} : ({W}.pre {k}).b {r} = ({bnum[r]} : ℝ) / {SA} := rfl')
                pl.append(f'pre{k}_b_{r}')
            PL = ', '.join(pl)
            gk = ' '.join(f'(g {r})' for r in range(k)); hgk = ' '.join(f'(hg {r})' for r in range(k))
            L.append(f'\n/-- `Fw ({W}.pre {k})` written out: the edge certificate\'s functional `{en}.G` -/\n'
                     f'theorem Fw_pre{k} (g : Fin ({k} + 1 - 1) → ℝ) :\n'
                     f'    Fw ({W}.pre {k}) g = AMW.Cert.{en}.G {gk} := by\n'
                     f'  show (∑ r : Fin {k}, ({W}.pre {k}).b r * g r) + (∑ i : Fin {k + 1}, ∑ j : Fin {k + 1},\n'
                     f'    if (i : ℕ) < (j : ℕ) then ({W}.pre {k}).a i j * wfun (ptsN {k + 1} g j - ptsN {k + 1} g i) else 0) = _\n'
                     f'  unfold AMW.Cert.{en}.G ptsN\n'
                     f'  simp only [cert_wfun_eq, sumE{k}a, Fin.sum_univ_{KW[k + 1]}, Fin.sum_univ_{KW[k]}, Fin.isValue, {PL}]\n'
                     f'  norm_num [AMW.Cert.{en}.SA]\n  try ring\n')
            L.append(f'/-- **the edge certificate `{en}`** ({k} gaps): `c_{k} ≤ Fw ({W}.pre {k}) g` on the nonnegative orthant -/\n'
                     f'theorem cert_E{k} : ∀ g : Fin ({k} + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → (({eCN} : ℝ) / {eSA}) ≤ Fw ({W}.pre {k}) g := by\n'
                     f'  intro g hg\n  rw [Fw_pre{k}]\n'
                     f'  have h := AMW.Cert.{en}_cert_full {gk} {hgk}\n'
                     f'  simp only [AMW.Cert.{en}.cN, AMW.Cert.{en}.SA] at h\n  push_cast at h\n  exact h\n')
        ks = [e[1] for e in EDGES]
        SEs = '{' + ', '.join(str(k) for k in ks) + '}'
        L.append('/-- the edge floors `ct k` (zero off the edge set) -/\ndef ctE : ℕ → ℝ\n'
                 + ''.join(f'  | {e[1]} => ({e[3]} : ℝ) / {e[2]}\n' for e in EDGES) + '  | _ => 0\n')
        L.append(f'/-- the edge set -/\ndef SE : Finset ℕ := {SEs}\n')
        memo = '  intro k hk\n  simp only [SE, Finset.mem_insert, Finset.mem_singleton] at hk\n'
        L.append(f'theorem SE_k : ∀ k ∈ SE, k + 2 ≤ {N} := by\n{memo}  omega\n')
        L.append(f'theorem SE_ct0 : ∀ k ∈ SE, 0 ≤ ctE k := by\n{memo}'
                 f'  rcases hk with {" | ".join("rfl" for _ in ks)} <;> norm_num [ctE]\n')
        L.append(f'theorem SE_cert : ∀ k ∈ SE, ∀ g : Fin (k + 1 - 1) → ℝ, (∀ i, 0 ≤ g i) → ctE k ≤ Fw ({W}.pre k) g := by\n'
                 f'{memo}  rcases hk with {" | ".join("rfl" for _ in ks)}\n'
                 + ''.join(f'  · exact cert_E{k}\n' for k in ks))
        Af = ESQ                                            # A = c(m−q) + 2 Σ c_k, exact
        Pf = B * (M - Q) + EXB                              # P = B(m−q) + 2 Σ B_k, exact
        sums = ', '.join(f'sumE{k}b' for k in ks); pbs = ', '.join(f'pre{k}_b_{r}' for k in ks for r in range(k))
        # the Finset sum over SE is evaluated first (norm_num), then each `edgeB W k` by its own Fin-sum and entries
        L.append(f'theorem edgeA_E : edgeA {c6} {N} {M} SE ctE = {Af.numerator} / {Af.denominator} := by\n'
                 f'  unfold edgeA\n  norm_num [SE, ctE]\n')
        L.append(f'theorem edgeP_E : edgeP {W} {M} SE = {Pf.numerator} / {Pf.denominator} := by\n'
                 f'  unfold edgeP\n  rw [{W}_B]\n  norm_num [SE]\n'
                 f'  simp only [edgeB, {sums}, {pbs}]\n  norm_num\n')
        if SLO is None:
            L.append(f'theorem kappa_le : candidateKappa ≤ Phi_g_edge {N} (edgeA {c6} {N} {M} SE ctE) {M} (edgeP {W} {M} SE) := by\n'
                     f'  rw [edgeA_E, edgeP_E]\n'
                     f'  exact Phi_g_edge_ge_lin (by norm_num) (by norm_num) AMW.HW_ge (by norm_num [tauq]) (by norm_num)\n'
                     f'    (by unfold candidateKappa; norm_num)\n')
        else:
            L.append(f'/-- the √ branch with the edge windows at `m = {M}`, with `√(τ A) ≥ {SLO.numerator}/{SLO.denominator}` -/\n'
                     f'theorem kappa_le : candidateKappa ≤ Phi_g_edge {N} (edgeA {c6} {N} {M} SE ctE) {M} (edgeP {W} {M} SE) := by\n'
                     f'  rw [edgeA_E, edgeP_E]\n'
                     f'  exact Phi_g_edge_ge_sqrt (s := ({SLO.numerator} : ℝ) / {SLO.denominator}) (by norm_num) (by norm_num) AMW.HW_ge\n'
                     f'    (by unfold candidateKappa; norm_num) (by norm_num) (by norm_num [tauq]) (by norm_num [tauq])\n'
                     f'    (by norm_num) (by unfold candidateKappa; norm_num [tauq])\n')
        L.append(f'theorem dyadic :\n    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,\n'
                 f'      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=\n'
                 f'  am_dyadic_n_edge (n := {N}) (by norm_num) {W}_adm {W}_hsym (by norm_num : (0 : ℝ) < ({bmin} : ℝ) / {SA}) '
                 f'{W}_bmin (by norm_num) (m := {M})\n    (by norm_num) cert_AM SE SE_k ctE SE_ct0 SE_cert '
                 f'(by rw [edgeA_E]; norm_num) kappa_le\n')
    elif args.sqrt:
        # the √ tail: an instantiation of window-scope's AMW.BrSqrtWS; every side condition is a rational inequality
        # for `norm_num [tauq]`, and the √ enters only through the rational floor SLO (SLO² ≤ τ·c(m−q))
        if SLO is None:
            L.append(f'theorem kappa_le : candidateKappa ≤ Phi_g {N} {c6} {M} {W}.B := by\n  rw [{W}_B]\n'
                     f'  exact Phi_g_ge_lin (by norm_num) (by norm_num) AMW.HW_ge (by norm_num [tauq]) (by norm_num)\n'
                     f'    (by unfold candidateKappa; norm_num)\n')
        else:
            L.append(f'/-- the √ branch at `m = {M}`, with `√(τ c(m−q)) ≥ {SLO.numerator}/{SLO.denominator}` -/\n'
                     f'theorem kappa_le : candidateKappa ≤ Phi_g {N} {c6} {M} {W}.B := by\n  rw [{W}_B]\n'
                     f'  exact Phi_g_ge_sqrt (s := ({SLO.numerator} : ℝ) / {SLO.denominator}) (by norm_num) (by norm_num) AMW.HW_ge\n'
                     f'    (by unfold candidateKappa; norm_num) (by norm_num) (by norm_num [tauq]) (by norm_num [tauq])\n'
                     f'    (by norm_num) (by unfold candidateKappa; norm_num [tauq])\n')
        L.append(f'theorem dyadic :\n    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,\n'
                 f'      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=\n'
                 f'  am_dyadic_n_g (n := {N}) (by norm_num) {W}_adm (by norm_num : (0 : ℝ) < ({bmin} : ℝ) / {SA}) '
                 f'{W}_bmin (by norm_num) (m := {M})\n    (by norm_num) (by norm_num) kappa_le cert_AM\n')
    else:
        L.append(f'theorem kappa_le : candidateKappa ≤ Phi_w\' {N} {c6} {M} {W}.B := by\n  rw [{W}_B]\n'
                 f'  exact {phige} (by norm_num) (by norm_num) (by unfold candidateKappa; norm_num)\n')
        L.append(f'theorem dyadic :\n    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,\n'
                 f'      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=\n'
                 f'  {dyad} (by norm_num : (0 : ℝ) < ({bmin} : ℝ) / {SA}) {W}_bmin (by norm_num) (m := {M})\n'
                 f'    (by norm_num) (by norm_num) kappa_le cert_AM\n')
    L.append('theorem cumulative :\n    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,\n'
             '      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=\n'
             '  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM\n'
             '    (fun _ _ _ => Zeta23.N0star_add\' Zeta23.zetaSeam) dyadic\n')
    L.append('theorem strict : currentRecordKappa < candidateKappa := by\n  unfold currentRecordKappa candidateKappa\n  norm_num\n')
    L.append('end RiemannFail\n\nend\n')
    L.append('''/-! ###### the three scored theorems, statements as generated by the trusted template ###### -/

noncomputable section

/-- The submitted bound is strictly larger than the current formal record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa :=
  RiemannFail.strict

/-- The candidate proves a larger unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  RiemannFail.dyadic

/-- The same unconditional bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  RiemannFail.cumulative

end

#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
''')
    tail = '\n'.join(L)
    mt = ''
    leaves = re.search(r'(\d+) leaves', mods.get(NAME + 'Data', ''))
    dhead = mods.get(NAME + 'Data', '')[:2000]
    nbas = re.search(r'(\d+) basins', dhead)
    if args.csrc:                                       # the certificate author's own credit lines
        csrc = open(args.csrc, encoding='utf-8').read().rstrip('\n')
    elif N == 8:
        sys.exit('n = 8: pass --csrc FILE with the certificate credit lines (the n = 7 texts would misdescribe it)')
    elif (nbas is None or int(nbas.group(1)) == 0) and 'minorant' in dhead:      # M-leaf certificate, no basins
        csrc = ("* pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0);\n"
                "* the certificate's leaves are zero-order (pyramid reads) or per-term minorant leaves: each pair term "
                "bounded below by\n  a constant, a tangent at a grid point inside a certified convex region of w "
                "(extended by derivative-table reads),\n  or a convex combination of two of these (mvt-engine's MinCore; "
                "tangent points on two grids);")
    else:
        csrc = ("* pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0); convex basins and centres\n"
                "  after six-point-convex-basins-2 by typh (Apache-2.0);")
    tmods = [m for m in order if 'engine speed-ups by typh' in mods[m]]   # modules taken verbatim from typh's files
    if tmods:
        names = tmods[0] if len(tmods) == 1 else ', '.join(tmods[:-1]) + ' and ' + tmods[-1]
        csrc += (f"\n* the cell-evaluator modules {names} are taken from seven-point-optimised-window by typh (Apache-2.0),\n"
                 "  including his unrolled far sums (engine speed-ups);")
    # provenance of the engine, by content, not comments: a kept CEngine/GBase/GFar/GCell carrying at least half of
    # the lines that typh's seven-point-optimised-window module (riemannzeta-fun dc788ef) has and our original
    # (window/root) lacks is typh-derived; it is credited here unless the credit lines already name that submission
    import subprocess
    typh = subprocess.run(['git', '-C', os.path.expanduser('~/work/riemannzeta-fun'), 'show',
                           'dc788ef:submissions/seven-point-optimised-window/proof/Solution.lean'],
                          capture_output=True, text=True).stdout
    if not typh:
        sys.exit('provenance check: cannot read typh\'s dc788ef source (~/work/riemannzeta-fun)')
    tp = re.split(r'/-! ###### AMW module: (\w+) ###### -/\n', typh)
    TM = dict(zip(tp[1::2], tp[2::2]))
    derived = []
    for m in ('CEngine', 'GBase', 'GFar', 'GCell'):
        if m not in order or m not in TM:
            continue
        orig = set(open(os.path.join(HERE, 'root', 'AMW', m + '.lean'), encoding='utf-8').read().splitlines())
        dist = [l for l in TM[m].splitlines() if l.strip() and l not in orig and not l.lstrip().startswith('--')]
        have = set(mods[m].splitlines())
        unrolled = m == 'GCell' and '(farJ n k XL XU XL2 XU2 (farJ' in mods[m]   # his unrolled far sum, own coefficients
        if dist and (2 * sum(l in have for l in dist) >= len(dist) or unrolled):
            derived.append(m)
    if derived:
        print(f'provenance: typh-derived engine modules {derived}')
        if 'seven-point-optimised-window' not in csrc:
            names = derived[0] if len(derived) == 1 else ', '.join(derived[:-1]) + ' and ' + derived[-1]
            csrc += f"\n* engine speed-ups in {names} taken from seven-point-optimised-window by typh (Apache-2.0);"
    TW = {7: 'seven', 8: 'eight', 6: 'six'}[N]
    taux = (f'  The block bound uses the band profile min((q+1)/q, E_band) ≤ defect (q = {Q}, τ = {Q + 1}/{Q};\n'
            f'AMTOPA\'s band bound, after Gebendorfer), so c(m−q) ≤ {Q + 1}/{Q} replaces c(m−q) ≤ 1.') if args.tau else ''
    meth = (f'\nMethod: τ = {Q + 1}/{Q} band profile (AMTOPA Lemma, via Gebendorfer 2026 Lemma 3.3) on the {NAME} {TW}-point certificate.\n') if args.tau else ''
    phis = f'Φ = (H_W − B(m−{Q})/m)/(1 − c(m−{Q})/m)'
    if args.sqrt:
        taux = (f'  The block bound uses the √ branch of the band profile, g_τ(E_band) ≤ defect (q = {Q}, τ = {Q + 1}/{Q}),\n'
                'g_τ(E) = E for E ≤ τ and 2√(τE) − τ for E > τ (`band_profile_sqrt`, derived from Gebendorfer\'s Lemma 3.3), so\n'
                'g_τ(c(m−q)) replaces c(m−q) with no cap on m.')
        meth = (f'\nMethod: √ τ = {Q + 1}/{Q} band profile (derived independently from Gebendorfer 2026 Lemma 3.3 / AMTOPA) on the\n'
                f'{NAME} {TW}-point certificate.\n')
        phis = (f'Φ = (H_W − B(m−{Q})/m)/(1 − g_τ(c(m−{Q}))/m), √(τ c(m−{Q})) read through the rational floor '
                f'{SLO.numerator}/{SLO.denominator},' if SLO is not None else
                f'Φ = (H_W − B(m−{Q})/m)/(1 − g_τ(c(m−{Q}))/m),')
        if EDGES:
            ks = ', '.join(str(e[1]) for e in EDGES)
            taux += (f'\nEdge windows: at both ends of each block, truncated windows of k = {ks} gaps carry the same weights\n'
                     f'restricted to their gaps, each with its own certificate (floor c_k, restricted pressure B_k; '
                     + ', '.join(f'`{e[0]}`: c = {e[3]}/{e[2]}' for e in EDGES) + ');\n'
                     'their floors join the block energy inside g_τ and their pressures join the cost.')
            phis = (f'Φ = (H_W − (B(m−{Q}) + Σ_t B_t)/m)/(1 − g_τ(c(m−{Q}) + Σ_t c_t)/m), √ read through the rational floor '
                    f'{SLO.numerator}/{SLO.denominator},' if SLO is not None else
                    f'Φ = (H_W − (B(m−{Q}) + Σ_t B_t)/m)/(1 − g_τ(c(m−{Q}) + Σ_t c_t)/m),')
    tsrc = ('* the band profile (τ = (q+1)/q in place of 1): AMTOPA, zeta-exact-pressure (MIT), as presented in\n'
            '  Gebendorfer, "Zeta Geometry and Class Cap" (preprint), Lemma 3.3; proved here by bridge-port\n'
            f'  (`band_profile_holds`, module {args.profmod}: a Fenchel bound on the defect and a residue-class\n'
            '  Cauchy–Schwarz on the band, for any Hermitian G and injective rank labelling);\n'
            '* the τ chain (module BrTau, am-cert): the band-restricted window energy, `block_bound_w\'_τ`,\n'
            '  `n_point_bound_w\'_τ` (c(m−q) ≤ (q+1)/q in place of 1) and `AMW.am_dyadic_n_τ`;\n') if args.tau else ''
    if args.sqrt:
        tsrc += (f'* √ branch of the band profile: derived independently from Gebendorfer 2026 Lemma 3.3 (module {args.sqrtmod},\n'
                 '  window-scope: `gtau`, `band_profile_sqrt`, `block_bound_w\'_g`, `n_point_bound_w\'_g`, `Phi_g`,\n'
                 '  `Phi_g_ge_sqrt`, `AMW.am_dyadic_n_g`); this branch was first used on riemannzeta.fun by dani-ani0\n'
                 '  (dani-bound-2026).\n')
    # attribution and copyright, first in every header (Sam, via the lead, 10-07)
    attrib = ('Copyright (c) 2026 Samuel Lavery (github: samlavery). Licensed under Apache-2.0. Built on the author\'s\n'
              'riemannzeta.fun submissions attempt-012/013/014. Third-party portions keep the notices listed under\n'
              '"Sources and attributions" below.\n'
              'NOTICE: reuse or adaptation of this file must retain this copyright and attribution notice\n'
              '(Apache-2.0 §4(c)) and must state any changes made (§4(b)).\n'
              'The internal modules are by Samuel Lavery\'s agent team (bridge-port, am-cert, mvt-engine, window-scope);\n'
              'those names, and "the lead", refer to members of that team below.\n\n')
    head = f'''/-
{attrib}Riemann.fail submission: an unconditional critical-line proportion of {kn}/{kd} = {float(K):.7f}, for the
{wtitle} in place of the Montgomery–Taylor window.

The mathematics: Theorem D of the pinned Zeta23 development, re-run for the window profile
v(s) = Σ_{{j<13}} c_j cos(ω_j s) (ω₀ = √2, ω_j = 2πj; {wcoef}), with constant
H_W = 3/2 − cos θ₀/(√2 sin θ₀) − Σ_j c_j²(1/2 − 1/(4π²j²))/(2 sin² θ₀) ≥ {Hdec} (θ₀ = √2/2; proved, `AMW.HW_eq`,
`AMW.HW_ge`), and Ainta's weighted n-point simple-zero refinement at n = {N} (pair weights a_ij and per-gap
pressures b_r, total B = {sum(bnum)}/{SA}; `n_point_bound_w'`), made unconditional by a kernel-checked finite
certificate `{NAME}` for the weighted functional on the {qw} gaps (c = {CN}/{SA}{', ' + leaves.group(1) + ' leaves' if leaves else ''},
half-space by reflection).{taux}  Constant {phis} at m = {M}, ≥ 0.{str(PHI.numerator * 10**9 // PHI.denominator).zfill(9)}.
{meth}
Sources and attributions:
{tsrc}{wsrc}
{csrc}
* ports of Zeta23 (anthropics/zeta-23-lean, Apache-2.0, Copyright (c) 2026 Anthropic, PBC): the XiPrime window
  family (atV, the generic zero side, ModWindow with its antitone hypothesis replaced by a positive-variation
  budget) and the ThmD window lemmas;
* the Zeta Lab bridge (Zeta23Ext.Bridge, Zeta23Ext.BridgeW, MIT), retargeted to the AM window.
Every declaration is proved from the pinned anthropics/zeta-23-lean and Mathlib; no placeholders, no
`native_decide`, no additional axioms; every certificate check is a `decide +kernel` evaluation of the data.
Modules: {', '.join(order)}.
-/
'''
    print(f'final6 {NAME}: SA {SA} cN {CN} B {sum(bnum)} m {M} Phi {float(PHI):.10f} kappa {kn}/{kd} = {float(K):.7f}')
    # external credits: always these; typh and his pyramid table whenever a kept module carries them
    need = ['AMTOPA', 'Zeta23', 'Zeta Lab bridge', 'Ainta'] + (['Gebendorfer'] if args.tau else [])
    need += ['Copyright (c) 2026 Samuel Lavery (github: samlavery)', "Samuel Lavery's agent team", 'NOTICE:']
    if args.sqrt:
        need += ['derived independently from Gebendorfer 2026 Lemma 3.3 (module BrSqrtWS',
                 'first used on riemannzeta.fun by dani-ani0']
        # the shipped √ module is window-scope's clean-room BrSqrtWS (lead, 10-07); no other √ module may be imported
        if args.sqrtmod != 'BrSqrtWS' or 'BrSqrtWS' not in order or 'BrSqrtLM' in order:
            sys.exit(f'√ tail: the import closure must contain BrSqrtWS and not BrSqrtLM (sqrtmod {args.sqrtmod})')
    kept = ''.join(mods[m] for m in order)
    need += [t for t in ('typh', 'five-point-pyramid-2') if t in kept]
    if nbas is not None and int(nbas.group(1)) > 0:
        need.append('six-point-convex-basins-2')
    if derived:
        need.append('seven-point-optimised-window')
    # edge build: every edge certificate and every edge Lean module is credited by name (via --csrc)
    need += [f'AMW.{e[0]}Inst' for e in EDGES] + [m for m in filter(None, args.edgemods.split(','))]
    miss = [t for t in need if t not in head]
    if miss:
        sys.exit(f'header lacks external credits {miss} (kept modules carry them); add them to --csrc')
text = head + '\n'.join('import ' + i for i in imports) + '\n\nset_option linter.all false\n\nset_option Elab.async false\n' \
    + ''.join(bodies) + mt + tail
open(args.out, 'w', encoding='utf-8').write(text)
print(f'{args.out}: {len(text.encode())} bytes (layer {sum(len(b.encode()) for b in bodies)}, mt block {len(mt.encode())}); '
      f'modules {order}; dropped {sorted(drop)}; imports {len(imports)}')
