#!/usr/bin/env python3
"""desos_r8.py CERT.json FACT.json --data DEData --cert cR8 --sos DESOSR8 [--root DIR] [--lifted]

The two Lean modules of the D-track Fejér–Riesz step (interface: bridge-port's AMW.DEDefs):
* DATA (imports AMW.DEDefs only): `AMW.DE.<cert> : PLCert := ⟨DkInv, E, Ys⟩`, from CERT.json's exact Y/E (or, with
  --lifted, from FACT.json's lifted y, for prototypes only);
* SOS (imports AMW.DECertSOS, AMW.<data>): the factor `A/D` from FACT.json, the margin MZ recomputed here against the
  PLCert's own Y/E, the integer checks by `decide +kernel`, and
  `AMW.DE.certG_<suffix> : CertGNonneg <cert>` and, when it holds, `AMW.DE.ghat0_le_g0_<suffix> : y₀ ≤ dk · certC 0`."""
import json, argparse, os
from fractions import Fraction as Fr

ap = argparse.ArgumentParser()
ap.add_argument('cert'); ap.add_argument('fact')
ap.add_argument('--data', required=True); ap.add_argument('--cert', dest='cname', required=True)
ap.add_argument('--sos', required=True); ap.add_argument('--suffix', default='R8')
ap.add_argument('--root', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'rootR8f', 'AMW'))
ap.add_argument('--lifted', action='store_true')
args = ap.parse_args()

C = json.load(open(args.cert)); F = json.load(open(args.fact))
DkInv = int(Fr(C['Dk']).denominator) if Fr(C['Dk']).numerator == 1 else None
assert DkInv, C['Dk']
if args.lifted:
    E, Y = int(F['E']), [int(v) for v in F['Y']]
    src = f"{os.path.basename(args.cert)}, y₀ lifted by {F['lift']} (PROTOTYPE)"
else:
    E, Y = int(C['E']), [int(v) for v in C['Y']]
    assert F['lift'] in ('0', '0/1'), 'the final data must not be lifted'
    src = os.path.basename(args.cert)
n = len(Y); A = [int(v) for v in F['A']]; D = int(F['D'])
assert len(A) == n
# the exact certificate against the PLCert's own Y/E
D2 = D * D
R = [Y[k] * D2 - E * sum(A[j] * A[j + k] for j in range(n - k)) for k in range(n)]
MZ = R[0] - 2 * sum(abs(r) for r in R[1:])
assert MZ >= 0, ('certificate fails against the PLCert data', MZ)
mC = Fr(MZ, E * D2)
g0ok = Y[0] * DkInv <= Y[0] + 2 * sum(Y[1:])
sigma = Fr(Y[0] + 2 * sum(Y[1:]), E * DkInv) - Fr(Y[0], E)
print(f'{args.cname}: n {n}, DkInv {DkInv}, E {E}; m_C = {float(mC):.6e}; ĝ(0) ≤ g(0): {g0ok} (σ = g(0) − ĝ(0) = {sigma})')

def lst(v): return '[' + ', '.join(str(x) for x in v) + ']'
dpath = os.path.join(args.root, args.data + '.lean'); spath = os.path.join(args.root, args.sos + '.lean')
for p in (dpath, spath):
    assert not os.path.exists(p), ('exists', p)
open(dpath, 'w').write(f'''import AMW.DEDefs

/-! ###### AMW/{args.data} — the piecewise-linear certificate `{args.cname}` (data; am-cert, from window-scope's certificate)

Source: `{src}`. Knots `y_k = Ys[k]/E` at `k/{DkInv}`, `k < {n}`. ###### -/

namespace AMW.DE

/-- the certificate's knots -/
def {args.cname} : PLCert := ⟨{DkInv}, {E}, {lst(Y)}⟩

end AMW.DE
''')
s = args.suffix
g0 = (f'''
/-- the integer form of `ĝ(0) ≤ g(0)` -/
theorem chk0_{s} : {args.cname}.Y 0 * ({args.cname}.DkInv : ℤ) ≤ {args.cname}.Y 0 + 2 * ∑ k ∈ Ico 1 {args.cname}.n, {args.cname}.Y k := by
  decide +kernel

/-- **`ĝ(0) ≤ g(0)`** for `{args.cname}` (`σ = g(0) − ĝ(0) = {sigma}`) -/
theorem ghat0_le_g0_{s} : {args.cname}.y 0 ≤ {args.cname}.dk * certC {args.cname} 0 :=
  ghat0_le_g0_of_int {args.cname} (by decide) (by decide) chk0_{s}
''' if g0ok else '')
# the exact slack ĝ(0) − g(0) (always emitted): S = DkInv·Y₀ − (Y₀ + 2ΣY_k) over E·DkInv
S = Y[0] * DkInv - (Y[0] + 2 * sum(Y[1:]))
slack = Fr(S, E * DkInv)
assert slack == -sigma
g0 += f'''
/-- the integer form of the slack `ĝ(0) − g(0)` -/
theorem chkS_{s} : {args.cname}.Y 0 * ({args.cname}.DkInv : ℤ) - ({args.cname}.Y 0 + 2 * ∑ k ∈ Ico 1 {args.cname}.n, {args.cname}.Y k)
    = {S} := by
  decide +kernel

/-- **the exact slack** `ĝ(0) − g(0) = y₀ − Dk · certC {args.cname} 0 = {slack.numerator}/{slack.denominator}` -/
theorem ghat0_sub_g0_{s} : {args.cname}.y 0 - {args.cname}.dk * certC {args.cname} 0 = ({slack.numerator} : ℝ) / {slack.denominator} := by
  rw [ghat0_sub_g0_of_int {args.cname} (by decide) (by decide) {S} chkS_{s}]
  simp only [{args.cname}]
  norm_num
'''
open(spath, 'w').write(f'''import AMW.DECertSOS
import AMW.{args.data}

/-! ###### AMW/{args.sos} — `certC {args.cname} ≥ 0` on ℝ by an integer Fejér–Riesz certificate (am-cert)

The factor `a_j = AL[j]/DC` (`DC = 10^{len(str(D)) - 1}`) is the minimum-phase Fejér–Riesz factor of `C − {F['keep']}`
(cepstral method on 2^20 points, `bench/window/desos/desos_fact.py`), rounded. The exact check (`{n * n}` integer
products) gives `certC {args.cname} ≥ m_C = MZ/(E·DC²) = {float(mC):.6e}`. ###### -/

noncomputable section

open Finset

namespace AMW.DE

namespace SOS{s}

def AL : List ℤ := {lst(A)}
def AC (j : ℕ) : ℤ := AL.getD j 0
def DC : ℕ := {D}
def MZC : ℤ := {MZ}

theorem AC_zero : ∀ j, {args.cname}.n ≤ j → AC j = 0 := by
  intro j hj
  unfold AC
  exact List.getD_eq_default _ _ (by simpa [AL, {args.cname}, PLCert.n] using hj)

/-- **the certificate check** -/
theorem chk : MZC ≤ AMW.DESOS.resZ {args.cname}.Y AC {args.cname}.E DC {args.cname}.n 0
    - 2 * ∑ k ∈ Ico 1 {args.cname}.n, |AMW.DESOS.resZ {args.cname}.Y AC {args.cname}.E DC {args.cname}.n k| := by
  decide +kernel

end SOS{s}

/-- **`certC {args.cname} ≥ 0` on ℝ** (obligation G) -/
theorem certG_{s} : CertGNonneg {args.cname} :=
  certG_of_int {args.cname} SOS{s}.AC SOS{s}.DC (by decide) (by norm_num [SOS{s}.DC]) SOS{s}.AC_zero SOS{s}.MZC
    (by decide) SOS{s}.chk
{g0}
end AMW.DE

end
''')
print('wrote', dpath, os.path.getsize(dpath), 'B;', spath, os.path.getsize(spath), 'B')
