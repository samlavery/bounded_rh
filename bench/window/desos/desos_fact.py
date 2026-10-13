#!/usr/bin/env python3
"""desos_fact.py IN.json OUT.json [--lift s] [--keep m] [--M log2] [--digits d]

Fejér–Riesz certificate for C(θ) = y₀ + 2 Σ_{b=1}^{n−1} y_b cos(bθ) (y_b = the JSON's g_knots, n = nb).
* y is read exactly (each float as its exact dyadic rational), then y₀ is lifted by s (rational).
* C − m is factored as |A(e^{iθ})|², A(z) = Σ_{j<n} a_j z^j, by the cepstral (minimum-phase) method on 2^M points.
* a_j are rounded to integers over D = 10^digits; y_b are put over a common denominator E.
* Exact integer check: R_k = Y_k·D² − E·Σ_j A_j A_{j+k} (k < n), and MZ = R_0 − 2 Σ_{k≥1} |R_k| > 0.
  Then C(θ) ≥ MZ/(E·D²) for every θ (the Lean lemma `AMW.DESOS.Ccos_ge`).
Writes the integer data (Y, E, A, D, MZ) to OUT.json."""
import json, sys, argparse
from fractions import Fraction as Fr
import numpy as np

ap = argparse.ArgumentParser()
ap.add_argument('inp'); ap.add_argument('out')
ap.add_argument('--lift', default='1/100000')        # s, added to y₀
ap.add_argument('--keep', default=None)              # m: factor C − m (default: half the lift)
ap.add_argument('--M', type=int, default=20)
ap.add_argument('--digits', type=int, default=16)
args = ap.parse_args()

d = json.load(open(args.inp))
# exact coefficients: rational strings ("p/q" or decimals) are read exactly; floats as their exact dyadic values
if 'Y' in d and 'E' in d:                             # window-scope's form: integer numerators over one E
    key = 'Y/E'
    yq = [Fr(int(v), int(d['E'])) for v in d['Y']]
else:
    key = next(k for k in ('y', 'y_b', 'g_knots_exact', 'g_knots') if k in d)
    yq = [Fr(v) if isinstance(v, str) else Fr(v) for v in d[key]]
n = len(yq)
s = Fr(args.lift)
yq[0] += s

M = 2 ** args.M
yf = np.array([float(v) for v in yq])
spec = np.zeros(M); spec[0] = yf[0]; spec[1:n] = yf[1:]; spec[M - n + 1:] = yf[1:][::-1]
C0 = np.fft.fft(spec).real                           # C(2πk/M)
if args.keep:
    m = Fr(args.keep)
elif s > 0:
    m = s / 2
else:                                                # no lift: keep half the certificate's own grid margin (a short decimal)
    assert C0.min() > 0, ('C not positive on the grid and no lift', C0.min())
    m = Fr(C0.min() / 2).limit_denominator(10 ** 12)
    m = Fr(int(m * 10 ** 12), 10 ** 12)
print(f'coefficients from key {key!r}; grid min C {C0.min():.6e}')

# numeric C − m on the grid, then the minimum-phase factor
Cg = C0 - float(m)                                   # C(2πk/M) − m
assert Cg.min() > 0, ('C − m not positive on the grid', Cg.min())
cep = np.fft.ifft(np.log(Cg)).real
fold = np.zeros(M); fold[0] = cep[0] / 2; fold[1:M // 2] = cep[1:M // 2]; fold[M // 2] = cep[M // 2] / 2
Ah = np.exp(np.fft.fft(fold))
a = np.fft.ifft(Ah).real[:n]
tail = np.abs(np.fft.ifft(Ah).real[n:M // 2]).max()

# exact integer data
D = 10 ** args.digits
A = [int(round(v * D)) for v in a]
from math import lcm
E = 1
for v in yq:
    E = lcm(E, v.denominator)
Y = [int(v * E) for v in yq]
assert all(Fr(Y[b], E) == yq[b] for b in range(n))
D2 = D * D
def acor(k): return sum(A[j] * A[j + k] for j in range(n - k))
R = [Y[k] * D2 - E * acor(k) for k in range(n)]
MZ = R[0] - 2 * sum(abs(r) for r in R[1:])
mC = Fr(MZ, E * D2)
print(f'n {n}, lift s {float(s):.3e}, factor C − m with m {float(m):.3e}; grid 2^{args.M}: min(C − m) {Cg.min():.3e}, '
      f'cepstral tail beyond degree n−1: {tail:.2e}')
print(f'a: digits {args.digits}; residual r = C − |A|²: r₀ {float(Fr(R[0], E * D2)):.6e}, '
      f'2Σ|r_k| {float(Fr(2 * sum(abs(r) for r in R[1:]), E * D2)):.3e}; certified m_C = {float(mC):.6e} '
      f'({"OK" if MZ > 0 else "FAIL"})')
print(f'E has {len(str(E))} digits, |Y| ≤ {max(abs(v) for v in Y)}, |A| ≤ {max(abs(v) for v in A)}, products {n * (n + 1) // 2}')
json.dump({'n': n, 'E': E, 'Y': Y, 'D': D, 'A': A, 'MZ': MZ, 'lift': str(s), 'keep': str(m),
           'source': args.inp}, open(args.out, 'w'))
