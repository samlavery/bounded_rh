"""Off-line pairs under the global certificate: the termwise step needs sum_{a,b} g(gamma_a - conj gamma_b) >= charges.
For a pair {s +- iy} replacing the double of a lattice dipole, compare the certificate's g-part with the double's:
  pair:   2 int g^ cosh(4 pi a y) + 2 g(0)  +  sum_n 4 m_n Re g(-n + i y)
  double: 4 g(0)                          +  sum_n 4 m_n g(-n)
(n over the lattice sites, vacancy at -2).  Delta(y) = pair - double; the certificate covers the pair iff Delta(y) >= 0."""
import sys, json, numpy as np
WIN, KEY, LABEL = sys.argv[1], sys.argv[2], sys.argv[3]
sol = json.load(open(WIN))['sols'][KEY]; A, Dk = map(float, KEY.split(',')); y = np.array(sol[1]); nb = len(y)
al = np.linspace(-A, A, 120001); gh = np.interp(np.abs(al), np.arange(nb + 1) * Dk, np.concatenate([y, [0.0]])); da = al[1] - al[0]
g = lambda z: np.sum(gh * np.exp(2j * np.pi * al * z)) * da
g0 = g(0).real; sites = [n for n in range(-60, 61) if n not in (0, -2)]
base = 4 * g0 + sum(4 * g(-n).real for n in sites)
print('%s: g(0) %.6f (two-sided charge per double 2 g(0)); int g^ a^2 = %.4e; lattice-tightness sum_n g(n) (n != 0) %.2e'
      % (LABEL, g0, float(np.sum(gh * al ** 2) * da), sum(g(n).real for n in range(1, 60)) * 2), flush=True)
for yy in (0.01, 0.03, 0.1, 0.2, 0.3, 0.5, 1.0):
    selfb = 2 * float(np.sum(gh * np.cosh(4 * np.pi * al * yy)) * da) + 2 * g0
    cross = sum(4 * g(-n + 1j * yy).real for n in sites)
    print('  depth y=%.2f: Delta(y) = %+.4e  (self-block %+.4e vs 4 g(0) %.4f; cross %+.4e vs %+.4e) -> pair charge / double charge %.4f'
          % (yy, selfb + cross - base, selfb, 4 * g0, cross, base - 4 * g0, (selfb + cross - (base - 4 * g0) - 2 * g0) / (2 * g0)), flush=True)
