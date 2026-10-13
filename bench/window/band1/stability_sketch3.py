"""Near-lattice perturbation constant: rho(y) = int qf B_y^2 * g''(1) / sum_{n!=0} L_y(n)^2  (AM-GM of the first-order field change
-2 sum_i (d_i - 1) L(n_i) against the nearest-neighbour strain energy g''(1) sum (d_i - 1)^2).  rho >= 1 closes the near-lattice step.
Also with all-neighbour stiffness: replace g''(1) by the full strain form (diagonal g''(1) + 2 sum_{k>=2} g''(k) k^2 ... reported)."""
import sys, json, numpy as np
from fractions import Fraction
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
al = np.linspace(-1, 1, 200001)[1:-1]; da = al[1] - al[0]; qa = qf(np.abs(al)); gpp1 = 2.3757
a4 = float(np.sum(qa * al ** 4) * da)
def L(y, u): B = 2 * (np.cosh(2 * np.pi * al * y) - 1); return np.array([np.sum(qa * B * np.cos(2 * np.pi * al * uu)) * da for uu in np.atleast_1d(u)])
def SB2(y): B = 2 * (np.cosh(2 * np.pi * al * y) - 1); return float(np.sum(qa * B * B) * da)
n = np.arange(1, 301); h = 1e-3
Kpp = np.array([np.sum(qa * (-(2 * np.pi * al) ** 2) * np.cos(2 * np.pi * al * nn)) * da for nn in n])
print('int qf a^4 (two-sided) %.5f; sum_{n!=0} K\'\'(n)^2 %.4f; small-y rho0 = 16 pi^4 a4 g\'\'(1) / sum K\'\'^2 = %.3f'
      % (a4, 2 * np.sum(Kpp ** 2), 16 * np.pi ** 4 * a4 * gpp1 / (2 * np.sum(Kpp ** 2))))
for y in (0.01, 0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.4, 2.0):
    Ln = L(y, n); print('  y=%.2f: rho(y) = %.3f' % (y, SB2(y) * gpp1 / (2 * np.sum(Ln ** 2))), flush=True)
