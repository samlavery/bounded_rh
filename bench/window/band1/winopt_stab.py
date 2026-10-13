"""N-stability with delta_true for a grid window (json from winopt.py general): cubic spline through (j/N, q_j), q(1) = 0;
at N = 24, 32, 48, 64: Delta_1 (wide multistart), d_min(k)/(k Delta_1) for k = 2..5, kappa with single delta and with
delta_true = min_k d_min(k)/(2kN), and the continuum-numerator value 1 - int q a / delta_true.  usage: python3 winopt_stab.py json"""
import sys, json, numpy as np
from scipy.interpolate import CubicSpline
from scipy.integrate import quad
src = sys.argv[1]; sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
g = json.load(open(src)); gq = np.array(g['q']); gN = g['N']
spl = CubicSpline(np.concatenate([np.arange(1, gN) / gN, [1.0]]), np.concatenate([gq, [0.0]]) / gq[0], bc_type=((1, 0.0), 'not-a-knot'))
I1 = quad(lambda a: float(spl(a)) * a, 0, 1, limit=400)[0]; I0 = quad(lambda a: float(spl(a)), 0, 1, limit=400)[0]
print('%s as a spline: min on [0,1) %+.2e, int q a / int q %.6f' % (src, spl(np.linspace(0, 0.999, 2001)).min(), I1 / I0), flush=True)
for NN in [24, 32, 48, 64]:
    q = spl(np.arange(1, NN) / NN); J = np.arange(1, NN); d1 = min(m[0] for m in single_minima(q, NN, 48))
    rat = {k: dmin_type(q, NN, k, 0, 90)[0] / (k * d1) for k in (2, 3, 4, 5)}
    dt = d1 * min([1.0] + list(rat.values()))
    print('  N=%d: d_min(k)/(k Delta_1) %s | kappa_D,N single %.7f, delta_true %.7f | continuum-numerator: single %.7f, delta_true %.7f; delta_true (int q = 1/2) %.6f'
          % (NN, ' '.join('k%d:%.5f' % kv for kv in rat.items()), 1 - 2 * float(q @ J) / (NN * d1), 1 - 2 * float(q @ J) / (NN * dt),
             1 - 2 * I1 / (d1 / NN), 1 - 2 * I1 / (dt / NN), dt / NN / 2 * 0.5 / I0), flush=True)
