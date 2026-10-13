"""Robustness of the reported windows: (a) smooth family fit and R8, Delta_1/N with a heavy multistart at N = 32, 48, 64;
(b) the N=32 general optimum as a continuous window (cubic spline through (j/32, q_j), q(1) = 0), kappa_D at N = 24..64
with the heavy multistart and int q a by quadrature.  usage: python3 winopt_robust.py STARTS"""
import sys, json, numpy as np
from scipy.interpolate import CubicSpline
from scipy.integrate import quad
ST = int(sys.argv[1]); sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
cs_fit = np.array(json.load(open('winopt_smoothfit_single_N24.json'))['c'])
for name, cc in [('R8', R8C), ('smooth family fit', cs_fit)]:
    out = []
    for NN in [32, 48, 64]:
        J = np.arange(1, NN); q = q_family(cc, NN); d = min(m[0] for m in single_minima(q, NN, ST)) / NN
        out.append('N=%d Delta_1/N %.6f kappa_D,N %.7f' % (NN, d, 1 - 2 * float(q @ J) / NN ** 2 / d))
    print('%s: %s' % (name, ' | '.join(out)), flush=True)
g = json.load(open('winopt_general_single_N32.json')); gq = np.array(g['q']); gN = g['N']
xs = np.concatenate([np.arange(1, gN) / gN, [1.0]]); ys = np.concatenate([gq, [0.0]]) / gq[0]
spl = CubicSpline(xs, ys, bc_type=((1, 0.0), 'not-a-knot')); qfun = lambda a: np.where(a < 1, spl(np.minimum(a, 1)), 0.0)
fine = np.linspace(0, 0.999, 2001); print('general N=32 window as a spline: min on [0,1) %+.2e' % qfun(fine).min(), flush=True)
I1 = quad(lambda a: float(qfun(a)) * a, 0, 1, limit=400)[0]; I0 = quad(lambda a: float(qfun(a)), 0, 1, limit=400)[0]
for NN in [24, 32, 48, 64]:
    J = np.arange(1, NN); q = qfun(J / NN); d = min(m[0] for m in single_minima(q, NN, ST)) / NN
    print('  general spline N=%d: Delta_1/N %.6f (in units int_0^1 q = 1/2: %.6f)  kappa_D,N %.7f  continuum-numerator kappa %.7f'
          % (NN, d, d * 0.5 / I0, 1 - 2 * float(q @ J) / NN ** 2 / d, 1 - 2 * I1 / d), flush=True)
print('general spline: int q a / int q = %.6f' % (I1 / I0))
