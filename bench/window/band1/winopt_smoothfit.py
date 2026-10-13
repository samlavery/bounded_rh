"""Smooth 25-mode fit of a general (grid) window: cubic spline through (j/N, q_j) with q(1) = 0, sampled at 200 points of
(0, 1), least squares over the family with qf >= 0 checked on a fine grid; then kappa_D,N at N = 24..64 and the continuum
value.  usage: python3 winopt_smoothfit.py general_json"""
import sys, json, numpy as np
from scipy.interpolate import CubicSpline
from scipy.optimize import least_squares
sys.argv = [sys.argv[0], 'x', '24'] + sys.argv[1:]
src = sys.argv[3]
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
g = json.load(open(src)); gq = np.array(g['q']); gN = g['N']
xs = np.concatenate([np.arange(1, gN) / gN, [1.0]]); ys = np.concatenate([gq, [0.0]]) / gq[0]
cs = CubicSpline(xs, ys, bc_type=((1, 0.0), 'not-a-knot'))
al = np.linspace(0.0025, 0.9975, 200); tg = cs(al); Ma = Mmats(al); Mg = Mmats(np.linspace(0, 0.999, 801))
def resid(c, lam):
    z = np.concatenate([[1.0], c]); q = np.einsum('jik,i,k->j', Ma, z, z)
    return np.concatenate([q / q[0] - tg, lam * c])
best = None
for lam in [0.0, 1e-4, 1e-3]:
    for c0 in [R8C, np.zeros(KF)]:
        c = least_squares(lambda c: resid(c, lam), c0).x
        z = np.concatenate([[1.0], c]); qmin = np.einsum('jik,i,k->j', Mg, z, z).min()
        r = np.abs(resid(c, 0)).max()
        k32 = kappa_D(q_family(c, 32), 32)[0]
        print('lam %.0e start %s: max resid %.2e, min qf %+.2e, |c| %.3f, kappa_D,32 %.7f' % (lam, 'R8' if c0 is R8C else '0', r, qmin, np.abs(c).max(), k32), flush=True)
        if qmin > -1e-9 and (best is None or k32 > best[0]): best = (k32, c)
c = best[1]
for NN in [24, 32, 48, 64]:
    kk, dN = kappa_D(q_family(c, NN), NN); kr, dr = kappa_D(q_family(R8C, NN), NN)
    print('  N=%d: smooth fit kappa_D,N %.7f (Delta_1/N %.6f) | R8 %.7f (%.6f)' % (NN, kk, dN, kr, dr), flush=True)
I1, I0, kc = cont_kappa(c, dN)
print('SMOOTH FIT continuum: kappa_D %.7f  delta %.6f  int q a / int q %.6f ; c = %s' % (kc, dN / 2, I1 / I0, np.array2string(c, precision=6, max_line_width=300)))
json.dump({'c': list(map(float, c)), 'kappa_D_cont': kc, 'delta': dN / 2, 'I1': I1, 'I0': I0, 'source': src}, open(src.replace('general', 'smoothfit'), 'w'), indent=1)
