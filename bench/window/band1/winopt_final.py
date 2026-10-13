"""Closing checks: far field of the general (spline) window at N=64; L3 y-Hessian at the single-defect optimum for R8, the
smooth family window and the general window (N=32); typed LP check of the general single-defect window at N=24."""
import sys, json, numpy as np
from scipy.interpolate import CubicSpline
sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
g = json.load(open('winopt_general_single_N32.json')); gq = np.array(g['q']); gN = g['N']
spl = CubicSpline(np.concatenate([np.arange(1, gN) / gN, [1.0]]), np.concatenate([gq, [0.0]]) / gq[0], bc_type=((1, 0.0), 'not-a-knot'))
qgen = lambda NN: spl(np.arange(1, NN) / NN)
cfam = np.array(json.load(open('winopt_smoothfit_single_N24.json'))['c'])
Ks = list(range(0, 9)) + [10, 12, 15, 20, 25, 30]
d1, d0, out, disp, dv = farfield(qgen(64), 64, Ks)
print('FAR general window N=64: dipole vacancy at -%d; unrelaxed/Delta_1 - 1 = %.2e' % (dv, d0 / d1 - 1))
print('  ' + ' '.join('K=%d:%.2e/%.4f' % (K, e / d1 - 1, (d0 - e) / (d0 - d1)) for K, e in out), flush=True)
for name, q in [('R8', q_family(R8C, 32)), ('family', q_family(cfam, 32)), ('general', qgen(32))]:
    NN = 32; J = np.arange(1, NN); dd, zz = min(single_minima(q, NN, 32), key=lambda t: t[0])
    E = np.exp(2j * np.pi * np.outer(J, zz) / NN); S = E @ np.concatenate([np.ones(NN - 2), [2.0]])
    Hy = 4 * float(np.real(q * (2 * np.pi * J / NN) ** 2 * np.conj(S) * E[:, -1]).sum())
    print('L3 %s: y-Hessian at the double of the single-defect optimum (N=32) %+.4f (relative to Delta_1: %+.3f)' % (name, Hy, Hy / dd), flush=True)
q24 = np.array(json.load(open('winopt_general_single_N24.json'))['q']); J = np.arange(1, 24)
kD = 1 - 2 * float(q24 @ J) / (24 * min(m[0] for m in single_minima(q24, 24, 32)))
lpv, k1, arg, per_def, dm = typed_lp(q24, 24, 60)
print('CHECK general single-defect window N=24: kappa_D,N %.7f | typed LP min p %.7f (c0 free), c0=1 value %.7f at %s' % (kD, lpv, k1, arg))
dmin1 = dm[(1, 0)][0]
print('  energy per double-equivalent / Delta_1(type search):', ' '.join('%s:%.5f' % (kt, v / dmin1) for kt, v in sorted(per_def.items(), key=lambda t: t[1])[:8]))
