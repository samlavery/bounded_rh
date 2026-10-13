"""L2 at the reported windows: d_min(k)/(k Delta_1) for k = 2, 3, 4 (heavy multistart incl. lattice-dipole inits) at
N = 32, 48; the dilute value with delta_true = min_k d_min(k)/(2kN)."""
import sys, json, numpy as np
from scipy.interpolate import CubicSpline
sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
g = json.load(open('winopt_general_single_N32.json')); gq = np.array(g['q']); gN = g['N']
spl = CubicSpline(np.concatenate([np.arange(1, gN) / gN, [1.0]]), np.concatenate([gq, [0.0]]) / gq[0], bc_type=((1, 0.0), 'not-a-knot'))
cfam = np.array(json.load(open('winopt_smoothfit_single_N24.json'))['c'])
for name, qf in [('R8', lambda NN: q_family(R8C, NN)), ('family', lambda NN: q_family(cfam, NN)), ('general', lambda NN: spl(np.arange(1, NN) / NN))]:
    for NN in [32, 48]:
        q = qf(NN); J = np.arange(1, NN); d1 = min(m[0] for m in single_minima(q, NN, 48))
        rat = {k: dmin_type(q, NN, k, 0, 90)[0] / (k * d1) for k in (2, 3, 4)}
        dtrue = d1 * min([1.0] + list(rat.values()))
        print('%s N=%d: d_min(k)/(k Delta_1): %s | kappa_D,N single %.7f, with delta_true %.7f' % (name, NN, ' '.join('k%d:%.5f' % kv for kv in rat.items()),
              1 - 2 * float(q @ J) / (NN * d1), 1 - 2 * float(q @ J) / (NN * dtrue)), flush=True)
