"""Superlattice scan: a single defect at period N is a superlattice of defects at spacing N, so delta_true <= min over
N >= 3 of Delta_1(N)/2N.  Prints Delta_1(N)/N for N = 3..48 for R8, the smooth family window and a general grid window."""
import sys, json, numpy as np
from scipy.interpolate import CubicSpline
sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
def single_any(q, N, starts):
    J = np.arange(1, N); best = np.inf
    inits = [unrelaxed(N, dv) for dv in range(1, max(2, N // 2))] if N >= 4 else []
    inits += [rng.uniform(-N / 2, N / 2, N - 2) for _ in range(starts)]
    for z0 in inits:
        if len(z0) != N - 2: continue
        r = minimize(lambda y: energy(y, q, N, J), z0, jac=True, method='L-BFGS-B'); best = min(best, r.fun)
    return best
cfam = np.array(json.load(open('winopt_smoothfit_single_N24.json'))['c'])
g = json.load(open('winopt_general_allc1_N24.json')); gq = np.array(g['q']); gN = g['N']
spl = CubicSpline(np.concatenate([np.arange(1, gN) / gN, [1.0]]), np.concatenate([gq, [0.0]]) / gq[0], bc_type=((1, 0.0), 'not-a-knot'))
for name, qf in [('R8', lambda NN: q_family(R8C, NN)), ('family', lambda NN: q_family(cfam, NN)), ('general24', lambda NN: spl(np.arange(1, NN) / NN))]:
    vals = {NN: single_any(qf(NN), NN, 24) / NN for NN in range(3, 49)}
    ref = vals[48]; mn = min(vals, key=vals.get)
    print('%s: Delta_1(N)/N relative to N=48: ' % name + ' '.join('%d:%.4f' % (NN, v / ref) for NN, v in vals.items()), flush=True)
    print('   min at N=%d: ratio %.5f' % (mn, vals[mn] / ref), flush=True)
