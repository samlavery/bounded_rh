"""Direct 25-mode family optimisation of kappa_D at grid N (default 48), qf >= 0 on a fine grid, from a starting c (json);
SLSQP with the Danskin gradient (inner: warm start + lattice-dipole inits), robust re-evaluation every round, and an
N-stability report (24, 32, 48, 64, continuum) for the result.  usage: python3 winopt_famopt.py start_json N ROUNDS"""
import sys, json, numpy as np
from scipy.optimize import minimize
START, NOPT, ROUNDS = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
sys.argv = [sys.argv[0], 'x', str(NOPT)]
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
N = NOPT; J = np.arange(1, N); M = Mmats(J / N); Mg = Mmats(np.linspace(0, 0.999, 401))
c = np.array(json.load(open(START))['c']); state = {'y': None}
def obj(cc):
    z = np.concatenate([[1.0], cc]); q = np.einsum('jik,i,k->j', M, z, z); TGT = float(q @ J)
    d, y, S2v = delta1(q, N, y0=state['y'], starts=2, dvs=range(1, 6)); state['y'] = y
    dq = 2 * np.einsum('jik,k->ji', M, z)
    return TGT / d, (((J @ dq) * d - TGT * (S2v @ dq)) / d ** 2)[1:]
cons = {'type': 'ineq', 'fun': lambda cc: np.einsum('jik,i,k->j', Mg, np.concatenate([[1.0], cc]), np.concatenate([[1.0], cc])),
        'jac': lambda cc: (2 * np.einsum('jik,k->ji', Mg, np.concatenate([[1.0], cc])))[:, 1:]}
hist = []
for rd in range(ROUNDS):
    r = minimize(obj, c, jac=True, method='SLSQP', constraints=[cons], options={'maxiter': 60, 'ftol': 1e-13})
    cn = r.x; q = q_family(cn, N); mins = single_minima(q, N, 24); dtrue = min(m[0] for m in mins)
    k_true = 1 - 2 * float(q @ J) / (N * dtrue); k_claim = 1 - 2 * r.fun / N
    qmin = float(cons['fun'](cn).min())
    print('round %d: claimed %.7f  robust %.7f  min qf %+.1e' % (rd, k_claim, k_true, qmin), flush=True)
    hist.append((k_true, cn.copy()))
    if abs(k_claim - k_true) > 1e-6: state['y'] = None
    if rd and abs(hist[-1][0] - hist[-2][0]) < 1e-7: break
    c = cn
k_best, c = max(hist, key=lambda t: t[0])
for NN in [24, 32, 48, 64]:
    kk, dN = kappa_D(q_family(c, NN), NN); qq = q_family(c, NN); d2 = min(m[0] for m in single_minima(qq, NN, 16)) / NN
    print('  N=%d: kappa_D,N %.7f (Delta_1/N %.6f; wide multistart Delta_1/N %.6f)' % (NN, kk, dN, d2), flush=True)
I1, I0, kc = cont_kappa(c, min(dN, d2))
print('FAMOPT N=%d: continuum kappa_D %.7f  delta %.6f  int q a / int q %.6f ; c = %s' % (N, kc, min(dN, d2) / 2, I1 / I0, np.array2string(c, precision=6, max_line_width=300)))
json.dump({'c': list(map(float, c)), 'kappa_D_cont': kc, 'delta': min(dN, d2) / 2, 'I1': I1, 'I0': I0, 'Nopt': N},
          open('winopt_famopt_N%d.json' % N, 'w'), indent=1)
