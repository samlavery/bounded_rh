"""Controlled 25-mode refinement of kappa_D: minimise rho_32 + rho_48 (rho_N = TGT/Delta_1 at grid N, robust inner via
single_minima, Danskin gradient) by L-BFGS-B in a box of +-BOX around the start c, with a quadratic penalty on qf < 0
over a fine grid.  Then the N-stability report, the continuum value and the y-Hessian of the single defect (L3).
usage: python3 winopt_famopt2.py start_json BOX MAXITER"""
import sys, json, time, numpy as np
from scipy.optimize import minimize
START, BOX, MAXIT = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
t0 = time.time(); c0 = np.array(json.load(open(START))['c']); Mg = Mmats(np.linspace(0, 0.999, 401))
grids = {n: (np.arange(1, n), Mmats(np.arange(1, n) / n)) for n in (32, 48)}
def rho(cc, n):
    J, M = grids[n]; z = np.concatenate([[1.0], cc]); q = np.einsum('jik,i,k->j', M, z, z); TGT = float(q @ J)
    best = min(single_minima(q, n, 8), key=lambda t: t[0]); d, zz = best
    S2v = np.abs(np.exp(2j * np.pi * np.outer(J, zz) / n) @ np.concatenate([np.ones(n - 2), [2.0]])) ** 2
    dq = 2 * np.einsum('jik,k->ji', M, z)
    return TGT / d, (((J @ dq) * d - TGT * (S2v @ dq)) / d ** 2)[1:]
def obj(cc):
    r32, g32 = rho(cc, 32); r48, g48 = rho(cc, 48)
    z = np.concatenate([[1.0], cc]); qg = np.einsum('jik,i,k->j', Mg, z, z); neg = np.minimum(qg, 0)
    pen = 1e4 * float(neg @ neg); gpen = 1e4 * 2 * (2 * np.einsum('jik,k->ji', Mg, z))[:, 1:].T @ neg
    return r32 / 32 + r48 / 48 + pen, g32 / 32 + g48 / 48 + gpen
f0 = obj(c0)[0]
r = minimize(obj, c0, jac=True, method='L-BFGS-B', bounds=[(v - BOX, v + BOX) for v in c0], options={'maxiter': MAXIT})
c = r.x; z = np.concatenate([[1.0], c]); qmin = float(np.einsum('jik,i,k->j', Mg, z, z).min())
print('objective %.8f -> %.8f in %d evaluations (%.0fs); min qf %+.2e' % (f0, r.fun, r.nfev, time.time() - t0, qmin), flush=True)
for NN in [24, 32, 48, 64]:
    J = np.arange(1, NN); q = q_family(c, NN); d = min(m[0] for m in single_minima(q, NN, 16))
    print('  N=%d: kappa_D,N %.7f (Delta_1/N %.6f)' % (NN, 1 - 2 * float(q @ J) / (NN * d), d / NN), flush=True)
I1, I0, kc = cont_kappa(c, d / NN)
# L3: y-Hessian at the double of the single-defect optimum, N = 32
NN = 32; J = np.arange(1, NN); q = q_family(c, NN); dd, zz = min(single_minima(q, NN, 16), key=lambda t: t[0])
E = np.exp(2j * np.pi * np.outer(J, zz) / NN); S = E @ np.concatenate([np.ones(NN - 2), [2.0]])
Hy = 4 * float(np.real(q * (2 * np.pi * J / NN) ** 2 * np.conj(S) * E[:, -1]).sum())
print('FAMOPT2: continuum kappa_D %.7f  delta %.6f  int q a / int q %.6f ; single-defect y-Hessian at the double (N=32) %+.3f ; c = %s'
      % (kc, d / NN / 2, I1 / I0, Hy, np.array2string(c, precision=6, max_line_width=300)), flush=True)
json.dump({'c': list(map(float, c)), 'kappa_D_cont': kc, 'delta': d / NN / 2, 'I1': I1, 'I0': I0, 'Hy32': Hy},
          open('winopt_famopt2.json', 'w'), indent=1)
