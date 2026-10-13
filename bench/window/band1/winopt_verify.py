"""Verification of the continuum D-form optimum (winopt_cont_B48.json) and of a smooth 25-mode fit to it, outside the
LP's cut set: superlattice periods N = 3..96 (single defect per period), clusters k = 2..5 at N = 64 and 96, triples at
N = 48; delta_true and kappa = 1 - int q a / delta_true; L3 y-Hessian (N=32); far field (N=64)."""
import sys, json, numpy as np
from scipy.optimize import least_squares
from scipy.integrate import quad
sys.argv = [sys.argv[0], 'x', '32']
exec(open('winopt.py').read().split("if __name__ == '__main__':")[0])
cj = json.load(open("winopt_cont_B48.json")); B = cj["B"]; wv = np.array(cj["w"])
hats = lambda a: np.maximum(0, 1 - np.abs(np.asarray(a, float)[:, None] * B - np.arange(B)[None, :]))
qc = lambda a: hats(np.atleast_1d(a)) @ wv
def single_any(q, N, starts):
    J = np.arange(1, N); best = np.inf
    inits = ([unrelaxed(N, dv) for dv in range(1, max(2, N // 2))] if N >= 4 else []) + [rng.uniform(-N / 2, N / 2, N - 2) for _ in range(starts)]
    for z0 in inits:
        if len(z0) == N - 2: best = min(best, minimize(lambda y: energy(y, q, N, J), z0, jac=True, method='L-BFGS-B').fun)
    return best
def verify(name, qfun):
    I1 = quad(lambda a: float(qfun(a)[0]) * a, 0, 1, limit=400, points=list(np.arange(1, B) / B))[0]
    I0 = quad(lambda a: float(qfun(a)[0]), 0, 1, limit=400, points=list(np.arange(1, B) / B))[0]
    per = {}   # energy per non-simple fraction: d / (N^2 (1 - p))
    for N in list(range(3, 49)) + [56, 64, 80, 96]:
        q = qfun(np.arange(1, N) / N); per[('s', N)] = single_any(q, N, 6) / N ** 2 / (2 / N)
    for N in (64, 96):
        q = qfun(np.arange(1, N) / N)
        for k in (2, 3, 4, 5): per[('k%d' % k, N)] = dmin_type(q, N, k, 0, 30)[0] / N ** 2 / (2 * k / N)
    q = qfun(np.arange(1, 48) / 48)
    for t in (1, 2): per[('t%d' % t, 48)] = dmin_type(q, 48, 0, t, 30)[0] / 48 ** 2 / (3 * t / 48)
    key = min(per, key=per.get); dt = per[key]; dinf = per[('s', 96)]
    print('%s: int q a / int q %.6f | delta_true %.6f at %s (isolated N=96: %.6f) | kappa single %.7f, kappa delta_true %.7f'
          % (name, I1 / I0, dt * 0.5 / I0, key, dinf * 0.5 / I0, 1 - I1 / dinf, 1 - I1 / dt), flush=True)
    worst = sorted(per.items(), key=lambda kv: kv[1])[:5]
    print('   lowest five (relative to isolated): ' + ' '.join('%s%s:%.5f' % (k[0], k[1], v / dinf) for k, v in worst), flush=True)
    NN = 32; J = np.arange(1, NN); q = qfun(J / NN); dd, zz = min(single_minima(q, NN, 16), key=lambda t: t[0])
    E = np.exp(2j * np.pi * np.outer(J, zz) / NN); S = E @ np.concatenate([np.ones(NN - 2), [2.0]])
    Hy = 4 * float(np.real(q * (2 * np.pi * J / NN) ** 2 * np.conj(S) * E[:, -1]).sum())
    d1, d0, out, disp, dv = farfield(qfun(np.arange(1, 64) / 64), 64, [0, 1, 2, 3, 4, 5, 6, 8, 10, 15, 20])
    print('   L3 y-Hessian/Delta_1 (N=32) %+.3f | far field N=64 (vacancy -%d): ' % (Hy / dd, dv) + ' '.join('K=%d:%.2e/%.4f' % (K, e / d1 - 1, (d0 - e) / (d0 - d1)) for K, e in out), flush=True)
    return 1 - I1 / dt, dt * 0.5 / I0, I1 * 0.5 / I0
kc, dc, ic = verify('continuum LP window', qc)
al = np.linspace(0.03, 0.97, 200); tg = qc(al) / qc(np.array([0.25]))[0]; Ma = Mmats(al)
def resid(c):
    z = np.concatenate([[1.0], c]); q = np.einsum('jik,i,k->j', Ma, z, z); return q / np.interp(0.25, al, q) - tg
cf = min([least_squares(resid, c0).x for c0 in [R8C, np.zeros(KF)]], key=lambda c: np.abs(resid(c)).max())
print('family fit to the continuum window: max rel. residual %.2e' % (np.abs(resid(cf)).max() / tg.max()), flush=True)
kf, df, if_ = verify('25-mode fit', lambda a: make_qf(cf)(np.atleast_1d(a)))
json.dump({'cont': [kc, dc, ic], 'family': [kf, df, if_], 'c_family': list(map(float, cf))}, open('winopt_verify.json', 'w'), indent=1)
for name, k_, d_, i_ in [('continuum', kc, dc, ic), ('family', kf, df, if_)]:
    print('SHARPNESS %s: kappa %.7f, delta %.6f, int q a %.6f (int q = 1/2): delta\'/delta to beat 0.6735 = %.4f%%, to reach 0.676 = %.4f%%'
          % (name, k_, d_, i_, 100 * i_ / (1 - 0.6735) / d_, 100 * i_ / (1 - 0.676) / d_))
