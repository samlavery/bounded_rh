"""Curvature-slack constant: for D with a double at s, maximise V''_D(s) subject to slack(D) <= sigma (SLSQP, analytic
gradients), sigma on a grid (units of 2 delta' = g(0)).  lambda* = sup V''/slack over V'' > 0.  Second-order Lemma P
holds for y^2 <= slack / (2 V''); the curve V''_max(sigma) tells the depth range covered at each slack.
usage: python3 curv_slack.py WINDOW N"""
import sys, numpy as np
from scipy.optimize import minimize
WINN = sys.argv[1:3]
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = WINN[0], int(WINN[1])"))
j = np.arange(-N + 1, N); qq = np.where(np.abs(j) < N, qfun(np.minimum(np.abs(j) / N, 0.99999)), 0.0); w2 = (2 * np.pi * j / N) ** 2
FCc = (qfun(np.array([0.0]))[0] - gh0) * N + gN0 * (N - 2 + 4)       # one double + N-2 simples
def parts(z):   # z = (N-2 simple positions, s); the double sits at s
    x = np.concatenate([z[:-1], z[-1:]]); m = np.concatenate([np.ones(N - 2), [2.0]]); s = z[-1]
    E = np.exp(2j * np.pi * np.outer(j, x) / N); S = E @ m; es = np.exp(-2j * np.pi * j * s / N)
    slack = float(np.sum(qq * np.abs(S) ** 2) / N) - FCc
    gsl = 2 * np.real((qq * np.conj(S))[:, None] * E * m[None, :] * (2j * np.pi * j[:, None] / N)).sum(0) / N
    V = float(-np.real(np.sum(qq * w2 * S * es)) / N)
    dV_dx = -np.real((qq * w2 * es)[:, None] * E * m[None, :] * (2j * np.pi * j[:, None] / N)).sum(0) / N
    dV_ds_extra = -np.real(np.sum(qq * w2 * S * es * (-2j * np.pi * j / N))) / N
    gV = dV_dx.copy(); gV[-1] += dV_ds_extra
    return V, gV, slack, gsl
rng = np.random.default_rng(9); g0u = g0
print('window %s N=%d (units: slack in 2 delta\' = %.4f)' % (WIN, N, g0u), flush=True)
ratio_best = 0
for sig in (0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 4.0):
    best = (-np.inf, None)
    for t in range(16):
        base = np.setdiff1d(np.arange(N, dtype=float), [10.0, 8.0])[: N - 2]
        x0 = base + rng.normal(0, 0.05 + 0.1 * (t % 4), N - 2) if t % 3 else np.sort(rng.uniform(0, N, N - 2))
        z0 = np.concatenate([x0, [10.0 + rng.normal(0, 0.1)]])
        cons = {'type': 'ineq', 'fun': lambda z: sig * g0u - parts(z)[2], 'jac': lambda z: -parts(z)[3]}
        r = minimize(lambda z: (lambda p: (-p[0], -p[1]))(parts(z)), z0, jac=True, method='SLSQP', constraints=[cons], options={'maxiter': 400, 'ftol': 1e-12})
        V, gV, sl, gs = parts(r.x)
        if sl <= sig * g0u * 1.001 and V > best[0]: best = (V, sl)
    V, sl = best
    if V > 0: ratio_best = max(ratio_best, V / max(sl, 1e-12))
    print('  slack <= %.2f: max V\'\'_D(s) %+.4f (slack used %.4f) -> second-order Lemma P covers y <= %s'
          % (sig, V, sl / g0u, '%.3f' % np.sqrt(sl / (2 * V)) if V > 0 else 'all y (V\'\' <= 0)'), flush=True)
print('lambda* (largest V\'\'/slack found, two-sided units) %.4f' % ratio_best)
