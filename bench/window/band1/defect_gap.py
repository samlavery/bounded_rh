"""Shallow-depth defect gap (canonical certificate v1).  LP(D, y) = E(Z) - F_C(D(Z)) for one pair at depth y (two-sided);
small-y expansion LP = s(D) + y^2 Q2(D) + R4, Q2 = -2 V''_D(s).
(N1) adversarial: one environment point PINNED at a non-lattice offset c from the pair (forcing D off the lattice through s),
     everything else free; min LP / y^2 for y in {0.03, 0.05, 0.1, 0.2, 0.3}; compared with the unconstrained minimum.
(N2) multi-double curvature-slack curve: q(sigma) = min { Q2(D) : slack(D) <= sigma } over D with k doubles (one at s), k = 1..6.
(N3) remainder: R4 = LP - s - y^2 Q2 on the N1 minimisers, against y^4.
usage: python3 defect_gap.py N"""
import sys, numpy as np
from scipy.optimize import minimize
NN = int(sys.argv[1])
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN))
JJ = np.arange(-N + 1, N); qq = np.where(np.abs(JJ) < N, qfun(np.minimum(np.abs(JJ) / N, 0.99999)), 0.0); q0 = float(qfun(np.array([0.0]))[0])
def S_of(x, m): return np.exp(2j * np.pi * np.outer(JJ, x) / N) @ m
def slack(x, m): return float(np.sum(qq * np.abs(S_of(x, m)) ** 2) / N) - ((q0 - gh0) * N + gN0 * float(np.sum(m ** 2)))
def Vpp(x, m, s): return float(-np.real(np.sum(qq * (2 * np.pi * JJ / N) ** 2 * S_of(x, m) * np.exp(-2j * np.pi * JJ * s / N))) / N)
def LP_of(z, n1, y):     # one pair (centre z[-1]), n1 simples
    d, _ = d_and_grad(z, n1, 0, 1, np.array([y])); return 2 * (d / N - N * (gN0 - gh0) / 2 - gN0 * 1)
print('certificate v1: g(0) %.6f; N = %d' % (g0, N), flush=True)
print('(N1) one env point pinned at offset c from the pair; min LP/y^2 (two-sided)', flush=True)
n1 = N - 2
for c in (None, 0.5, 0.75, 1.25, 1.5, 2.5):
    row = []
    for y in (0.03, 0.05, 0.1, 0.2, 0.3):
        best = (np.inf, None)
        for s0 in range(10):
            z0 = inits(n1, 0, 1, s0)
            if c is None:
                r = minimize(lambda z: d_and_grad(z, n1, 0, 1, np.array([y])), z0, jac=True, method='L-BFGS-B', options={'maxiter': 4000}); z = r.x
            else:
                # pin env point 0 at (pair centre + c): optimise the others and the centre, then set env 0 accordingly
                def f(zz):
                    full = np.concatenate([[zz[-1] + c], zz[:-1], [zz[-1]]]); d, g = d_and_grad(full, n1, 0, 1, np.array([y]))
                    gg = np.concatenate([g[1:n1], [g[0] + g[n1]]]); return d, gg
                zz0 = np.concatenate([z0[1:n1], [z0[-1]]])
                r = minimize(f, zz0, jac=True, method='L-BFGS-B', options={'maxiter': 4000}); z = np.concatenate([[r.x[-1] + c], r.x[:-1], [r.x[-1]]])
            lp = LP_of(z, n1, y)
            if lp < best[0]: best = (lp, z.copy())
        lp, z = best; x = np.concatenate([z[:n1], z[n1:]]); m = np.concatenate([np.ones(n1), [2.0]])
        sl = slack(x, m); q2 = -2 * Vpp(x, m, z[-1])
        row.append('y=%.2f: %.2f (s %.4f, Q2 %.2f, R4/y^4 %+.1f)' % (y, lp / y ** 2, sl, q2, (lp - sl - y ** 2 * q2) / y ** 4))
    print('  c=%s | %s' % ('free' if c is None else '%.2f' % c, ' | '.join(row)), flush=True)
print('(N2) multi-double curvature-slack curve: max V\'\'_D(s) s.t. slack <= sigma, k doubles (one at s); Q2 = -2 V\'\'', flush=True)
for k in (1, 2, 4, 6):
    row = []
    for sig in (0.05, 0.2, 0.5, 1.0, 2.0):
        best = -np.inf
        for t in range(10):
            nsimp = N - 2 * k; dsites = [0] + [int(v) for v in rng.choice(np.arange(-6, 7)[np.arange(-6, 7) != 0], k - 1, replace=False)]
            vac = [int(v) for v in rng.choice(np.arange(N // 2 - 8, N // 2 + 8), k, replace=False)]
            occ = set(dsites) | set(vac); simp = np.array([t2 for t2 in range(-N // 2, N // 2) if t2 not in occ][:nsimp], float)
            x0 = np.concatenate([simp + rng.normal(0, 0.03, len(simp)), np.array(dsites, float)]); m = np.concatenate([np.ones(len(simp)), np.full(k, 2.0)])
            cons = {'type': 'ineq', 'fun': lambda x: sig - slack(np.concatenate([x[:-k], [0.0], x[-k + 1:]]) if k > 1 else np.concatenate([x[:-1], [0.0]]), m)}
            def negV(x):
                xx = np.concatenate([x[:-k], [0.0], x[-k + 1:]]) if k > 1 else np.concatenate([x[:-1], [0.0]])
                return -Vpp(xx, m, 0.0)
            r = minimize(negV, x0, method='SLSQP', constraints=[cons], options={'maxiter': 200, 'ftol': 1e-10})
            xx = np.concatenate([r.x[:-k], [0.0], r.x[-k + 1:]]) if k > 1 else np.concatenate([r.x[:-1], [0.0]])
            if slack(xx, m) <= sig * 1.001: best = max(best, Vpp(xx, m, 0.0))
        row.append('s<=%.2f: Q2 >= %.3f' % (sig, -2 * best))
    print('  k=%d: %s' % (k, ' | '.join(row)), flush=True)
