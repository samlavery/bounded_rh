"""Slack-relative Lemma P (two-sided units, backed-off R8 certificate cert_R8_backed.json).
W = E(Z) - F_C(D(Z)) = s(D) + sum_p R_p + X_pp + X_env  (exact), with
  R_p   = int qf (A_p^2 - 4)                       (pair self-excess, ~ cosh^2(2 pi y)/y^2),
  R_coll= int qf (|sum_p A_p e_p|^2 - |sum_p 2 e_p|^2)   (collective self-excess of all pairs, >= 0 by the pair-block lemma).
Forms tested:  (P1) W >= theta1 * sum_p R_p ;  (P2) W >= theta2 * R_coll.
Measured on: fixed-depth W-minimisers (P = 1..3 pairs, k = 0 or 3 on-line doubles), Delta_B-seeking configurations, and the
coherent class "two equal-depth pairs at half-integer separation".  Also the constants of the deep-depth analytic regime.
usage: python3 lemmaP_rel.py N"""
import sys, numpy as np
NN = int(sys.argv[1])
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN))
def pair_amp(y): return 2 * np.cosh(2 * np.pi * np.outer(J, np.atleast_1d(y)) / N)     # (N-1, P)
def Rself(y):  # two-sided pair self-excess
    A = pair_amp(y); return (2 / N) * (qv[:, None] * (A ** 2 - 4)).sum(0)
def Rcoll(s, y):
    A = pair_amp(y); E = np.exp(2j * np.pi * np.outer(J, s) / N)
    return float((2 / N) * np.sum(qv * (np.abs((A * E).sum(1)) ** 2 - np.abs(2 * E.sum(1)) ** 2)))
def W2(z, n1, k, P, y):
    d, _ = d_and_grad(z, n1, k, P, np.full(P, y) if np.isscalar(y) else y)
    return 2 * (d / N - N * (gN0 - gh0) / 2 - gN0 * (k + P))
print('R8b certificate, N=%d: g(0) %.6f, sigma %.3e' % (N, g0, gh0 - g0), flush=True)
print('pair self-excess R(y) (two-sided):', ' '.join('y=%.2f:%.3e' % (y, Rself(y)[0]) for y in (0.05, 0.1, 0.2, 0.5, 1, 2, 3)), flush=True)
print('(1) fixed-depth W-minimisers: theta1 = W / sum R_p, theta2 = W / R_coll', flush=True)
th1, th2 = np.inf, np.inf
for y in (0.02, 0.05, 0.1, 0.2, 0.3, 0.5, 1.0, 2.0, 3.0):
    row = []
    for (P, k) in ((1, 0), (2, 0), (3, 0), (2, 3), (3, 3)):
        n1 = N - 2 * k - 2 * P; best = (np.inf, None)
        for s0 in range(16):
            z0 = inits(n1, k, P, s0)
            r = minimize(lambda z: d_and_grad(z, n1, k, P, np.full(P, y)), z0, jac=True, method='L-BFGS-B', options={'maxiter': 4000})
            if r.fun < best[0]: best = (r.fun, r.x)
        z = best[1]; w = W2(z, n1, k, P, y); n = n1 + k; s = z[n:n + P]
        t1 = w / float(Rself(np.full(P, y)).sum()); rc = Rcoll(s, np.full(P, y)); t2 = w / rc
        th1, th2 = min(th1, t1), min(th2, t2); row.append('P%dk%d: %.3f/%.3f' % (P, k, t1, t2))
    print('  y=%.2f: theta1/theta2 %s' % (y, ' '.join(row)), flush=True)
print('(2) coherent class: two equal-depth pairs at separation 1/2 (and 3/2), lattice environment elsewhere', flush=True)
for sep in (0.5, 1.5):
    for y in (0.3, 0.5, 1.0, 2.0, 3.0):
        k, P = 0, 2; n1 = N - 4
        base = np.setdiff1d(np.arange(N, dtype=float), [10.0, 11.0, 12.0, 13.0])[:n1]
        best = (np.inf, None)
        for s0 in range(8):
            x0 = np.concatenate([base + rng.normal(0, 0.02 * s0, n1), [11.0, 11.0 + sep]])
            # optimise environment only; pair centres fixed at separation sep
            def f(zz):
                z = np.concatenate([zz, [11.0, 11.0 + sep]]); d, g = d_and_grad(z, n1, k, P, np.full(P, y)); return d, g[:n1]
            r = minimize(f, x0[:n1], jac=True, method='L-BFGS-B', options={'maxiter': 3000})
            if r.fun < best[0]: best = (r.fun, np.concatenate([r.x, [11.0, 11.0 + sep]]))
        z = best[1]; w = W2(z, n1, k, P, y)
        print('  sep %.1f y=%.1f: W %.3e | sum R_p %.3e (theta1 %.4f) | R_coll %.3e (theta2 %.4f)'
              % (sep, y, w, float(Rself(np.full(2, y)).sum()), w / float(Rself(np.full(2, y)).sum()), Rcoll(np.array([11.0, 11.0 + sep]), np.full(2, y)), w / Rcoll(np.array([11.0, 11.0 + sep]), np.full(2, y))), flush=True)
print('MIN over (1): theta1 %.4f  theta2 %.4f' % (th1, th2), flush=True)
# deep-depth constants: L_y(0) = int qf B, R(y), the far-field decay constant of L_y, g on [0, 1/2]
a = J / N
for y in (0.5, 1.0, 2.0, 3.0):
    B = 2 * (np.cosh(2 * np.pi * a * y) - 1); L0 = (2 / N) * np.sum(qv * B)
    us = np.linspace(1, 20, 2000); Lu = (2 / N) * (np.cos(2 * np.pi * np.outer(us, J) / N) @ (qv * B)); CL = float(np.max(np.abs(Lu) * us ** 2))
    print('deep constants y=%.1f: L_y(0) %.3e, sup_{u>=1} u^2 |L_y(u)| %.3e, R(y) %.3e, R/L_y(0)^2 %.3e' % (y, L0, CL, Rself(y)[0], Rself(y)[0] / L0 ** 2), flush=True)
gh = g_of(np.linspace(0.001, 0.5, 500)); print('g on (0, 1/2]: min %.4f (at 1/2), g(0) %.4f' % (gh.min(), g0), flush=True)
