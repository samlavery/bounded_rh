"""B: coherent deep clusters - P pairs at depth y at spacing 1.5 (coherent at alpha = 1, cheap in T_g), lattice environment
relaxed; exact W = E(Z) - F_C(D(Z)) (two-sided), R_coll, sum_p R_p, ||S_B||, env mass near the cluster.
C: size of step 2's sign check: L_y(n) < 0 for 1 <= n, y in (0, 1.4]; tail via L_y(n) = qf'(1) B_y(1) / (2 pi^2 n^2) + O(n^-4)."""
import sys, numpy as np
from scipy.optimize import minimize
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', 96"))
def W2(z, n1, k, P, y):
    d, _ = d_and_grad(z, n1, k, P, np.full(P, y)); return 2 * (d / N - N * (gN0 - gh0) / 2 - gN0 * (k + P))
def SBn(s, y):
    A = 2 * np.cosh(2 * np.pi * np.outer(J, np.full(len(s), y)) / N) - 2; E = np.exp(2j * np.pi * np.outer(J, s) / N)
    return np.sqrt((2 / N) * np.sum(qv * np.abs((A * E).sum(1)) ** 2))
def Rcoll(s, y):
    A = 2 * np.cosh(2 * np.pi * np.outer(J, np.full(len(s), y)) / N); E = np.exp(2j * np.pi * np.outer(J, s) / N)
    return float((2 / N) * np.sum(qv * (np.abs((A * E).sum(1)) ** 2 - np.abs(2 * E.sum(1)) ** 2)))
def Rp(y): A = 2 * np.cosh(2 * np.pi * J * y / N); return float((2 / N) * np.sum(qv * (A ** 2 - 4)))
print('B: coherent clusters, P pairs at spacing 1.5, lattice environment (N = 96), environment relaxed', flush=True)
for y in (1.5, 2.0, 3.0):
    for P in (2, 4, 6, 8):
        s = 20.0 + 1.5 * np.arange(P); n1 = N - 2 * P
        occupied = set(np.round(s).astype(int)) | set(np.floor(s).astype(int))
        base = np.array([t for t in range(N) if t not in occupied], float)[:n1]
        best = (np.inf, None)
        for s0 in range(4):
            x0 = base + rng.normal(0, 0.02 * s0, n1)
            def f(zz):
                z = np.concatenate([zz, s]); d, g = d_and_grad(z, n1, 0, P, np.full(P, y)); return d, g[:n1]
            r = minimize(f, x0, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
            if r.fun < best[0]: best = (r.fun, np.concatenate([r.x, s]))
        z = best[1]; w = W2(z, n1, 0, P, y); rc = Rcoll(s, y); nb_ = SBn(s, y)
        near = int(np.sum(np.abs(z[:n1, None] - s[None, :]).min(1) < 1.0))
        print('  y=%.1f P=%d: W %.3e | R_coll %.3e | sum R_p %.3e (R_coll/sum %.2e) | ||S_B|| %.3e vs 4P + 2M_near = %d | W/R_coll %.4f'
              % (y, P, w, rc, P * Rp(y), rc / (P * Rp(y)), nb_, 4 * P + 2 * near, w / rc), flush=True)
print('C: sign check of L_y(n), y in (0, 1.4]', flush=True)
a = J / N   # reuse the N-grid only for qf; use a fine alpha grid for L
al = np.linspace(0, 1, 40001); wa = np.full(len(al), al[1]); wa[0] /= 2; wa[-1] /= 2; qa = qfun(np.minimum(al, 0.999999)); qa[-1] = 0
qfp1 = (qfun(np.array([0.999999]))[0] - qfun(np.array([0.999]))[0]) / (0.999999 - 0.999)
ys = np.concatenate([np.linspace(0.005, 0.1, 20), np.linspace(0.1, 1.4, 131)[1:]]); ns = np.arange(1, 201)
worst_ratio, worstN0 = np.inf, 0
for y in ys:
    B = 2 * (np.cosh(2 * np.pi * al * y) - 1); f = qa * B
    Ln = 2 * (np.cos(2 * np.pi * np.outer(ns, al)) @ (f * wa))
    lead = qfp1 * 2 * (np.cosh(2 * np.pi * y) - 1) / (2 * np.pi ** 2 * ns ** 2)
    assert np.all(Ln < 0), ('sign fails', y, ns[Ln >= 0][:5])
    rel = np.abs(Ln - lead) / np.abs(lead)
    N0 = int(ns[np.where(rel > 0.5)[0].max()] + 1) if np.any(rel > 0.5) else 1
    worstN0 = max(worstN0, N0)
    dB = 2 * 2 * np.pi * al * np.sinh(2 * np.pi * al * y); D = 2 * np.sum(qa * dB * wa)       # |d L / dy| <= 2 int qf |dB/dy|
    worst_ratio = min(worst_ratio, float(np.min(np.abs(Ln[:N0])) / D))
print('  L_y(n) < 0 for all n = 1..200 on %d y-points in (0, 1.4]: yes' % len(ys))
print('  asymptotic qf\'(1) B_y(1)/(2 pi^2 n^2) within 50%% for n >= N0, N0 (worst over y) = %d   [qf\'(1) = %.4f]' % (worstN0, qfp1))
print('  Lipschitz-in-y cell width needed (min_n<N0 |L_y(n)| / sup|dL/dy|): >= %.2e (relative to y near 0: cells ~ y * const)' % worst_ratio)
