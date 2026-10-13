"""E14: certificate slack of a single heavy point: k coincident on-line doubles (mass 2k at one site) in a lattice environment,
environment relaxed (periodic model of band1/lemmaP.py, backed R8 certificate).  Is s(D) ~ c k^2 (density floor through the
h-part), as the stack data of e13 suggests?"""
import sys, numpy as np
from scipy.optimize import minimize
NN = int(sys.argv[1]) if len(sys.argv) > 1 else 192
src = open('/Users/samuellavery/work/riemann-submission/bench/window/band1/lemmaP.py').read().split("if __name__ == '__main__':")[0]
src = src.replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN).replace("open('cert_R8_backed.json')",
      "open('/Users/samuellavery/work/riemann-submission/bench/window/band1/cert_R8_backed.json')")
exec(src)
rng = np.random.default_rng(2)
for k in (1, 2, 4, 8, 16, 32):
    n1 = N - 2 * k; x0d = np.full(k, 10.0)
    base = np.array([t for t in range(N) if t not in (10,)], float)[:n1]
    best = np.inf
    for kk in range(3):
        x0 = base + rng.normal(0, 0.03 * kk, n1)
        def f(xx):
            z = np.concatenate([xx, x0d]); d, g = d_and_grad(z, n1, k, 0, np.zeros(0)); return d, g[:n1]
        r = minimize(f, x0, jac=True, method='L-BFGS-B', options={'maxiter': 6000})
        best = min(best, r.fun)
    # slack in lemmaP units: d/N - N (gN0 - gh0)/2 - gN0 * (#doubles)  [the heavy point counted as k doubles]
    # but F_C counts the heavy point as ONE point of mass 2k: g_N(0) (2k)^2 /... use exact F_C on distinct points
    sl_k_doubles = best / N - N * (gN0 - gh0) / 2 - gN0 * k
    # distinct-point F_C: sum m^2 = n1 + (2k)^2 instead of n1 + 4k; in one-sided units F_C/2 contains gN0 * sum(m^2 - m)/2 ...
    sl_heavy = sl_k_doubles - gN0 * (k * (2 * k) - 2 * k) / 2 if k > 1 else sl_k_doubles
    print('k=%2d (mass %2d): slack as k separate doubles %+9.3f | slack as one point of mass 2k %+9.3f | /k^2 %.4f'
          % (k, 2 * k, sl_k_doubles, sl_heavy, sl_heavy / k ** 2), flush=True)
