"""Soundness probe for crowd_dp.py: heuristic minimisation of the SAME relaxed one-sided objective the DP bounds,
  V_side = sum_i [m_i psi_y(u_i) + 4 m_i g(u_i)/y^2] + sum_i 2 m_i m_{i+1} g(u_{i+1} - u_i)/y^2,
over chains 0 < u_1 < ... < u_n <= 128 (gaps free, masses 1/2 by greedy flips), many starts, at fixed y.
The DP gives a certified lower bound for min over y in an interval; every feasible value found here must lie above it
(S0(y) + 2 V_side >= DP bound for 'ALL D').  Also reports the slack check (1) of crowd_check.py done through g^ directly."""
import sys, numpy as np
from scipy.optimize import minimize
from scipy.interpolate import CubicSpline
sys.argv = ['crowd_dp.py', '128']
import crowd_dp as C
UG = np.arange(0, 130.0001, 1 / 1024); gS = CubicSpline(UG, C.gfun(UG))
rng = np.random.default_rng(11)
def make(y):
    pS = CubicSpline(UG, (C.cjs(UG) * np.array([y ** (2 * j) for j in range(C.J)])[:, None]).sum(0)); iy2 = 1 / y ** 2
    def V(w, m):
        u = np.cumsum(w); val = m @ pS(u) + 4 * iy2 * (m @ gS(u)) + 2 * iy2 * np.sum(m[1:] * m[:-1] * gS(w[1:]))
        du = m * pS(u, 1) + 4 * iy2 * m * gS(u, 1)            # d/du_i
        gw = np.cumsum(du[::-1])[::-1]                          # d/dw_k = sum_{i >= k} d/du_i
        gw[1:] += 2 * iy2 * m[1:] * m[:-1] * gS(w[1:], 1)
        return val, gw
    return V
def starts(n):
    out = []
    for kind in range(10):
        w = np.ones(n)
        if kind == 1: w[:] = 1.026
        if kind == 2: w[:] = 0.985
        if kind == 3: w = w + rng.normal(0, 0.03, n)
        if kind == 4: w[0] = 0.85
        if kind == 5: w[0] = 0.79; w[1] = 1.1
        if kind == 6: w = rng.choice([1.026, 0.974, 1.0, 1.988, 2.087], n)
        if kind == 7: w[:] = 1.013
        if kind == 8: w[0] = 0.9; w[1:] = 1.02
        if kind == 9: w = rng.uniform(0.5, 1.6, n)
        m = np.full(n, 2.0) if kind % 3 != 2 else rng.choice([1.0, 2.0], n)
        out.append((np.maximum(w, 1e-3), m))
    return out
def minimise(y, n=128):
    V = make(y); best = (np.inf, None, None)
    for w, m in starts(n):
        for it in range(4):
            r = minimize(lambda z: V(z, m), w, jac=True, method='L-BFGS-B', bounds=[(0, 3)] * len(w), options={'maxiter': 5000})
            w = r.x; v0 = V(w, m)[0]; ch = False
            for i in range(min(len(m), 12)):
                mm = m.copy(); mm[i] = 3 - m[i]; v = V(w, mm)[0]
                if v < v0 - 1e-9: m, v0, ch = mm, v, True
            u = np.cumsum(w); keep = u <= 128; w, m = w[keep], m[keep]
            if not ch: break
        v = V(w, m)[0]
        if v < best[0]: best = (v, np.cumsum(w), m.copy())
    return best
print('slack check through g^ (N = 64): (1/N) sum_j g^(j/N)|S_j|^2 - g_N(0) sum m^2 vs image-sum T_g', flush=True)
N = 64; js = np.arange(-3 * N, 3 * N + 1)
ghat = lambda a: np.interp(np.abs(a), np.arange(len(C.yk) + 1) * C.Dk, np.concatenate([C.yk, [0.0]]), right=0.0)
x = np.sort(rng.uniform(0, N, 50)); m = rng.choice([1.0, 2.0], 50); S = np.exp(2j * np.pi * np.outer(js, x) / N) @ m
TgF = float(np.sum(ghat(js / N) * np.abs(S) ** 2) / N) - float(np.sum(ghat(js / N)) / N) * float(np.sum(m ** 2))
for nim in (40, 400):
    gN = lambda u: sum(C.gfun(u + k * N) for k in range(-nim, nim + 1))
    D = x[:, None] - x[None, :]; G = gN(D.ravel()).reshape(D.shape); np.fill_diagonal(G, 0.0)
    print('   images +-%d: T_g %.8f ; Fourier form %.8f' % (nim, float(m @ G @ m), TgF), flush=True)
ug = np.linspace(0, 6, 60001); g2 = np.gradient(np.gradient(C.gfun(ug), ug), ug)
print('max |g\'\'| on [0,6] (finite differences) %.4f <= M2g %.4f' % (np.max(np.abs(g2[2:-2])), C.M2g), flush=True)
print('heuristic min of the relaxed objective (feasible values: must be >= the DP bound)', flush=True)
for y in (0.05, 0.1, 0.1625, 0.17, 0.175, 0.2, 0.25, 0.3, 0.4):
    v, u, m = minimise(y)
    print('   y=%.4f: S0 + 2 min V_side <= %+.4f   chain %s ...' % (y, C.S0(y) + 2 * v, ' '.join('%.3f(m%d)' % (a, b) for a, b in zip(u[:6], m[:6]))), flush=True)
