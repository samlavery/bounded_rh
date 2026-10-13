"""Local route for D: with density 1 (N = sum of gaps), E - N qf(0) = sum_a [ sum_b m_a m_b K(x_a - x_b) - qf(0) gap_a ] exactly.
Truncating the inner sum with a smooth cutoff w_R (w = 1 on |u| <= R-1, cos^2 taper to 0 at R) is a valid lower bound (K >= 0):
    Phi_R = sum_a [ sum_b m_a m_b K(x_a - x_b) w_R(x_a - x_b) - qf(0) gap_a ]  <=  E - N qf(0),
and for the lattice Phi_R = -N t_R, t_R = sum_n K(n)(1 - w_R(n)).  Measured on the periodic model (N = 64):
  delta_R = min over relaxations of [Phi_R(one dipole) - Phi_R(lattice)] / 4   (one-sided, per non-simple zero),
  L2 under truncation: two dipoles, min over placements, per defect,
  lower side under truncation: min over all-simple configurations of Phi_R + N t_R (extra loss lam_R per point if < 0),
and the resulting kappa_local(R) = 1 - (e_inf + (t_R + lam_R)/2) / delta_R.  usage: python3 local_route.py WINDOW E_INF"""
import sys, json, math, numpy as np
from scipy.optimize import minimize
WIN, EINF = sys.argv[1], float(sys.argv[2])
exec(open('global_cert.py').read().split("def b3(t):")[0].replace("WIN = sys.argv[1]; DT = float(sys.argv[2])", "WIN = '%s'; DT = 1.0" % WIN))
def dF(u):
    h = 1e-6; return (F(u + h) - F(u - h)) / (2 * h)
def wR(u, R):
    a = np.abs(u); return np.where(a <= R - 1, 1.0, np.where(a >= R, 0.0, np.cos(np.pi / 2 * (a - R + 1)) ** 2))
def dwR(u, R):
    a = np.abs(u); s = np.sign(u); return np.where((a > R - 1) & (a < R), -np.pi / 2 * np.sin(np.pi * (a - R + 1)) * s, 0.0)
N = 64
def Phi(x, m, R, grad=False):
    order = np.argsort(x % N); xs = x % N
    d = xs[:, None] - xs[None, :]; d = d - N * np.round(d / N)
    Kd = F(d) ** 2; W = wR(d, R); M = m[:, None] * m[None, :]
    srt = xs[order]; gaps_sorted = np.roll(srt, -1) - srt; gaps_sorted[-1] += N; gaps = np.empty(len(x)); gaps[order] = gaps_sorted
    val = float(np.sum(M * Kd * W) - q0 * np.sum(gaps))    # sum of gaps = N always (periodic) -> the gap term is the constant N q0
    if not grad: return val
    dK = 2 * F(d) * dF(d); g = 2 * np.sum(M * (dK * W + Kd * dwR(d, R)), axis=1)
    return val, g
def lattice(): return np.arange(N, dtype=float), np.ones(N)
def dipole_cfg(centres, dv=2):
    x = np.arange(N, dtype=float); m = np.ones(N); rm = []
    for c in centres: m[c] = 2.0; rm.append((c - dv) % N)
    keep = np.setdiff1d(np.arange(N), rm); return x[keep], m[keep]
def relax(x, m, R, starts=3):
    best = (np.inf, None)
    for s in range(starts):
        x0 = x + (np.random.default_rng(s).normal(0, 0.02, len(x)) if s else 0)
        r = minimize(lambda z: Phi(z, m, R, grad=True), x0, jac=True, method='L-BFGS-B', options={'maxiter': 4000})
        if r.fun < best[0]: best = (r.fun, r.x)
    return best
tR = lambda R: float(np.sum(K(np.arange(-400, 401)) * (1 - wR(np.arange(-400, 401), R))))
xl, ml = lattice(); full = None
print('window %s: e_inf %.6f, qf(0) %.6f' % (WIN, EINF, q0), flush=True)
for R in (2, 3, 4, 5, 6, 8, 10, 14, 20):
    t = tR(R); P0 = Phi(xl, ml, R)
    xd, md = dipole_cfg([N // 2]); e1, _ = relax(xd, md, R); dR = (e1 - P0) / 4
    xd2, md2 = dipole_cfg([N // 2, N // 2 + 7]); e2a, _ = relax(xd2, md2, R)
    xd3, md3 = dipole_cfg([N // 2, N // 2 + 4]); e2b, _ = relax(xd3, md3, R)
    xd4, md4 = dipole_cfg([0, N // 2]); e2c, _ = relax(xd4, md4, R)
    l2 = min(e2a, e2b, e2c); l2r = (l2 - P0) / 8 / dR
    lo = np.inf
    for s in range(4):   # all-simple lower side under truncation
        x0 = xl + np.random.default_rng(10 + s).normal(0, 0.15 * s, N)
        r = minimize(lambda z: Phi(z, ml, R, grad=True), x0, jac=True, method='L-BFGS-B', options={'maxiter': 4000}); lo = min(lo, r.fun)
    lam = max(0.0, -(lo + N * t) / N)
    dtrue = min(dR, dR * l2r)
    kap = 1 - (EINF + (t + lam) / 2) / dtrue
    print('R=%2d: t_R %.2e | delta_R %.6f | two-dipole energy per defect / delta_R %.5f | all-simple min (Phi_R + N t_R)/N %+.2e -> extra loss %.1e | kappa_local %.6f'
          % (R, t, dR, l2r, (lo + N * t) / N, lam, kap), flush=True)
