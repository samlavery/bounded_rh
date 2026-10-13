"""Global two-point certificate, piecewise-linear g^ (hats at knots b*Dk, so the Fejer kernel is in the class exactly):
max g(0) s.t. g >= 0 (u-grid to 600 with cutting planes), g^ <= qf (qf = 0 off [-1,1]), g^(0) <= g(0).  delta' = g(0)/2.
usage: python3 global_cert2.py WINDOW DELTA_TRUE"""
import sys, numpy as np
from scipy.optimize import linprog
WIN, DT = sys.argv[1], float(sys.argv[2])
exec(open('global_cert.py').read().split("def b3(t):")[0].replace("WIN = sys.argv[1]; DT = float(sys.argv[2])", "WIN = '%s'; DT = %r" % (WIN, DT)))
def solve(A, Dk, rounds=12):
    nb = int(round(A / Dk)); cen = np.arange(nb) * Dk        # hats centred at b Dk, half-width Dk, vanishing at A
    hat = lambda t: np.maximum(0, 1 - np.abs(t))
    def ghat_mat(a):
        a = np.asarray(a, float)[:, None]; M = hat((a - cen) / Dk) + hat((a + cen) / Dk); M[:, 0] = hat(a[:, 0] / Dk); return M
    def g_mat(u):
        u = np.asarray(u, float)[:, None]; base = Dk * np.sinc(Dk * u) ** 2
        M = 2 * base * np.cos(2 * np.pi * cen * u); M[:, 0] = base[:, 0]; return M
    g0row = g_mat(np.array([0.0]))[0]; gh0row = ghat_mat(np.array([0.0]))[0]
    ak = np.arange(nb) * Dk; qk = np.where(ak < 1, qfun(np.minimum(ak, 0.99999)), 0.0)    # piecewise linear vs qf: knots + midpoints
    am = ak + Dk / 2; qm = np.where(am < 1, qfun(np.minimum(am, 0.99999)), 0.0)
    ugrid = list(np.arange(0, 80, 0.01))
    for rd in range(rounds):
        Ub = np.vstack([ghat_mat(ak), ghat_mat(am), -g_mat(np.array(ugrid)), (gh0row - g0row)[None, :]])
        bb = np.concatenate([qk, qm, np.zeros(len(ugrid)), [0.0]])
        r = linprog(-g0row, A_ub=Ub, b_ub=bb, bounds=[(-50, 50)] * nb, method="highs", options={"presolve": False})
        if r.x is None: print("    LP status", r.status, r.message, flush=True); return -np.inf, 0, 0, 0, np.zeros(nb), cen
        cv = r.x; ufar = np.arange(0, 800, 0.004); gv = g_mat(ufar) @ cv; bad = ufar[gv < -1e-13]
        if len(bad) == 0: break
        ugrid += list(bad[:: max(1, len(bad) // 500)])
    fa = np.arange(0, A, Dk / 50); va = float(np.max(ghat_mat(fa) @ cv - np.where(fa < 1, qfun(np.minimum(fa, 0.99999)), 0.0)))
    return -r.fun, va, float(-np.sum(np.minimum(gv, 0)) * 0.004 * 2), len(bad), cv, cen
res = {}
for A in (1.0, 1.25, 1.5, 2.0, 3.0):
    for Dk in (1 / 32, 1 / 64):
        g0, va, gneg, nbad, cv, cen = solve(A, Dk); res[(A, Dk)] = (g0, cv, cen)
        print('  hat-basis LP A=%.2f Dk=1/%d: g(0) %.6f -> delta\' %.6f = %.2f%% of delta_true  (max(g^-qf) %+.1e, int g_- %.1e, %d far neg pts)'
              % (A, round(1 / Dk), g0, g0 / 2, 100 * g0 / 2 / DT, va, gneg, nbad), flush=True)
g0, cv, cen = max(res.values(), key=lambda t: t[0])
print('best g^ (knot values at a = 0, 0.25, 0.5, 0.75, 0.9, 1.0, 1.1, 1.25, 1.5):', ' '.join('%.4f' % np.interp(a, cen, cv) for a in (0, .25, .5, .75, .9, 1.0, 1.1, 1.25, 1.5)))
print('qf at the same a:', ' '.join('%.4f' % (qfun(np.array([min(a, 0.99999)]))[0] if a < 1 else 0.0) for a in (0, .25, .5, .75, .9, 1.0, 1.1, 1.25, 1.5)))
