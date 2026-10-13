"""Global two-point certificate with EXACT positivity.  g^ even, piecewise linear with knots b*Dk (b = 0..nb, g^(A) = 0,
A = nb*Dk); knot values y_b free.  Then g^'' = sum of deltas and, for u != 0,
    g(u) = T(u) / (4 pi^2 u^2),   T(u) = -[J_0 + 2 sum_{b>=1} J_b cos(2 pi b Dk u)],
J_b = (y_{b+1} - 2 y_b + y_{b-1}) / Dk (J_0 = 2 (y_1 - y_0)/Dk; y_{nb} = y_{nb+1} = 0), EXACTLY.  So g >= 0 on R iff the
trigonometric polynomial T >= 0 on one period [0, 1/(2Dk)] (even, period 1/Dk) - a finite check.
LP: max g(0) = Dk (y_0 + 2 sum_{b>=1} y_b)  s.t.  T(u_i) >= 0 (fine grid, refined by cutting planes),  g^ <= qf (fine
alpha grid, qf = 0 off [-1,1]),  y_0 = g^(0) <= g(0).   delta' = g(0)/2 (one-sided, per non-simple zero).
usage: python3 global_cert3.py WINDOW DELTA_TRUE"""
import sys, json, numpy as np
from scipy.optimize import linprog
WIN, DT = sys.argv[1], float(sys.argv[2])
exec(open('global_cert.py').read().split("def b3(t):")[0].replace("WIN = sys.argv[1]; DT = float(sys.argv[2])", "WIN = '%s'; DT = %r" % (WIN, DT)))
def solve(A, Dk, rounds=30):
    nb = int(round(A / Dk)); P = 1 / Dk                      # unknowns y_0..y_{nb-1}
    D2 = np.zeros((nb + 1, nb))                              # J_b as rows over y (b = 0..nb)
    for b in range(nb + 1):
        for (o, w) in ((b - 1, 1), (b, -2), (b + 1, 1)):
            oo = abs(o)
            if 0 <= oo < nb: D2[b, oo] += w / Dk
    D2[0] = 0; D2[0, 0] = -2 / Dk
    if nb > 1: D2[0, 1] = 2 / Dk
    def T_mat(u):
        u = np.asarray(u, float)[:, None]; cs = np.cos(2 * np.pi * np.arange(nb + 1)[None, :] * Dk * u); cs[:, 1:] *= 2
        return -(cs @ D2)
    def gh_mat(a):
        a = np.abs(np.asarray(a, float)); M = np.zeros((len(a), nb)); t = a / Dk; i = np.floor(t).astype(int); fr = t - i
        for r in range(len(a)):
            if i[r] < nb: M[r, i[r]] += 1 - fr[r]
            if i[r] + 1 < nb: M[r, i[r] + 1] += fr[r]
        return M
    g0row = Dk * np.concatenate([[1.0], 2 * np.ones(nb - 1)]); y0row = np.zeros(nb); y0row[0] = 1
    ug = list(np.linspace(1e-4, P / 2, 4000)); ag = np.arange(0, A, Dk / 8); qa = np.where(ag < 1, qfun(np.minimum(ag, 0.99999)), 0.0)
    for rd in range(rounds):
        Ub = np.vstack([-T_mat(np.array(ug)), gh_mat(ag), (y0row - g0row)[None, :]]); bb = np.concatenate([np.zeros(len(ug)), qa, [0.0]])
        r = linprog(-g0row, A_ub=Ub, b_ub=bb, bounds=[(-5, 5)] * nb, method='highs', options={'presolve': False})
        y = r.x; uf = np.linspace(1e-4, P / 2, 200000); Tv = T_mat(uf) @ y; badu = uf[Tv < -1e-12]
        af = np.arange(0, A, Dk / 64); ex = gh_mat(af) @ y - np.where(af < 1, qfun(np.minimum(af, 0.99999)), 0.0); bada = af[ex > 1e-11]
        if len(badu) == 0 and len(bada) == 0: break
        ug += list(badu[:: max(1, len(badu) // 300)]); ag = np.concatenate([ag, bada[:: max(1, len(bada) // 300)]])
        qa = np.where(ag < 1, qfun(np.minimum(ag, 0.99999)), 0.0)
    return -r.fun, float(Tv.min()), float(ex.max()), rd, y
out = {}
for A in (1.0, 1.25, 1.5, 2.0, 3.0):
    for Dk in (1 / 32, 1 / 64):
        g0, Tmin, exmax, rd, y = solve(A, Dk); out['%g,%g' % (A, Dk)] = (g0, list(map(float, y)))
        print('  exact LP A=%.2f Dk=1/%d: g(0) %.6f -> delta\' %.6f = %.2f%% of delta_true  (min T %+.1e, max(g^-qf) %+.1e, %d refinements)'
              % (A, round(1 / Dk), g0, g0 / 2, 100 * g0 / 2 / DT, Tmin, exmax, rd), flush=True)
json.dump({'window': WIN, 'delta_true': DT, 'sols': out}, open('global_cert3_%s.json' % ('R8' if WIN == 'R8' else 'best'), 'w'))
