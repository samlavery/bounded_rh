"""Backed-off rational dip certificate for R8 (bridge-port's section 0).
g^ even, piecewise linear on knots b/32 (b = 0..95), g^(3) = 0;  g(u) = Dk sinc^2(Dk u) C(2 pi Dk u),
C(theta) = y_0 + 2 sum_{1<=b<96} y_b cos(b theta).  Constraints:
  C >= m_C on [0, pi];   h^ = qf - g^ >= m_h on [0, 1 - 1/32],  h^ >= 0 on the edge cell [31/32, 1];
  y_32 = 0 exactly;  y_b <= 0 for b >= 32;  g^(0) = y_0 <= g(0) = Dk (y_0 + 2 sum_{b>=1} y_b)  (excess after rounding = sigma).
Objective max g(0).  kappa_cert = 1 - (e_inf + sigma/2) / (g(0)/2).  Knots rounded to Y_b / E (exact rationals).
usage: python3 cert_backed.py m_C m_h [E_exp]"""
import sys, json, numpy as np
from fractions import Fraction
from scipy.optimize import linprog
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
mC, mH = float(sys.argv[1]), float(sys.argv[2]); EEXP = int(sys.argv[3]) if len(sys.argv) > 3 else 40
cnum = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum']
qf = make_qf(window_from_cnum(cnum, 24)); EINF = 0.1597839052404248      # JInf/(2 aInf^2), matches the compiled datum
nb, Dk = 96, 1.0 / 32
def Cmat(th):
    th = np.asarray(th, float)[:, None]; M = 2 * np.cos(th * np.arange(nb)[None, :]); M[:, 0] = 1.0; return M
def ghat_mat(a):
    a = np.asarray(a, float); M = np.zeros((len(a), nb)); t = a / Dk; i = np.floor(t).astype(int); fr = t - i
    for r in range(len(a)):
        if i[r] < nb: M[r, i[r]] += 1 - fr[r]
        if i[r] + 1 < nb: M[r, i[r] + 1] += fr[r]
    return M
g0row = Dk * np.concatenate([[1.0], 2 * np.ones(nb - 1)]); e0 = np.zeros(nb); e0[0] = 1
a_in = np.arange(0, 1 - 1 / 32 + 1e-12, Dk / 64); a_edge = np.linspace(1 - 1 / 32, 0.99999, 200)
th = list(np.linspace(0, np.pi, 6000))
bounds = [(-5, 5)] * 32 + [(0, 0)] + [(-5, 0)] * (nb - 33)                 # y_32 = 0, y_b <= 0 beyond
mu = 3.0; sig_var = True
for outer in range(8):                                                        # Dinkelbach on kappa = 1 - (2 e_inf + sigma)/g(0)
    for it in range(12):
        nv = nb + 1                                                           # variables: y (nb), sigma
        A = np.vstack([np.hstack([-Cmat(np.array(th)), np.zeros((len(th), 1))]),
                       np.hstack([ghat_mat(a_in), np.zeros((len(a_in), 1))]),
                       np.hstack([ghat_mat(a_edge), np.zeros((len(a_edge), 1))]),
                       np.concatenate([e0 - g0row, [-1.0]])[None, :]])         # y_0 - g(0) - sigma <= 0
        b = np.concatenate([np.full(len(th), -mC), qf(a_in) - mH, qf(a_edge) - mH * 32 * (1 - a_edge), [0.0]])
        cobj = np.concatenate([-g0row, [mu]])
        r = linprog(cobj, A_ub=A, b_ub=b, bounds=bounds + [(0, None)], method='highs', options={'presolve': False})
        y = r.x[:nb]; thf = np.linspace(0, np.pi, 400001)
        mn, bad = np.inf, []
        for k in range(0, len(thf), 50000):
            cv = Cmat(thf[k:k + 50000]) @ y; mn = min(mn, cv.min()); bad += list(thf[k:k + 50000][cv < (0.95 * mC if mC > 0 else -1e-9)])
        if not bad: break
        th += bad[:: max(1, len(bad) // 300)]
    g0v = float(g0row @ y); sg = float(r.x[nb]); mu_new = g0v / (2 * EINF + sg)
    if abs(mu_new - mu) < 1e-10: break
    mu = mu_new
r_fun_g0 = g0v
g0f = r_fun_g0
# rationalise
E = 2 ** EEXP
Y = [int(np.floor(v * E)) if i >= 32 else int(np.round(v * E)) for i, v in enumerate(y)]; Y[32] = 0
Y = [min(v, 0) if i >= 32 else v for i, v in enumerate(Y)]
yq = [Fraction(v, E) for v in Y]
g0q = Fraction(1, 32) * (yq[0] + 2 * sum(yq[1:])); sigma = max(Fraction(0), yq[0] - g0q)
yr = np.array([float(v) for v in yq])
# verification of the rounded certificate (float64, fine grids)
Cmin = min((Cmat(thf[k:k + 50000]) @ yr).min() for k in range(0, len(thf), 50000))
af = np.arange(0, 1 - 1 / 32 + 1e-12, Dk / 512); hmin_in = float((qf(af) - ghat_mat(af) @ yr).min())
ae = np.linspace(1 - 1 / 32, 0.999999, 4000); hmin_edge = float(((qf(ae) - ghat_mat(ae) @ yr) / (32 * (1 - ae))).min())
ab = np.arange(1, 3, Dk / 8); beyond = float((ghat_mat(ab) @ yr).max())
kap = 1 - (EINF + float(sigma) / 2) / (float(g0q) / 2)
print('m_C %.1e m_H %.1e: LP g(0) %.8f -> rational g(0) %.10f (sigma %.2e) | kappa_cert %.7f | checks: min C %.3e, min h^ in band %.3e, min h^/(32(1-a)) edge cell %.3e, max g^ beyond 1 %.1e'
      % (mC, mH, g0f, float(g0q), float(sigma), kap, Cmin, hmin_in, hmin_edge, beyond), flush=True)
out = {'window': 'R8 (rwin8.json cnum, AMW.vAM)', 'Dk': '1/32', 'A': 3, 'nb': nb, 'E': str(E),
       'Y': [str(v) for v in Y], 'knots_rational': [str(v) for v in yq],
       'C_definition': 'C(theta) = y_0 + 2 sum_{1<=b<96} y_b cos(b theta), y_b = Y[b]/E; g(u) = (1/32) sinc^2(u/32) C(2 pi u/32)',
       'ghat_definition': 'even, piecewise linear through (b/32, y_b), b = 0..95, zero at 3; y_32 = 0, y_b <= 0 for b >= 32',
       'g0': str(g0q), 'ghat0': str(yq[0]), 'sigma': str(sigma), 'e_inf': EINF, 'delta_prime': float(g0q) / 2,
       'kappa_cert': kap, 'margins_requested': {'m_C': mC, 'm_h_band': mH},
       'margins_verified_float64': {'min_C': Cmin, 'min_hhat_on_[0,31/32]': hmin_in, 'min_hhat_edge_cell_over_32(1-a)': hmin_edge, 'max_ghat_beyond_1': beyond}}
fn = (sys.argv[4] if len(sys.argv) > 4 else 'cert_R8_backed_mC%g_mh%g.json' % (mC, mH)); json.dump(out, open(fn, 'w'), indent=1); print('saved', fn)
