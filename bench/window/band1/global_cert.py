"""Global two-point certificate for D (Cohn-Elkies / Cohn-Kumar shape).
Pair-sum form: E = sum_{a,b} m_a m_b K(x_a - x_b), K = F^2 >= 0, F = f^ (f the window, int f = 1), K^ = qf (supp [-1,1]).
Split K = h + g: g >= 0 pointwise (dropped termwise off the diagonal) and h^ = qf - g^ >= 0 (so sum_{a,b} h >= h^(0) N):
    E - N qf(0) >= g(0) sum_a m_a (m_a - 1) + N [g(0) - g^(0)]
so the certificate needs g >= 0, g^ <= qf (everywhere; qf = 0 off [-1,1]), g^(0) <= g(0), and gives delta' = g(0)/2
(one-sided, per non-simple zero).  LP: max g(0).  g^ = sum of even cubic B-splines (knot step Dk) on [-A, A], free signs.
Band-limited case (A = 1): Fejer-Riesz + Cauchy-Schwarz force g = c sinc^2, delta' = (1/2) inf qf(a)/(1 - |a|) (closed form).
usage: python3 global_cert.py WINDOW(R8|json) DELTA_TRUE"""
import sys, json, math, numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
WIN = sys.argv[1]; DT = float(sys.argv[2])
c = (window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24) if WIN == 'R8'
     else np.array(json.load(open(WIN))['c']))
S2 = math.sqrt(2.0); A0 = 2 * math.sin(S2 / 2) / S2
def F(u):
    u = np.asarray(u, float); a, b = S2 - 2 * np.pi * u, S2 + 2 * np.pi * u
    I = np.where(np.abs(a) < 1e-12, 0.5, np.sin(a / 2) / np.where(np.abs(a) < 1e-12, 1, a)) + np.where(np.abs(b) < 1e-12, 0.5, np.sin(b / 2) / np.where(np.abs(b) < 1e-12, 1, b))
    return (I + sum(cj * 0.5 * (np.sinc(u - (j + 1)) + np.sinc(u + (j + 1))) for j, cj in enumerate(c))) / A0
K = lambda u: F(u) ** 2
qfun = make_qf(c); q0 = float(qfun(np.array([0.0]))[0])
print('window %s: K(0) = F(0)^2 = %.8f, qf(0) = %.6f; lattice check sum_n K(n) = %.8f (= qf(0))' % (WIN, K(0.0), q0, float(K(0.0) + 2 * np.sum(K(np.arange(1, 200000))))), flush=True)
al = np.linspace(0, 0.9999, 20000); ratio = qfun(al) / (1 - al); i = int(np.argmin(ratio))
print('band-limited global certificate (A = 1, closed form): delta\' = inf qf/(1-a) / 2 = %.6f at a = %.4f  -> %.2f%% of delta_true %.6f'
      % (ratio[i] / 2, al[i], 100 * ratio[i] / 2 / DT, DT), flush=True)

def b3(t):
    t = np.abs(t); return np.where(t < 1, 2 / 3 - t ** 2 + t ** 3 / 2, np.where(t < 2, (2 - t) ** 3 / 6, 0.0))
def solve(A, Dk, U=60.0, du=0.01, rounds=8):
    nb = int(round(A / Dk)) - 1; cen = np.arange(nb + 1) * Dk          # splines with support inside [-A, A]
    def ghat_mat(a):   # (len(a), nb+1)
        a = np.asarray(a, float)[:, None]; M = b3((a - cen) / Dk) + b3((a + cen) / Dk); M[:, 0] = b3(a[:, 0] / Dk); return M
    def g_mat(u):
        u = np.asarray(u, float)[:, None]; base = Dk * np.sinc(Dk * u) ** 4
        M = 2 * base * np.cos(2 * np.pi * cen * u); M[:, 0] = base[:, 0]; return M
    g0row = g_mat(np.array([0.0]))[0]; gh0row = ghat_mat(np.array([0.0]))[0]
    agrid = np.arange(0, A + Dk, Dk / 8); qa = np.where(agrid < 1, qfun(np.minimum(agrid, 0.99999)), 0.0)
    ugrid = list(np.arange(0, U, du))
    for rd in range(rounds):
        Ub = np.vstack([ghat_mat(agrid), -g_mat(np.array(ugrid)), (gh0row - g0row)[None, :]])
        bb = np.concatenate([qa, np.zeros(len(ugrid)), [0.0]])
        r = linprog(-g0row, A_ub=Ub, b_ub=bb, bounds=[(None, None)] * (nb + 1), method='highs')
        if r.status != 0: return None
        cv = r.x; ufar = np.arange(0, 600, 0.005); gv = g_mat(ufar) @ cv
        bad = ufar[gv < -1e-12]
        fine_a = np.arange(0, A + Dk, Dk / 64); gha = ghat_mat(fine_a) @ cv; qfa = np.where(fine_a < 1, qfun(np.minimum(fine_a, 0.99999)), 0.0)
        viol_a = float(np.max(gha - qfa))
        if len(bad) == 0 and viol_a < 1e-9: break
        ugrid += list(bad[:: max(1, len(bad) // 400)]); agrid = np.unique(np.concatenate([agrid, fine_a[gha - qfa > 1e-10]]))
    gneg = float(np.sum(np.minimum(gv, 0)) * 0.005 * 2)
    return -r.fun, viol_a, gneg, len(bad)

for A in (1.0, 1.25, 1.5, 2.0, 3.0, 4.0):
    for Dk in (1 / 16, 1 / 32):
        out = solve(A, Dk)
        if out is None: print('  A=%.2f Dk=1/%d: LP failed' % (A, round(1 / Dk))); continue
        g0, va, gneg, nbad = out
        print('  general LP A=%.2f Dk=1/%d: g(0) %.6f -> delta\' %.6f = %.2f%% of delta_true  (residual: max(g^ - qf) %.1e, int g_- %.1e, %d far points < 0)'
              % (A, round(1 / Dk), g0, g0 / 2, 100 * g0 / 2 / DT, va, gneg, nbad), flush=True)
