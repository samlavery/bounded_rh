"""Constants for the pencil sketch of Lemma P / the curvature-slack gap (R8, backed certificate v2).
(a) On-lattice core: Psi(y) = int qf B_y^2 + 2 L_y(0) - 2 sum_{n!=0} |L_y(n)|  (two-sided integrals, infinite lattice sums with
    tail bound).  Psi >= 0 for all y  =>  Lemma P for every on-lattice configuration with masses <= 2, using no slack.
(b) The posed curvature-slack gap on PACKED doubles: k consecutive doubles around s, k vacancies far away (periodic N),
    V''_D(s) and slack(D).
(c) Elastic constants: g(n), g'(n), g''(n) at integers (strain coercivity of T_g); K''(n); h^ near the band edge (Bragg term
    for the dilation soft mode); g on [0, 1/2] (cluster bound); |L_y'(n)| (field sensitivity to displacements)."""
import sys, json, numpy as np
from fractions import Fraction
from scipy.integrate import quad
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
cj = json.load(open('cert_R8_backed_v2.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); nb, Dk = 96, 1 / 32
g0 = float(Fraction(cj['g0'])); gh0 = yk[0]
al = np.linspace(-1, 1, 400001)[1:-1]; da = al[1] - al[0]; qa = qf(np.abs(al))
gha = np.interp(np.abs(al), np.arange(nb + 1) * Dk, np.concatenate([yk, [0.0]]))
def L(y, u):
    B = 2 * (np.cosh(2 * np.pi * al * y) - 1); u = np.atleast_1d(u)
    return np.array([np.sum(qa * B * np.cos(2 * np.pi * al * uu)) * da for uu in u])
def SB2(y): B = 2 * (np.cosh(2 * np.pi * al * y) - 1); return float(np.sum(qa * B * B) * da)
print('(a) on-lattice core Psi(y) = int qf B^2 + 2 L(0) - 2 sum_{n!=0} |L(n)|  [tail n > 400 bounded by 2 sup u^2|L|/400]', flush=True)
worst = np.inf
for y in [0.01, 0.03, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.7, 1.0, 1.5, 2.0, 3.0]:
    n = np.arange(1, 401); Ln = L(y, n); L0 = L(y, 0.0)[0]; tail = 2 * np.max(np.abs(Ln[-50:]) * n[-50:] ** 2) / 400
    psi = SB2(y) + 2 * L0 - 2 * (2 * np.sum(np.abs(Ln)) + tail)
    neg = int(np.sum(Ln[:10] > 0))
    worst = min(worst, psi / max(SB2(y) + 2 * L0, 1e-300))
    print('  y=%.2f: int qf B^2 %.4e, 2L(0) %.4e, 2 sum|L(n)| %.4e -> Psi %+.4e (Psi/(int qfB^2 + 2L(0)) %+.4f); sign of L(1..10): %s'
          % (y, SB2(y), 2 * L0, 2 * (2 * np.sum(np.abs(Ln)) + tail), psi, psi / (SB2(y) + 2 * L0), ''.join('+' if v > 0 else '-' for v in Ln[:10])), flush=True)
print('  min Psi/(self) over the grid %+.4f' % worst, flush=True)
# (c) constants
def gfun(u):
    u = np.atleast_1d(u); return np.array([np.sum(gha * np.cos(2 * np.pi * al * uu)) * da for uu in u])
def Kfun(u):
    u = np.atleast_1d(u); return np.array([np.sum(qa * np.cos(2 * np.pi * al * uu)) * da for uu in u])
h = 1e-3; ns = np.arange(1, 7)
gn = gfun(ns); gpp = (gfun(ns + h) - 2 * gn + gfun(ns - h)) / h ** 2; gp = (gfun(ns + h) - gfun(ns - h)) / (2 * h)
Kpp = (Kfun(ns + h) - 2 * Kfun(ns) + Kfun(ns - h)) / h ** 2; Kpp0 = float((Kfun(np.array([h]))[0] * 2 - 2 * Kfun(np.array([0.0]))[0]) / h ** 2)
print('(c) g(n) %s | g\'(n) %s | g\'\'(n) %s' % (np.round(gn, 7), np.round(gp, 6), np.round(gpp, 4)), flush=True)
print('    K\'\'(0) %.4f | K\'\'(n) n=1..6 %s | sum_{n!=0} K\'\'(n) (Poisson: = -K\'\'(0)) %.4f' % (Kpp0, np.round(Kpp, 4), 2 * float(np.sum((Kfun(np.arange(1, 400) + h) - 2 * Kfun(np.arange(1, 400)) + Kfun(np.arange(1, 400) - h)) / h ** 2))), flush=True)
gh = gfun(np.linspace(0, 0.5, 51)); print('    g on [0, 1/2]: decreasing %s, g(1/2) %.4f, g(0) %.4f' % (bool(np.all(np.diff(gh) <= 1e-9)), gh[-1], gh[0]), flush=True)
hh = qf(np.abs(al)) - gha; edge = (al > 0.9) & (al < 1)
print('    h^ = qf - g^: h^(0) %.4f (= qf(0) - g^(0)); min h^ on [0.5, 31/32] %.2e; h^/(1 - a) on [0.9, 1): min %.4f' % (qf(np.array([0.0]))[0] - gh0, hh[(al > 0.5) & (al < 31 / 32)].min(), (hh[edge] / (1 - al[edge])).min()), flush=True)
for y in (0.1, 0.3, 1.0):
    Lp = (L(y, ns + h) - L(y, ns - h)) / (2 * h); print('    |L_y\'(n)| y=%.1f n=1..6: %s (L_y(0) %.4e)' % (y, np.round(np.abs(Lp), 6), L(y, 0.0)[0]), flush=True)
