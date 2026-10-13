"""(c') g constants with the full support of g^ ([-3, 3]); (b) the posed curvature-slack gap on PACKED doubles and the Lemma P
field quantity for the same configurations (periodic N = 64, on-lattice, unrelaxed and relaxed)."""
import sys, json, numpy as np
from fractions import Fraction
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
cj = json.load(open('cert_R8_backed_v2.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); nb, Dk = 96, 1 / 32
g0 = float(Fraction(cj['g0'])); gh0 = yk[0]
def gfun(u):   # exact closed form g(u) = Dk sinc^2(Dk u) C(2 pi Dk u)
    u = np.atleast_1d(np.asarray(u, float)); th = 2 * np.pi * Dk * u
    C = yk[0] + 2 * (np.cos(np.outer(th, np.arange(1, nb))) @ yk[1:]); return Dk * np.sinc(Dk * u) ** 2 * C
h = 1e-4; ns = np.arange(1, 8)
gn = gfun(ns); gp = (gfun(ns + h) - gfun(ns - h)) / (2 * h); gpp = (gfun(ns + h) - 2 * gn + gfun(ns - h)) / h ** 2
print("(c') g(0) %.6f | g(n) n=1..7 %s | g'(n) %s | g''(n) %s" % (gfun(0.0)[0], np.round(gn, 7), np.round(gp, 6), np.round(gpp, 4)), flush=True)
w = np.linspace(0, 1, 201); gw = gfun(w); print("    g on [0,1]: g(1/4) %.4f g(1/2) %.4f g(3/4) %.4f; decreasing on [0, 0.9]: %s" % (gfun(0.25)[0], gfun(0.5)[0], gfun(0.75)[0], bool(np.all(np.diff(gw[:181]) < 0))), flush=True)
# (b) packed doubles, periodic N
N = 64; J = np.arange(-N + 1, N); qq = np.where(np.abs(J) < N, qf(np.minimum(np.abs(J) / N, 0.99999)), 0.0)
FC = lambda m: (qf(np.array([0.0]))[0] - gh0) * N + g0 * float(np.sum(m ** 2))
def E(x, m): S = np.exp(2j * np.pi * np.outer(J, x) / N) @ m; return float(np.sum(qq * np.abs(S) ** 2) / N)
def Vpp(x, m, s): return float(-np.real(np.sum(qq * (2 * np.pi * J / N) ** 2 * (np.exp(2j * np.pi * np.outer(J, x) / N) @ m) * np.exp(-2j * np.pi * J * s / N))) / N)
def field(x, m, s, y):   # 2 sum_b m_b L_y(x_b - s) = (2/N) sum_j q_j B_j Re(S_j e(-j s/N)) * ... two-sided
    B = 2 * (np.cosh(2 * np.pi * J * y / N) - 1); S = np.exp(2j * np.pi * np.outer(J, x) / N) @ m
    return float(2 * np.real(np.sum(qq * B * S * np.exp(-2j * np.pi * J * s / N))) / N)
def SB2(y): B = 2 * (np.cosh(2 * np.pi * J * y / N) - 1); return float(np.sum(qq * B * B) / N)
print('(b) packed doubles: doubles at s=0 and sites +-1..+-k, the 2k+1 vacancies spread far (sites N/2 +- ...), on-lattice', flush=True)
for k in (0, 1, 2, 3, 5, 8):
    sites = np.arange(N); m = np.ones(N); dbl = [i % N for i in range(-k, k + 1)]
    vac = [(N // 2 + 3 * (i - k)) % N for i in range(2 * k + 1)]
    for d in dbl: m[d] = 2
    keep = np.setdiff1d(sites, vac); x = sites[keep].astype(float); mm = m[keep]
    x = np.where(x > N / 2, x - N, x)
    sl = E(x, mm) - FC(mm); vpp = Vpp(x, mm, 0.0)
    fl = [SB2(y) + field(x, mm, 0.0, y) for y in (0.05, 0.2, 0.5)]
    print("  k=%d (%d doubles): slack %.4f (per double %.4f) | V''_D(s) %+.4f | Lemma P quantity int qf B^2 + field at y=.05/.2/.5: %s"
          % (k, 2 * k + 1, sl, sl / (2 * k + 1), vpp, ' '.join('%+.4e' % v for v in fl)), flush=True)
