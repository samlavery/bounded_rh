"""Step 8: certified one-sided chain DP for the field form of Lemma P (canonical certificate v1, R8 window).
LP(D) = s(D) + int qf B_y^2 + 2 sum_{b in D} m_b L_y(x_b - s) >= T_g + int qf B^2 + 4 L(0) + 2 sum_env m_b L(x_b - s)
      >= int qf B^2 + 4 L(0) + 2 Phi_one(y)          (P_h >= 0 and cross-side g >= 0 dropped; two symmetric sides)
Phi_one = min over chains 0 < x_1 < x_2 < ... (masses m_i) of  sum_i [2 m_i L(x_i) + 4 m_i g(x_i)] + sum_consecutive 2 m_i m_j g(x_j - x_i)
          (+ 3 g(0) per triple in the Lemma P' form), plus the tail beyond X.
Certified: cells of width h; one-body / pair terms replaced by their cell minima (fine samples minus Lipschitz slack); a point in
cell k' after one in cell k is at distance in ((k'-k-1)h, (k'-k+1)h).
usage: python3 chain_dp.py H_DEN XMAX MASSES(12|123)"""
import sys, json, time, numpy as np
from fractions import Fraction
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
HD, XMAX, MS = int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
masses = [1, 2] if MS == '12' else [1, 2, 3]
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
cj = json.load(open('cert_R8_backed.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); nb, Dk = 96, 1 / 32
def gfun(u):
    u = np.atleast_1d(np.asarray(u, float)); th = 2 * np.pi * Dk * u
    C = yk[0] + 2 * (np.cos(np.outer(th, np.arange(1, nb))) @ yk[1:]); return Dk * np.sinc(Dk * u) ** 2 * C
g00 = float(gfun(0.0)[0])
al = np.linspace(0, 1, 20001); w_al = np.full(len(al), al[1]); w_al[0] /= 2; w_al[-1] /= 2; qa = qf(np.minimum(al, 0.999999)); qa[-1] = 0
def Lfun(y, x):     # two-sided L_y(x) = int_{-1}^{1} qf B cos = 2 int_0^1
    B = 2 * (np.cosh(2 * np.pi * al * y) - 1); x = np.atleast_1d(x); out = np.empty(len(x))
    for i in range(0, len(x), 4000): out[i:i + 4000] = 2 * (np.cos(2 * np.pi * np.outer(x[i:i + 4000], al)) @ (qa * B * w_al))
    return out
def SB2(y): B = 2 * (np.cosh(2 * np.pi * al * y) - 1); return float(2 * np.sum(qa * B * B * w_al))
h = 1.0 / HD; K = int(round(XMAX / h)); sub = 8
xs = (np.arange(K)[:, None] + (np.arange(sub + 1)[None, :] / sub)) * h          # sample points per cell (incl. endpoints)
gx = gfun(xs.ravel()).reshape(xs.shape)
ug = np.arange(0, (K + 1) * h + 1e-12, h / sub); gu = gfun(ug)
lipg = float(np.max(np.abs(np.diff(gu))) / (h / sub)) * 1.5
gmin_d = np.array([gu[max(0, (d - 1) * sub):(d + 1) * sub + 1].min() for d in range(K + 1)]) - lipg * h / (2 * sub)
gmin_d = np.maximum(gmin_d, 0.0)                                                # g >= 0 (certificate)
t0 = time.time()
print('chain DP: h = 1/%d, X = %g, masses %s, certificate v1 (g(0) %.6f)' % (HD, XMAX, masses, g00), flush=True)
for y in (0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.4):
    Lx = Lfun(y, xs.ravel()).reshape(xs.shape)
    lipL = float(np.max(np.abs(np.diff(Lx, axis=1))) / (h / sub)) * 1.5
    one = {m: np.min(2 * m * Lx + 4 * m * gx, axis=1) - (2 * m * lipL + 4 * m * lipg) * h / (2 * sub) + (3 * g00 if m == 3 else 0.0) for m in masses}
    # backward DP: F[m][k] = min(0, min_{k'>k, m'} one[m'][k'] + 2 m m' gmin(k'-k) + F[m'][k'])
    F = {m: np.zeros(K) for m in masses}; arg = {m: np.full(K, -1, dtype=int) for m in masses}; argm = {m: np.zeros(K, dtype=int) for m in masses}
    for k in range(K - 2, -1, -1):
        d = np.arange(1, K - k)
        for m in masses:
            best = 0.0; bi = -1; bm = 0
            for m2 in masses:
                cand = one[m2][k + 1:] + 2 * m * m2 * gmin_d[d] + F[m2][k + 1:]
                i = int(np.argmin(cand))
                if cand[i] < best: best, bi, bm = float(cand[i]), k + 1 + i, m2
            F[m][k] = best; arg[m][k] = bi; argm[m][k] = bm
    start = min(((one[m][k] + F[m][k], k, m) for m in masses for k in range(K)), key=lambda t: t[0])
    phi_one = min(0.0, start[0])
    # tail beyond X: at most 2 points per unit length of mass <= max(masses) gaining 2 m |L^-|  (crude)
    nt = np.arange(int(XMAX), int(XMAX) + 4000); Lt = Lfun(y, nt + 0.5); CLt = float(np.max(np.abs(Lfun(y, np.linspace(XMAX, XMAX + 3, 200))) * np.linspace(XMAX, XMAX + 3, 200) ** 2))
    tail = -2 * 2 * max(masses) * (CLt / (XMAX - 1)) * 1.0
    L0 = float(Lfun(y, 0.0)[0]); sb = SB2(y)
    lower = sb + 4 * L0 + 2 * (phi_one + tail)
    # reconstruct the binding chain
    chain = []
    if start[0] < 0:
        k, m = start[1], start[2]; chain.append((k, m))
        while arg[m][k] >= 0:
            k, m = arg[m][k], argm[m][k]; chain.append((k, m))
    pts = ' '.join('%.3f(m%d)' % ((k + 0.5) * h, m) for k, m in chain[:14])
    print('  y=%.2f: int qf B^2 %.4e  4L(0) %.4e  2*Phi_one %.4e  2*tail %.2e  -> certified LP lower bound %+.4e  (margin/(int qfB^2) %+.3f)  [%.0fs]'
          % (y, sb, 4 * L0, 2 * phi_one, 2 * tail, lower, lower / sb, time.time() - t0), flush=True)
    print('     binding chain (positions from s, masses): %s%s' % (pts, ' ...' if len(chain) > 14 else ''), flush=True)
