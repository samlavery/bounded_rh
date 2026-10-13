"""Dual tightening of the class-cap obstruction (Lemma 5.1, refs/Zeta_Geometry_and_Class_Cap.txt:328-339) for a FIXED
window f, in double precision.

For a fixed window, Lemma 5.1 with a per-point mixture of periodic words of mean gap 1/r excludes kappa >= r whenever
H(f) - r(1 - Ef(mix)) < 0.  Ef is linear in the per-point mixture weights and the mean gap is linear too, so the best
mixture at mean gap d is the lower convex envelope E*(d) of e(d) = min{Ef(word) : mean gap d}; in one dimension two
words suffice (Caratheodory).  The window's tightened ceiling is the root of H(f) = r (1 - E*(1/r)).

Ef of a periodic word (q points, gaps g, period L = sum g) by (15) (txt:345-354), valid for any real L > 0 because
the autocorrelation qf(h) = int f(t) f(t+h) dt vanishes for h >= 1:
  Ef + 1 = (1/(qL)) [q^2 qf(0) + 2 sum_{1 <= j < L} |sum_i e^{2 pi i j x_i / L}|^2 qf(j/L)].
qf(h) = z^t M(h) z with M as in (17) (txt:376-379), closed form by txt:414-416.  Gaps may be 0 (coincident points:
(2) is required on [0, inf)^{m-1})."""
import sys, json, math, time
import numpy as np
from scipy.optimize import minimize

S2 = math.sqrt(2.0)

def window_from_cnum(cnum, K=None):
    c = np.array(cnum[1:], float) / cnum[0]
    if K is not None and len(c) < K: c = np.concatenate([c, np.zeros(K - len(c))])
    return c

def make_qf(c, w0=S2):
    """vectorised qf(h) for the window (1/A)(cos(w0 t) + sum c_j cos(2 pi j t))"""
    z = np.concatenate([[1.0], c]); n = len(z)
    w = np.concatenate([[w0], 2 * np.pi * np.arange(1, n)])
    A = 2 * math.sin(w0 / 2) / w0
    def I(nu, theta, h):
        l = 1 - h; ch = -h / 2; x = nu * l / 2
        s = np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / np.where(np.abs(x) < 1e-12, 1.0, x))
        return l * np.cos(nu * ch + theta) * s
    def qf(h):
        h = np.asarray(h, float); out = np.zeros_like(h)
        for i in range(n):
            for k in range(n):
                if z[i] == 0 or z[k] == 0: continue
                out += z[i] * z[k] * 0.5 * (I(w[i] + w[k], w[k] * h, h) + I(w[i] - w[k], -w[k] * h, h))
        out = out / A ** 2
        return np.where(h >= 1, 0.0, out)
    return qf

def H_of(c, w0=S2):
    """(5) for w0 = sqrt 2 (txt:112-113)"""
    a0 = w0 / 2; A = math.sin(a0) / a0
    j = np.arange(1, len(c) + 1)
    D = (1 - 1 / (2 * j ** 2 * np.pi ** 2)) / (2 * A ** 2)
    return 1.5 - a0 / math.tan(a0) - float(np.sum(D * c ** 2))

class QFTable:
    """qf on a fine grid with cubic interpolation (for the optimiser); exact qf for reporting"""
    def __init__(self, qf, N=400001):
        self.h = np.linspace(0, 1, N); self.v = qf(self.h); self.qf = qf; self.N = N
        self.q0 = float(qf(np.array([0.0]))[0])
    def __call__(self, h):
        return np.interp(h, self.h, self.v)

def Ef_word(gaps, T, exact=False):
    g = np.asarray(gaps, float); q = len(g); L = g.sum()
    x = np.concatenate([[0.0], np.cumsum(g)[:-1]])
    jmax = int(math.ceil(L)) - 1
    tot = q * q * T.q0
    if jmax >= 1:
        j = np.arange(1, jmax + 1)
        hj = j / L
        S = np.exp(2j * np.pi * np.outer(j, x) / L).sum(axis=1)
        vals = T.qf(hj) if exact else T(hj)
        tot += 2 * np.sum(np.abs(S) ** 2 * vals)
    return tot / (q * L) - 1

def min_word(T, q, d, starts=12, rng=None):
    """min Ef over words of q points with mean gap d (gaps >= 0, sum = q d)"""
    L = q * d; best = (np.inf, None)
    if q == 1:
        e = Ef_word([L], T); return e, np.array([L])
    rng = rng or np.random.default_rng(0)
    cons = ({'type': 'eq', 'fun': lambda g: g.sum() - L, 'jac': lambda g: np.ones_like(g)},)
    for s in range(starts):
        g0 = rng.dirichlet(np.ones(q) * (0.7 if s % 2 else 2.0)) * L
        if s == 0: g0 = np.full(q, d)
        r = minimize(lambda g: Ef_word(g, T), g0, method='SLSQP', bounds=[(0, L)] * q, constraints=cons,
                     options={'maxiter': 300, 'ftol': 1e-13})
        if r.fun < best[0]: best = (float(r.fun), r.x.copy())
    return best

def lower_hull(pts):
    pts = sorted(pts, key=lambda p: (p[0], p[1]))
    hull = []
    for p in pts:
        if hull and abs(hull[-1][0] - p[0]) < 1e-12:      # same d: keep the lower
            if p[1] < hull[-1][1]: hull.pop()
            else: continue
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2][:2], hull[-1][:2]
            if (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1) <= 0: hull.pop()
            else: break
        hull.append(p)
    return hull

def envelope_at(hull, d):
    for (x1, y1, *_), (x2, y2, *_) in zip(hull[:-1], hull[1:]):
        if x1 <= d <= x2:
            t = (d - x1) / (x2 - x1) if x2 > x1 else 0.0
            return y1 + t * (y2 - y1), (x1, x2, t)
    return None, None

def ceiling_from_hull(H, hull, lo=0.60, hi=0.70):
    def G(r):
        e, _ = envelope_at(hull, 1 / r)
        return H - r * (1 - e)
    a, b = lo, hi
    if G(a) < 0 or G(b) > 0: return None
    for _ in range(200):
        m = (a + b) / 2
        if G(m) >= 0: a = m
        else: b = m
    return a

if __name__ == '__main__':
    src = sys.argv[1]; qmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    dgrid = np.round(np.arange(0.70, 3.001, 0.02), 4)
    cnum = json.load(open(src))['cnum']
    c = window_from_cnum(cnum)
    H = H_of(c); qf = make_qf(c); T = QFTable(qf)
    t0 = time.time()
    # control: the paper's two words, per-point mixture at mean gap 1/r
    A_ = [5189 / 5000, 9811 / 5000]; B_ = [10289 / 10000, 10289 / 10000, 9711 / 5000]
    eA, eB = Ef_word(A_, T, exact=True), Ef_word(B_, T, exact=True)
    hull_paper = [(1.5, eA), (4 / 3, eB)]; hull_paper.sort()
    def Gp(r):
        lam = (1 / r - 1.5) / (4 / 3 - 1.5); return H - r * (1 - ((1 - lam) * eA + lam * eB))
    a, b = 0.60, 0.70
    for _ in range(200):
        m = (a + b) / 2
        if Gp(m) >= 0: a = m
        else: b = m
    print('window %s: H = %.10f; control (paper words): ceiling %.10f' % (src.split('/')[-1], H, a), flush=True)
    pts = []
    rng = np.random.default_rng(7)
    for q in range(1, qmax + 1):
        # Ef jumps up just above integer periods (a new Fourier term enters, qf ~ (1-h) f(1/2)^2 near h = 1), so
        # every integer period L (mean gap L/q) is included, with a coarse grid in between
        dq = sorted(set([round(L / q, 12) for L in range(int(math.ceil(0.7 * q)), int(3.0 * q) + 1)]
                        + [float(x) for x in np.round(np.arange(0.70, 3.001, 0.05), 4)]))
        for d in dq:
            e, g = min_word(T, q, float(d), rng=rng)
            pts.append((float(d), e, q, [round(float(x), 6) for x in g]))
        hull = lower_hull([(p[0], p[1], p[2], p[3]) for p in pts])
        r = ceiling_from_hull(H, hull)
        e, (x1, x2, t) = envelope_at(hull, 1 / r)
        used = [h for h in hull if h[0] in (x1, x2)]
        print('q <= %d: tightened ceiling %.10f  (envelope at d = %.5f between d = %.3f and %.3f, weight %.4f) (%.0fs)'
              % (q, r, 1 / r, x1, x2, t, time.time() - t0), flush=True)
        for h in used: print('    word d=%.3f q=%d Ef=%.9f gaps=%s' % (h[0], h[2], h[1], h[3]), flush=True)
    json.dump(dict(window=src, H=H, control=a, ceiling=r, hull=[list(h) for h in hull]),
              open('dual_%s_q%d.json' % (src.split('/')[-1].replace('.json', ''), qmax), 'w'), indent=1)
