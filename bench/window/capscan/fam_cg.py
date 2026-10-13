"""Family dual tightening with MULTI-word mixtures and column generation (double precision; 25-mode family, w0 = sqrt 2,
c unconstrained as in txt:403-404).

For a word pool S and density r, Psi(w) = max_c [H(c) - r(1 - Ef(c, w))] over per-point mixtures w with mean gap 1/r
(Lemma 5.1, txt:328-339) is convex in w (a max of affine functions); it is minimised by Frank-Wolfe over the polytope
{w >= 0, sum w = 1, sum w_k d_k = 1/r} (its vertices are single words or two-word pairs).  The family ceiling U(S) is
the root of min_w Psi = 0 (an upper bound: each mixture obstructs every window).  Column generation: the window c*
maximising at the optimum mixture is handed to the word search (fam_dual.window_words); its tightened ceiling r_{c*}
is a lower bound Lo on the family ceiling over all words; its best words join S."""
import sys, json, math, time, itertools
import numpy as np
from fam_dual import window_words
from dual import H_of

K = 24; S2 = math.sqrt(2.0)
z_w = np.concatenate([[S2], 2 * np.pi * np.arange(1, K + 1)])
A = 2 * math.sin(S2 / 2) / S2

def Mmat(h):
    l = 1 - h; ch = -h / 2
    wi = z_w[:, None]; wk = z_w[None, :]
    def I(nu, th):
        x = nu * l / 2
        s = np.where(np.abs(x) < 1e-14, 1.0, np.sin(x) / np.where(np.abs(x) < 1e-14, 1.0, x))
        return l * np.cos(nu * ch + th) * s
    return 0.5 * (I(wi + wk, wk * h) + I(wi - wk, -wk * h)) / A ** 2

def Cmat():
    n = K + 1; C = np.zeros((n, n))
    I0 = 2 * np.sin(z_w / 2) / z_w
    for i in range(n):
        for k in range(n):
            pp = Mmat(0.0)[i, k] * A ** 2
            al = math.sin(z_w[k] / 2) / z_w[k] + 2 * math.cos(z_w[k] / 2) / z_w[k] ** 2; be = -2 / z_w[k] ** 2
            C[i, k] = pp + al * I0[i] + be * pp
    return C / A ** 2

def Qword(g):
    g = np.asarray(g, float); q = len(g); L = float(round(g.sum())); g = g * L / g.sum()
    x = np.concatenate([[0.0], np.cumsum(g)[:-1]])
    Q = q * q * Mmat(0.0)
    for j in range(1, int(round(L))):
        S = np.exp(2j * np.pi * j * x / L).sum()
        Q += 2 * abs(S) ** 2 * Mmat(j / L)
    return Q / (q * L), L / q

CA = Cmat()

def Psi(Qmix, r):
    P = CA - r * Qmix
    P11 = P[1:, 1:]; P10 = P[1:, 0]
    sol = np.linalg.solve(P11, P10)
    return 2 - 2 * r - P[0, 0] + P10 @ sol, np.concatenate([[1.0], -sol])

def vertices(d, D0):
    V = []
    for i in range(len(d)):
        if abs(d[i] - D0) < 1e-12: V.append(((i,), (1.0,)))
    for i, j in itertools.combinations(range(len(d)), 2):
        lo, hi = (i, j) if d[i] < d[j] else (j, i)
        if d[lo] < D0 < d[hi]:
            t = (D0 - d[lo]) / (d[hi] - d[lo]); V.append(((lo, hi), (1 - t, t)))
    return V

def min_psi(Qs, d, r, iters=300):
    D0 = 1 / r; V = vertices(d, D0)
    if not V: return None
    def mixQ(wv): return sum(wk * Qs[k] for k, wk in enumerate(wv) if wk > 0)
    def vec(v):
        wv = np.zeros(len(d))
        for k, a in zip(*v): wv[k] += a
        return wv
    # start at the best vertex
    vals = [Psi(mixQ(vec(v)), r)[0] for v in V]
    w = vec(V[int(np.argmin(vals))]); val, z = Psi(mixQ(w), r)
    for it in range(iters):
        g = np.array([r * z @ Qk @ z for Qk in Qs])
        s = min((vec(v) for v in V), key=lambda sv: g @ sv)
        dirn = s - w
        if g @ dirn > -1e-15: break
        a, b = 0.0, 1.0
        for _ in range(40):                       # golden section on the convex 1-D restriction
            m1, m2 = a + (b - a) * 0.382, a + (b - a) * 0.618
            if Psi(mixQ(w + m1 * dirn), r)[0] <= Psi(mixQ(w + m2 * dirn), r)[0]: b = m2
            else: a = m1
        w = w + (a + b) / 2 * dirn
        val, z = Psi(mixQ(w), r)
    return val, w, z

def family_U(Qs, d, lo=0.6720, hi=0.6745):
    f = lambda r: min_psi(Qs, d, r)
    flo, fhi = f(lo), f(hi)
    if flo is None or fhi is None or flo[0] < 0 or fhi[0] > 0: return None
    a, b = lo, hi
    while b - a > 1e-10:
        m = (a + b) / 2
        if f(m)[0] >= 0: a = m
        else: b = m
    val, w, z = f(a)
    return a, w, z

if __name__ == '__main__':
    t0 = time.time()
    PA = [5189 / 5000, 9811 / 5000]; PB = [10289 / 10000, 10289 / 10000, 9711 / 5000]
    pool = [PA, PB]
    seed = json.load(open('dual_rwin8_q8_blocks.json'))['hull']          # R8's best words as initial columns
    for h in seed:
        if 1.30 < h[0] < 1.70: pool.append(h[3])
    Qd = [Qword(g) for g in pool]; Qs = [x[0] for x in Qd]; d = [x[1] for x in Qd]
    U, w, z = family_U(Qs, d)
    print('control/start: family U with the paper words + R8 words = %.10f (%d words) (%.0fs)' % (U, len(pool), time.time() - t0), flush=True)
    Lo = 0.0
    for it in range(8):
        c = z[1:]
        rc, used, hl = window_words(c)
        Lo = max(Lo, rc)
        new = 0
        for h in hl:
            if 1.25 < h[0] < 1.75 and not any(len(p) == len(h[3]) and np.allclose(p, h[3], atol=1e-6) for p in pool):
                pool.append(h[3]); Qd.append(Qword(h[3])); new += 1
        Qs = [x[0] for x in Qd]; d = [x[1] for x in Qd]
        U, w, z = family_U(Qs, d)
        act = [(len(pool[k]), round(d[k], 5), round(float(w[k]), 4)) for k in range(len(w)) if w[k] > 1e-4]
        print('it %d: window r_c = %.10f -> Lo = %.10f; +%d words (pool %d); U = %.10f; active (q, d, weight) %s (%.0fs)'
              % (it, rc, Lo, new, len(pool), U, act, time.time() - t0), flush=True)
        if U - Lo < 2e-7: break
    json.dump(dict(U=U, Lo=Lo, c=list(map(float, z[1:])), H=H_of(z[1:]),
                   mixture=[dict(gaps=list(map(float, pool[k])), d=d[k], weight=float(w[k])) for k in range(len(w)) if w[k] > 1e-6]),
              open('fam_cg_K24.json', 'w'), indent=1)
