"""Class-cap obstruction (Gebendorfer, refs/Zeta_Geometry_and_Class_Cap.txt), reconstructed from the text.

Window (txt:94-98): f(t) = (1/A)(cos(w0 t) + sum_j c_j cos(2 pi j t)) on [-1/2, 1/2], A = int cos(w0 t) = 2 sin(w0/2)/w0
  (his w0 = sqrt 2, a0 = w0/2 = 1/sqrt 2, A = sin(a0)/a0).
H(f) = 2 - C(f), C(f) = int f^2 + int int |t-u| f(t) f(u)  (txt:79, 106-107); for w0 = sqrt 2 this is (5):
  H = H0 - c^t D c, H0 = 3/2 - a0 cot a0, D_jj = (1 - 1/(2 j^2 pi^2))/(2 A^2)  (txt:112-113).
Pair energy of a periodic word (13), by Poisson (15) (txt:320-354):
  Ef + 1 = (1/(qL)) [q^2 qf(0) + 2 sum_{1<=j<L} |sum_i e^{2 pi i j x_i/L}|^2 qf(j/L)],  qf(h) = z^t M(h) z  (17),
  M_ik(h) = (1/A^2) int_{-1/2}^{1/2-h} cos(w_i t) cos(w_k (t+h)) dt  (txt:376-379), z = (1, c).
Mixture: weight lam on config B so that the mean gap is 1/r (txt:366-370).
Obstruction (txt:395-403, Lemma 5.1 txt:328-331): Fobs(r) = max_c [H(f) - r (1 - Ef)]; if Fobs(r) < 0 then every
certificate in the family has kappa < r.  General form (any w0): Fobs = 2 - 2r - P00 + P10^t P11^{-1} P10 with
P = Cmat/A^2 - r Q (P11 > 0 required); for w0 = sqrt 2 it is his b0 + v^t A^{-1} v.
"""
import mpmath as mp

def sinc(x):
    return mp.mpf(1) if x == 0 else mp.sin(x) / x

def int_cos(nu, theta, h):
    """int_{-1/2}^{1/2-h} cos(nu t + theta) dt = l cos(nu c_h + theta) sinc(nu l / 2), l = 1-h, c_h = -h/2 (txt:414-416)"""
    l = 1 - h; ch = -h / 2
    return l * mp.cos(nu * ch + theta) * sinc(nu * l / 2)

def freqs(K, w0):
    return [mp.mpf(w0)] + [2 * mp.pi * j for j in range(1, K + 1)]

def Amass(w0):
    w0 = mp.mpf(w0); return mp.mpf(1) if w0 == 0 else 2 * mp.sin(w0 / 2) / w0

def Mmat(h, w, A):
    """M_ik(h) = (1/A^2) int cos(w_i t) cos(w_k (t + h)) dt over [-1/2, 1/2 - h], by product-to-sum"""
    n = len(w); M = mp.matrix(n, n)
    for i in range(n):
        for k in range(n):
            s = int_cos(w[i] + w[k], w[k] * h, h) + int_cos(w[i] - w[k], -w[k] * h, h)
            M[i, k] = s / 2 / A ** 2
    return M

def psi_coef(w):
    """int_{-1/2}^{1/2} |t-u| cos(w u) du = alpha(w) + beta(w) cos(w t) (w != 0):
    alpha = sin(w/2)/w + 2 cos(w/2)/w^2, beta = -2/w^2"""
    return mp.sin(w / 2) / w + 2 * mp.cos(w / 2) / w ** 2, -2 / w ** 2

def Cmat(w):
    """C_ik = int phi_i phi_k + int int |t-u| phi_i(t) phi_k(u), phi_i = cos(w_i t) on [-1/2,1/2]"""
    n = len(w); C = mp.matrix(n, n)
    I0 = [int_cos(wi, 0, 0) for wi in w]                               # int phi_i
    for i in range(n):
        for k in range(n):
            pp = int_cos(w[i] + w[k], 0, 0) / 2 + int_cos(w[i] - w[k], 0, 0) / 2   # int phi_i phi_k
            if w[k] == 0:      # constant basis function: int |t-u| du = t^2 + 1/4
                C[i, k] = pp + mp.quad(lambda t: mp.cos(w[i] * t) * (t * t + mp.mpf(1) / 4), [-0.5, 0, 0.5])
                continue
            al, be = psi_coef(w[k])
            C[i, k] = pp + al * I0[i] + be * pp
    return C

def Qconf(q, L, x, w, A):
    """Ef + 1 = z^t Q z for one periodic word with points x (period L, integer L), via (15)"""
    n = len(w); Q = mp.matrix(n, n)
    Q += (q * q) * Mmat(mp.mpf(0), w, A)
    for j in range(1, L):
        s = sum(mp.expjpi(2 * mp.mpf(j) * xi / L) for xi in x)
        Q += 2 * abs(s) ** 2 * Mmat(mp.mpf(j) / L, w, A)
    return Q / (q * L)

def word_points(gaps):
    x = [mp.mpf(0)]
    for g in gaps[:-1]: x.append(x[-1] + g)
    return x

def obstruction(r, w, A, confs, Cm=None, ret_c=False):
    """Fobs(r) for a two-configuration mixture confs = [(q, L, gaps), (q, L, gaps)], weight on the second set so
    that the mean gap is 1/r; Cm = Cmat(w) (precomputed)."""
    r = mp.mpf(r)
    (qa, La, ga), (qb, Lb, gb) = confs
    da, db = mp.mpf(La) / qa, mp.mpf(Lb) / qb
    lam = (1 / r - da) / (db - da)
    QA = Qconf(qa, La, word_points(ga), w, A); QB = Qconf(qb, Lb, word_points(gb), w, A)
    Q = (1 - lam) * QA + lam * QB
    if Cm is None: Cm = Cmat(w)
    P = Cm / A ** 2 - r * Q
    n = len(w)
    P11 = P[1:n, 1:n]; P10 = P[1:n, 0]
    sol = mp.lu_solve(P11, P10)
    val = 2 - 2 * r - P[0, 0] + (P10.T * sol)[0, 0]
    if ret_c: return val, lam, -sol, P11
    return val, lam

def prep(w, A, confs):
    """precompute Cmat and the two configuration matrices (they do not depend on r)"""
    (qa, La, ga), (qb, Lb, gb) = confs
    return dict(Cm=Cmat(w), QA=Qconf(qa, La, word_points(ga), w, A), QB=Qconf(qb, Lb, word_points(gb), w, A),
                da=mp.mpf(La) / qa, db=mp.mpf(Lb) / qb, A=A, n=len(w))

def obstruction_pre(r, pre, ret_c=False):
    r = mp.mpf(r)
    lam = (1 / r - pre['da']) / (pre['db'] - pre['da'])
    Q = (1 - lam) * pre['QA'] + lam * pre['QB']
    P = pre['Cm'] / pre['A'] ** 2 - r * Q
    n = pre['n']
    P11 = P[1:n, 1:n]; P10 = P[1:n, 0]
    sol = mp.lu_solve(P11, P10)
    val = 2 - 2 * r - P[0, 0] + (P10.T * sol)[0, 0]
    if ret_c: return val, lam, -sol, P11
    return val, lam
