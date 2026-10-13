"""Lemma P test: E(Z) >= F_C(D(Z)) for every configuration Z, D(Z) = Z with each off-line pair s +- iy replaced by an
on-line double at s, C the dip certificate (exact LP, A = 3).
Periodic model (period N, total multiplicity N).  Two-sided energy E(Z) = (1/N) sum_j q(j/N) |S_j|^2 = N q(0) + 2 d(Z)/N,
d(Z) = sum_{0<j<N} q(j/N)|S_j|^2,  S_j = sum_on m e(j x/N) + sum_pairs 2 cosh(2 pi j y/N) e(j s/N).
The certificate on a real configuration D:  E(D) >= F_C(D) = h^(0) N + g_N(0) sum m^2,  g_N(0) = sum_n g(nN) >= g(0),
h^(0) = q(0) - g^(0).  F_C is COUNT-ONLY, so with one-sided units
    W(Z) := [E(Z) - F_C(D(Z))]/2 = d(Z)/N - N (g_N(0) - g^(0))/2 - g_N(0) (#doubles + #pairs),
and Lemma P <=> W >= 0 for all Z; per-defect units: W / (g(0) (#doubles + #pairs))  (g(0) = 2 delta').
Also reported: the split W = s(D(Z)) + Delta_B/2 (s = certificate slack of D(Z), Delta_B = E(Z) - E(D(Z))).
usage: python3 lemmaP.py WINDOW(R8|joint) N"""
import sys, json, time, math, numpy as np
from scipy.optimize import minimize
WIN, N = sys.argv[1], int(sys.argv[2]); t0 = time.time()
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
if WIN == 'R8b':
    c = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24)
    qfun = make_qf(c); cj = json.load(open('cert_R8_backed.json')); from fractions import Fraction
    yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); A, Dk = 3.0, 1 / 32; EINF = 0.159784
elif WIN == 'R8':
    c = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24)
    qfun = make_qf(c); sol = json.load(open('global_cert3_R8.json'))['sols']['3,0.03125']; yk = np.array(sol[1]); A, Dk = 3.0, 1 / 32
    EINF = 0.159784
else:
    jj = json.load(open('global_joint_A3_K.json')); A, Dk = jj['A'], jj['Dk']; yk = np.array(jj['g_knots']); qk = np.array(jj['q_knots'])
    qfun = lambda a: np.interp(np.abs(np.asarray(a, float)), np.arange(len(qk) + 1) * Dk, np.concatenate([qk, [0.0]]))
    EINF = jj['einf']
nb = len(yk); g0 = Dk * (yk[0] + 2 * yk[1:].sum()); gh0 = yk[0]
D2 = np.zeros((nb + 1, nb))
for b in range(nb + 1):
    for (o, w) in ((b - 1, 1), (b, -2), (b + 1, 1)):
        if 0 <= abs(o) < nb: D2[b, abs(o)] += w / Dk
D2[0] = 0; D2[0, 0] = -2 / Dk; D2[0, 1] = 2 / Dk
Jk = D2 @ yk
def g_of(u):
    u = np.asarray(u, float)[:, None]; cs = np.cos(2 * np.pi * np.arange(nb + 1)[None, :] * Dk * u); cs[:, 1:] *= 2
    return -(cs @ Jk) / (4 * np.pi ** 2 * u[:, 0] ** 2)
gN0 = g0 + 2 * float(np.sum(g_of(np.arange(1, 200001) * N)))
J = np.arange(1, N); qv = qfun(J / N); kappa_cert = 1 - (EINF + max(0.0, gh0 - g0) / 2) / (g0 / 2)
print('window %s, N=%d: certificate g(0) = 2 delta\' = %.6f, g^(0) = %.6f, g_N(0) = %.6f, kappa_cert %.6f; budget for Lemma P\' (per defect, units of 2 delta\'): %.3f%%'
      % (WIN, N, g0, gh0, gN0, kappa_cert, 100 * (1 - (1 - kappa_cert) / (1 - 0.6735) * 0 - 0) if False else 100 * (1 - (EINF / (1 - 0.6735)) / (g0 / 2))), flush=True)
rng = np.random.default_rng(17)

def d_and_grad(z, n1, k, P, yfix):
    """z = (on-line positions: n1 simples then k doubles, pair centres P, [pair depths P if yfix is None])"""
    n = n1 + k; x = z[:n]; s = z[n:n + P]; y = yfix if yfix is not None else z[n + P:]
    m = np.concatenate([np.ones(n1), np.full(k, 2.0)])
    Ex = np.exp(2j * np.pi * np.outer(J, x) / N); Es = np.exp(2j * np.pi * np.outer(J, s) / N)
    ch = 2 * np.cosh(2 * np.pi * np.outer(J, y) / N)
    S = Ex @ m + (Es * ch).sum(1); d = float(qv @ np.abs(S) ** 2)
    W = (qv * np.conj(S))[:, None]
    gx = 2 * np.real(W * Ex * m[None, :] * (2j * np.pi * J[:, None] / N)).sum(0)
    gs = 2 * np.real(W * Es * ch * (2j * np.pi * J[:, None] / N)).sum(0)
    out = [gx, gs]
    if yfix is None: out.append(2 * np.real(W * Es * 2 * np.sinh(2 * np.pi * np.outer(J, y) / N) * (2 * np.pi * J[:, None] / N)).sum(0))
    return d, np.concatenate(out)

def d_real(xr, mr):
    S = np.exp(2j * np.pi * np.outer(J, xr) / N) @ mr; return float(qv @ np.abs(S) ** 2)

def inits(n1, k, P, s):
    """structured starts: lattice with defects (double on a site + vacancy at dv) and pairs (on a site, or at a
    half-integer offset, which puts the high-alpha field negative), clustered pairs, random"""
    n = n1 + k; kind = s % 5
    if kind in (0, 1, 2):
        sites = np.arange(N, dtype=float); nd = k + P
        cen = (np.round(np.linspace(0, N, nd, endpoint=False)) if kind != 2 else (np.arange(nd) * (2 + s % 3))) % N
        cen = cen.astype(int); vac = (cen - (2 if kind == 0 else 1)) % N
        used = set(cen.tolist()) | set(vac.tolist())
        if len(used) == 2 * nd:
            rest = np.array([t for t in range(N) if t not in used], float)
            x = np.concatenate([rest, cen[:k].astype(float)]); sc = cen[k:].astype(float) + (0.5 if (kind == 1 and s % 2) else 0.0)
            return np.concatenate([x + rng.normal(0, 0.02, n), sc])
    return np.concatenate([np.sort(rng.uniform(0, N, n)), rng.uniform(0, N, P)])

def search(k, P, yfix, starts):
    n1 = N - 2 * k - 2 * P; best = (np.inf, None)
    for s in range(starts):
        z0 = inits(n1, k, P, s)
        if yfix is None:
            z0 = np.concatenate([z0, rng.uniform(0, 3, P) if s % 2 else np.full(P, 0.05)])
            bnds = [(None, None)] * (n1 + k + P) + [(0, 3)] * P
        else:
            bnds = None
        r = minimize(lambda z: d_and_grad(z, n1, k, P, None if yfix is None else np.full(P, yfix)), z0, jac=True, method='L-BFGS-B', bounds=bnds, options={'maxiter': 4000})
        if r.fun < best[0]: best = (float(r.fun), r.x.copy())
    d, z = best; n = n1 + k
    W = d / N - N * (gN0 - gh0) / 2 - gN0 * (k + P)
    xr = np.concatenate([z[:n], z[n:n + P]]); mr = np.concatenate([np.ones(n1), np.full(k + P, 2.0)])
    dD = d_real(xr, mr); slack = dD / N - N * (gN0 - gh0) / 2 - gN0 * (k + P); dB = (d - dD) / N
    ys = (z[n + P:] if yfix is None else np.full(P, yfix))
    return W / (g0 * (k + P)), slack / (g0 * (k + P)), dB / (g0 * (k + P)), ys, z

if __name__ == '__main__':
    worst = (np.inf,)
    print('(1) free depths in [0, 3]: min over positions and depths of W per defect (units of 2 delta\')', flush=True)
    for P in (1, 2, 3):
        for k in ((0, 1) if WIN != 'R8b' else (0, 1, 3, 5)):
            w, sl, db, ys, z = search(k, P, None, 30)
            print('  P=%d pairs, k=%d on-line doubles: W/defect %+.5f (slack %+.5f, Delta_B/2 %+.5f), depths at optimum %s' % (P, k, w, sl, db, np.round(ys, 4)), flush=True)
            worst = min(worst, (w, 'free', P, k, tuple(np.round(ys, 4))))
    print('(2) fixed depth profile: min W per defect, and its split', flush=True)
    for y in (0.01, 0.03, 0.05, 0.1, 0.2, 0.3, 0.5, 1.0, 2.0, 3.0):
        row = []
        for P in (1, 2, 3):
            w, sl, db, ys, z = search(0, P, y, 20)
            row.append('P=%d: %+.4f (slack %+.4f, dB/2 %+.4f)' % (P, w, sl, db)); worst = min(worst, (w, 'fixed', P, 0, y))
        print('  y=%.2f: %s' % (y, ' | '.join(row)), flush=True)
    print('(3) Delta_B-seeking: minimise Delta_B alone at fixed depth (pair centre + environment), report the slack that pays for it', flush=True)
    for y in (0.05, 0.1, 0.2, 0.5):
        n1 = N - 2; best = (np.inf, None)
        for s in range(20):
            z0 = inits(n1, 0, 1, s)
            def fB(z):
                d, g = d_and_grad(z, n1, 0, 1, np.array([y]))
                xr = np.concatenate([z[:n1], z[n1:n1 + 1]]); mr = np.concatenate([np.ones(n1), [2.0]])
                Er = np.exp(2j * np.pi * np.outer(J, xr) / N); S = Er @ mr; dD = float(qv @ np.abs(S) ** 2)
                Wq = (qv * np.conj(S))[:, None]; gD = 2 * np.real(Wq * Er * mr[None, :] * (2j * np.pi * J[:, None] / N)).sum(0)
                return d - dD, g - gD
            r = minimize(fB, z0, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
            if r.fun < best[0]: best = (r.fun, r.x.copy())
        dBv, z = best; xr = np.concatenate([z[:n1], z[n1:n1 + 1]]); mr = np.concatenate([np.ones(n1), [2.0]])
        dD = d_real(xr, mr); slack = dD / N - N * (gN0 - gh0) / 2 - gN0
        print('  y=%.2f: most negative Delta_B/2 found %+.4f (units 2 delta\': %+.4f); slack of that D(Z) %+.4f -> W %+.4f' % (y, dBv / N, dBv / N / g0, slack / g0, (slack + dBv / N) / g0), flush=True)
    print('WORST W per defect over (1)+(2): %+.5f at %s  (%.0fs)' % (worst[0], worst[1:], time.time() - t0), flush=True)
