"""The Lean object of AMW/DefectEnergy.lean, sampled numerically in normalised units (lambda = 1, taper ramp -> 0):
  rows v_rho(k) = Psi(x_rho - k), k = 0..W-1 (the Gabor grid tau_k = T + k h, h = 2 pi / L, over (T, 2T]),
  Psi = Fourier transform of psi = sqrt(f) on [-1/2, 1/2], f = the window profile with int f = 1 (vAM / A for R8),
  A = sum_rho m_rho v_rho v_rho^T (hat units), frobSq = ||A||_F^2 = m^T (G o G) m, G = V V^T,
  E_T = (frobSq / N - qf(0)) / 2, N = number of zeros with x in (0, W] (zeros in the margins, D0 = sqrt T, still enter A).
Psi is evaluated from the cosine series of psi (period-1 continuation is continuous): Psi(y) = sum_j beta_j (sinc(y-j) +
sinc(y+j)) / 2, tabulated on a fine grid with a cubic spline.
Tests: (a) bulk aliasing |G - F(x - x')|; (b) all-simple lattice N E_T vs W; (c) one relaxed lattice dipole: N E_T(defect)
- N E_T(lattice) vs Delta_1/N of the periodic model; (d) k far-apart dipoles; (e) the all-simple lower side: min N E_T over
all-simple configurations, positions free.  usage: python3 sampled.py WINDOW(R8|json) """
import sys, json, math, time, numpy as np
from scipy.interpolate import CubicSpline
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
WIN = sys.argv[1] if len(sys.argv) > 1 else 'R8'
c = (window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24) if WIN == 'R8'
     else np.array(json.load(open(WIN))['c']))
S2 = math.sqrt(2.0); A0 = 2 * math.sin(S2 / 2) / S2
fprof = lambda s: (np.cos(S2 * s) + sum(cj * np.cos(2 * np.pi * (j + 1) * s) for j, cj in enumerate(c))) / A0
qf = make_qf(c); q0 = float(qf(np.array([0.0]))[0])
# cosine coefficients of psi = sqrt f on [-1/2, 1/2]
gs, gw = np.polynomial.legendre.leggauss(4000); gs = gs / 2; gw = gw / 2
psi = np.sqrt(fprof(gs)); JM = 600; jj = np.arange(JM + 1)
beta = np.array([np.sum(gw * psi * np.cos(2 * np.pi * j * gs)) for j in jj]); beta[1:] *= 2
def Psi_exact(y):
    y = np.asarray(y, float)[..., None]
    return (beta * 0.5 * (np.sinc(y - jj) + np.sinc(y + jj))).sum(-1)
YMAX = 1400.0; yt = np.arange(0, YMAX + 0.002, 0.002)
tab = np.concatenate([Psi_exact(yt[i:i + 20000]) for i in range(0, len(yt), 20000)])
spl = CubicSpline(yt, tab); dspl = spl.derivative()
Psi = lambda y: spl(np.abs(y)); dPsi = lambda y: np.sign(y) * dspl(np.abs(y))
Ff = lambda u: np.sum(gw[None, :] * fprof(gs)[None, :] * np.cos(2 * np.pi * np.asarray(u, float)[:, None] * gs[None, :]), axis=1)

def frob(x, m, W, grad=False):
    k = np.arange(W); Y = x[:, None] - k[None, :]; V = Psi(Y); G = V @ V.T; mG = m[:, None] * m[None, :]
    fs = float(np.sum(mG * G * G))
    if not grad: return fs
    H = dPsi(Y) @ V.T
    return fs, 4 * m * np.sum(m[None, :] * G * H, axis=1)

def ET(x, m, W):
    inside = (x > 0) & (x <= W); N = float(np.sum(m[inside]))
    return (frob(x, m, W) / N - q0) / 2, N

def lattice(W, D):
    return np.arange(-D, W + D) + 0.5, np.ones(W + 2 * D)

if __name__ == '__main__':
    t0 = time.time()
    print('window %s: qf(0) %.6f, Psi(0)^2 sum check (bulk Sum_k Psi(x-k)^2 = F(0) = 1): %.8f' % (WIN, q0, float(np.sum(Psi(0.3 - np.arange(-600, 600)) ** 2))), flush=True)
    # (a) bulk aliasing
    W = 200; x = np.array([90.3, 95.0, 100.7, 103.2, 110.1]); V = Psi(x[:, None] - np.arange(W)[None, :]); G = V @ V.T
    Fx = Ff((x[:, None] - x[None, :]).ravel()).reshape(G.shape)
    print('(a) bulk Gabor sum vs F(x - x\'): max |G - F| = %.2e (truncation of k to [0, W) included)' % np.abs(G - Fx).max(), flush=True)
    # (b) lattice
    for D in (0, 100):
        out = []
        for W in (50, 100, 200, 400):
            xl, ml = lattice(W, D); e, N = ET(xl, ml, W); out.append('W=%d: N E_T %+.4f' % (W, N * e))
        print('(b) all-simple lattice, margin %d: %s' % (D, ' | '.join(out)), flush=True)
    # (c) one relaxed lattice dipole in the middle, margin 100
    for W in (100, 200):
        D = 100; xl, ml = lattice(W, D); e_lat, N = ET(xl, ml, W)
        ci = D + W // 2; xd = np.delete(xl, ci - 2); md = np.delete(ml, ci - 2); idx = ci - 1; md[idx] = 2.0   # vacancy two sites below the double
        free = np.where(np.abs(xd - xd[idx]) <= 25)[0]
        def fobj(z):
            xx = xd.copy(); xx[free] = z; fs, g = frob(xx, md, W, grad=True); return fs, g[free]
        f_un = frob(xd, md, W); r = minimize(fobj, xd[free], jac=True, method='L-BFGS-B', options={'maxiter': 2000})
        xr = xd.copy(); xr[free] = r.x; e_def, N2 = ET(xr, md, W)
        print('(c) W=%d: one dipole: N E_T(defect) - N E_T(lattice) = %.6f relaxed (unrelaxed %.6f); N unchanged %s; per-defect 2 delta from the periodic model: R8 0.990774 / best 0.968893'
              % (W, N2 * e_def - N * e_lat, (f_un - frob(xl, ml, W)) / N / 2 * 1, N2 == N), flush=True)
    # (d) k dipoles far apart, W = 400, margin 100, relaxed jointly near each
    W = 400; D = 100; xl, ml = lattice(W, D); e_lat, N = ET(xl, ml, W)
    for kdef in (2, 4):
        centres = [D + int(W * (i + 0.5) / kdef) for i in range(kdef)]
        xd, md = xl.copy(), ml.copy(); rm = [cc - 2 for cc in centres]
        for cc in centres: md[cc] = 2.0
        keep = np.setdiff1d(np.arange(len(xd)), rm); xd, md = xd[keep], md[keep]
        dbl = np.where(md == 2)[0]; free = np.where(np.min(np.abs(xd[:, None] - xd[dbl][None, :]), axis=1) <= 20)[0]
        def fobj(z):
            xx = xd.copy(); xx[free] = z; fs, g = frob(xx, md, W, grad=True); return fs, g[free]
        r = minimize(fobj, xd[free], jac=True, method='L-BFGS-B', options={'maxiter': 3000}); xr = xd.copy(); xr[free] = r.x
        e_def, N2 = ET(xr, md, W)
        print('(d) W=%d: %d far-apart dipoles: (N E_T(defect) - N E_T(lattice)) / k = %.6f' % (W, kdef, (N2 * e_def - N * e_lat) / kdef), flush=True)
    # (e) all-simple lower side: N points in [0, W] (no margin: margin zeros only add to frobSq), minimise frobSq
    for W in (50, 100, 200, 400):
        best = np.inf; rng = np.random.default_rng(1)
        starts = [np.arange(W) + 0.5] + [np.sort(rng.uniform(0, W, W)) for _ in range(3)] + [np.arange(W) * (W - 1.0) / W + 0.5]
        for x0 in starts:
            mm = np.ones(W)
            r = minimize(lambda z: frob(z, mm, W, grad=True), x0, jac=True, method='L-BFGS-B', bounds=[(1e-9, W)] * W, options={'maxiter': 3000})
            best = min(best, r.fun)
        lat = frob(np.arange(W) + 0.5, np.ones(W), W)
        print('(e) all-simple lower side, no margin, W=%d: min N E_T = %+.4f (lattice %+.4f)  (%.0fs)' % (W, (best / W - q0) / 2 * W, (lat / W - q0) / 2 * W, time.time() - t0), flush=True)
    # (e') realistic margins: lattice zeros fixed in 100-wide margins, the N = W counted zeros free in (0, W]
    for W in (50, 100, 200):
        D = 100; xm = np.concatenate([np.arange(-D, 0) + 0.5, np.arange(W, W + D) + 0.5]); best = np.inf; rng = np.random.default_rng(2)
        for x0 in [np.arange(W) + 0.5] + [np.sort(rng.uniform(0, W, W)) for _ in range(2)]:
            mm = np.ones(W + 2 * D)
            def fo(z):
                fs, g = frob(np.concatenate([xm, z]), mm, W, grad=True); return fs, g[2 * D:]
            r = minimize(fo, x0, jac=True, method='L-BFGS-B', bounds=[(1e-9, W)] * W, options={'maxiter': 3000}); best = min(best, r.fun)
        lat = frob(np.concatenate([xm, np.arange(W) + 0.5]), np.ones(W + 2 * D), W)
        print("(e') all-simple lower side, lattice margins 100, W=%d: min N E_T = %+.4f (lattice %+.4f)  (%.0fs)" % (W, (best / W - q0) / 2 * W, (lat / W - q0) / 2 * W, time.time() - t0), flush=True)
