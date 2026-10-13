"""E41c: (b) at P = 512 (fixed lattice a = 0.99, N = 2048): saddle-free damped Newton (eigendecomposition of the exact dense
Hessian, |lambda| with floor mu, backtracking line search, depth-box guard), from the best available start (e41b2's endpoint
if present, else e40's).  Stop at ||grad|| <= 1e-6 * ||grad_start|| or 400 iterations; report LP, ||grad||, min eigenvalue."""
import sys, json, time, numpy as np
exec(open('e38_fullLP.py').read().split("if __name__ == '__main__':")[0])
A = 0.99; P = int(sys.argv[1]) if len(sys.argv) > 1 else 512; N = 4 * P; M = Model(N, P); n = M.n_on
saved = json.load(open('e40b_results.json')); z = np.array(saved[str(P)]['z']); sfix = z[n:n + P]
kap = 2 * np.pi * M.J.astype(float) / N; w = (2 / N) * M.q; Es = np.exp(1j * np.outer(kap, sfix))
def fgh(v, need_h=True):
    if (0.8 + v[n:] ** 2).max() > 3.0: return np.inf, None, None
    x = v[:n]; u = v[n:]; y = 0.8 + u ** 2
    Ex = np.exp(1j * np.outer(kap, x)); ch = 2 * np.cosh(np.outer(kap, y)); sh = 2 * np.sinh(np.outer(kap, y))
    S = Ex.sum(1) + (ch * Es).sum(1); f = float(w @ np.abs(S) ** 2) - M.const
    if not need_h: return f, None, None
    dx = 1j * kap[:, None] * Ex; dy = kap[:, None] * sh * Es; du = dy * (2 * u)[None, :]
    J = np.concatenate([dx, du], 1)
    d2 = np.concatenate([-(kap ** 2)[:, None] * Ex, (kap[:, None] ** 2 * ch * Es) * (2 * u)[None, :] ** 2 + dy * 2.0], 1)
    g = 2 * np.real(np.conj(J).T @ (w * S))
    H = 2 * np.real(np.conj(J).T @ (w[:, None] * J)) + np.diag(2 * np.real((np.conj(S) * w) @ d2))
    return f, g, H
v = np.concatenate([z[:n], np.sqrt(np.maximum(z[n + P:] - 0.8, 0)) + 1e-6])
f, g, H = fgh(v); g_start = np.linalg.norm(g); t0 = time.time()
for it in range(400):
    lam, V = np.linalg.eigh(H); gn = np.linalg.norm(g)
    if gn <= 1e-6 * g_start: break
    mu = max(1e-8 * np.abs(lam).max(), 1e-6)
    step = -V @ ((V.T @ g) / np.maximum(np.abs(lam), mu))
    tstep = 1.0; ok = False
    while tstep > 1e-12:
        f2, _, _ = fgh(v + tstep * step, need_h=False)
        if f2 < f - 1e-4 * tstep * abs(g @ step): ok = True; break
        tstep *= 0.5
    if not ok:
        # gradient step fallback
        step = -g / max(np.abs(lam).max(), 1.0); tstep = 1.0
        while tstep > 1e-12:
            f2, _, _ = fgh(v + tstep * step, need_h=False)
            if f2 < f: ok = True; break
            tstep *= 0.5
        if not ok: break
    v = v + tstep * step; f, g, H = fgh(v)
    if it % 20 == 0: print('  it %3d: LP %+.6f ||grad|| %.3e min eig %+.3e step %.2e' % (it, f, np.linalg.norm(g), lam[0], tstep), flush=True)
lam = np.linalg.eigvalsh(H); gn = np.linalg.norm(g)
zz = np.concatenate([v[:n], sfix, 0.8 + v[n:] ** 2]); check = Model(N, P).LP(zz, False)
print('(b) P=%d N=%d saddle-free Newton: LP %+.6f (fresh check %+.6f) | ||grad|| %.3e (ratio %.2e) | min Hess eig %+.3e | its %d | depths max %.3f | %.0fs'
      % (P, N, f, check, gn, gn / g_start, lam[0], it, (0.8 + v[n:] ** 2).max(), time.time() - t0), flush=True)
json.dump({'LP': f, 'grad': gn, 'ratio': gn / g_start, 'mineig': float(lam[0]), 'z': zz.tolist()}, open('e41c_P%d.json' % P, 'w'))
