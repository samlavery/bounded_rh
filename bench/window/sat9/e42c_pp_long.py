"""E42c: pair-pair profile minimum of Q_pp (statement E) at a given (a, P), LONG run: start from the P/2 profile file if given
(end layers of 100 sites + flat interior at its mid value) else arched; L-BFGS 20000 then saddle-free Newton up to 3000
iterations (exact Hessian), stop at rel grad 1e-8 with PD Hessian.  Saves the profile (e42c_pp_a<a>_P<P>.json)."""
import sys, json, time, numpy as np
from scipy.optimize import minimize
exec(open('e42_separate.py').read().split("if part == 'env':")[0].split('part = sys.argv[1]')[0] + open('e42_separate.py').read().split('part = sys.argv[1]')[1].split("if part == 'env':")[0])
from common import al, W2
A = float(sys.argv[1]); P = int(sys.argv[2]); src = sys.argv[3] if len(sys.argv) > 3 else None
s = A * np.arange(P); E = np.exp(2j * np.pi * np.outer(al, s)); G2 = float(W2 @ (4 * np.abs(E.sum(1)) ** 2)); k2 = (2 * np.pi * al) ** 2
def fgh(v, need=True):
    if (0.8 + v ** 2).max() > 3.0: return np.inf, None, None
    y = 0.8 + v ** 2; ch = 2 * np.cosh(2 * np.pi * np.outer(al, y)); sh = 2 * np.sinh(2 * np.pi * np.outer(al, y))
    S = (ch * E).sum(1); f = float(W2 @ np.abs(S) ** 2) - G2
    if not need: return f, None, None
    dy = (2 * np.pi * al)[:, None] * sh * E; J = dy * (2 * v)[None, :]
    d2 = (k2[:, None] * ch * E) * (2 * v)[None, :] ** 2 + dy * 2.0
    g = 2 * np.real(np.conj(J).T @ (W2 * S))
    H = 2 * np.real(np.conj(J).T @ (W2[:, None] * J)) + np.diag(2 * np.real((np.conj(S) * W2) @ d2))
    return f, g, H
if src:
    yp = np.array(json.load(open(src))['y']); L = 100; y0 = np.full(P, yp[len(yp) // 2]); y0[:L] = yp[:L]; y0[-L:] = yp[-L:]
else:
    y0 = 0.8 + 0.7 * np.sin(np.pi * np.arange(P) / (P - 1)) ** 0.8
t0 = time.time()
r = minimize(lambda v: fgh(v)[:2] if np.isfinite(fgh(v, False)[0]) else (1e30, np.zeros_like(v)), np.sqrt(np.maximum(y0 - 0.8, 0)) + 1e-6,
             jac=True, method='L-BFGS-B', options={'maxiter': 20000})
print('  L-BFGS: Q_pp %.6f' % r.fun, flush=True)
v, f, gn, g0n, lam, it = sfn(fgh, r.x, 1e-8, 3000, log=True, every=250)
y = 0.8 + v ** 2
print('(E) a=%.2f P=%4d: Q_pp %+.6f | ||grad|| %.2e (rel %.1e) | mineig %+.3e (%s) | its %d | depths ends %.3f mid %.3f max %.3f | %.0fs'
      % (A, P, f, gn, gn / g0n, lam, 'PD' if lam > 0 else 'NOT PD', it, y[0], y[P // 2], y.max(), time.time() - t0), flush=True)
json.dump({'a': A, 'P': P, 'Q_pp': f, 'grad': gn, 'mineig': lam, 'y': y.tolist()}, open('e42c_pp_a%.2f_P%d.json' % (A, P), 'w'))
