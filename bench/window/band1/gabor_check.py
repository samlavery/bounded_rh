"""Is the joint window a single Gabor family?  Needs q = f*f (autocorrelation) with f >= 0 on [-1/2, 1/2] (f = phi^2, phi
admissible).  Fit: f even, nonnegative, on 2M cells; minimise sum_k (h sum_i f_i f_{i+k} - q(k h))^2 over k = 1..2M-1
(alpha in (0,1); q(0) is a free LP knot so it is fitted separately).  Control: R8 (f = vAM/A, realisable by construction)."""
import sys, json, numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
M = 128; h = 1.0 / (2 * M); s = -0.5 + (np.arange(2 * M) + 0.5) * h; ks = np.arange(1, 2 * M)
def fit(qtarget, label, w0):
    tq = qtarget(ks * h)
    def obj(v):
        f = np.concatenate([v[::-1], v]); ac = np.array([h * f[:-k] @ f[k:] for k in ks]); r = ac - tq
        g = np.zeros(2 * M)
        for idx, k in enumerate(ks):
            g[:-k] += 2 * r[idx] * h * f[k:]; g[k:] += 2 * r[idx] * h * f[:-k]
        gv = g[M:] + g[:M][::-1]
        return float(r @ r), gv
    best = None
    for v0 in w0:
        r = minimize(obj, v0, jac=True, method='L-BFGS-B', bounds=[(0, None)] * M, options={'maxiter': 20000, 'ftol': 1e-16, 'gtol': 1e-12})
        if best is None or r.fun < best.fun: best = r
    f = np.concatenate([best.x[::-1], best.x]); ac = np.array([h * f[:-k] @ f[k:] for k in ks])
    rel = np.max(np.abs(ac - tq)) / tq.max()
    print('%s: best fit with f >= 0: max |f*f - q| / max q = %.2e (rms %.2e); implied q(0) = int f^2 = %.4f; min f %.3f, f(+-1/2) %.3f'
          % (label, rel, np.sqrt(best.fun / len(ks)) / tq.max(), h * f @ f, f.min(), f[0]), flush=True)
    return rel
c8 = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24)
q8 = make_qf(c8); flat = np.full(M, 1.0)
fit(lambda a: q8(np.minimum(a, 0.99999)), 'R8 control', [flat, np.sqrt(np.maximum(1e-3, 1 - 2 * s[M:]))])
jj = json.load(open('global_joint_A3_K.json')); qk = np.array(jj['q_knots']); Dk = jj['Dk']
qj = lambda a: np.interp(np.abs(a), np.arange(len(qk) + 1) * Dk, np.concatenate([qk, [0.0]]))
fit(qj, 'joint window', [flat, flat * 1.1, np.linspace(1.2, 0.8, M)])
print('joint window knots q(a)/q(1/32) at a = 1/32, 1/8, 1/4, 1/2, 3/4, 7/8, 31/32:', ' '.join('%.4f' % (qj(np.array([a]))[0] / qj(np.array([1 / 32]))[0]) for a in (1 / 32, 1 / 8, 1 / 4, 1 / 2, 3 / 4, 7 / 8, 31 / 32)))
