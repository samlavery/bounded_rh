"""Crowding regime, exploratory (NOT certified): P_h-free local objective in the line model, divided by y^2,
  F(D, y) = S0(y) + sum_b m_b psi_y(u_b) + [sum_b 4 m_b g(u_b) + sum_{a != b} m_a m_b g(u_a - u_b)] / y^2,
  S0 = 2 [K(2iy) - K(0)] / y^2,  psi_y(u) = 4 [Re K(u + iy) - K(u)] / y^2   (LP >= y^2 F since P_h >= 0).
Minimised over env points (positions free, masses 1/2) with one point PINNED at displacement delta from site n (crowding),
compared with the unpinned minimum.  usage: python3 crowd_explore.py"""
import sys, json, time, numpy as np
from fractions import Fraction
from scipy.optimize import minimize
from scipy.interpolate import CubicSpline
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
cj = json.load(open('cert_R8_backed.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); nb, Dk = 96, 1 / 32
def gfun(u):
    u = np.atleast_1d(np.asarray(u, float)); th = 2 * np.pi * Dk * u
    C = yk[0] + 2 * (np.cos(np.outer(th, np.arange(1, nb))) @ yk[1:]); return Dk * np.sinc(Dk * u) ** 2 * C
xg, wg = np.polynomial.legendre.leggauss(300); al = (xg + 1) / 2; wa = wg / 2; qa = qf(al)
def psi(u, y):
    u = np.atleast_1d(np.asarray(u, float)); B = (np.cosh(2 * np.pi * al * y) - 1) / y ** 2; out = np.empty(len(u))
    for i in range(0, len(u), 5000): out[i:i + 5000] = 8 * (np.cos(2 * np.pi * np.outer(u[i:i + 5000], al)) @ (qa * wa * B))
    return out
def S0(y): return float(4 * np.sum(qa * wa * (np.cosh(4 * np.pi * al * y) - 1)) / y ** 2)
UG = np.arange(0, 60.0001, 1 / 512); gS = CubicSpline(UG, gfun(UG)); X = 26
def make(y):
    pS = CubicSpline(UG[UG <= X + 1], psi(UG[UG <= X + 1], y)); s0 = S0(y); iy2 = 1 / y ** 2
    def F(u, m):
        a = np.abs(u); D = u[:, None] - u[None, :]; Da = np.abs(D); G = gS(Da); np.fill_diagonal(G, 0.0)
        val = s0 + m @ pS(a) + iy2 * (4 * m @ gS(a) + m @ G @ m)
        dG = gS(Da, 1) * np.sign(D); np.fill_diagonal(dG, 0.0)
        grad = m * pS(a, 1) * np.sign(u) + iy2 * (4 * m * gS(a, 1) * np.sign(u) + 2 * m * (dG @ m))
        return val, grad
    return F
rng = np.random.default_rng(3)
def starts(n_side, pin):
    out = []
    for kind in range(8):
        pos = np.concatenate([-np.arange(1, n_side + 1), np.arange(1, n_side + 1)]).astype(float)
        m = np.full(len(pos), 2.0)
        if kind in (1, 5): m[:] = 1.0
        if kind in (2, 6): m = rng.choice([1.0, 2.0], len(pos))
        if kind == 3: pos = pos * 1.026
        if kind == 4: pos = pos + rng.normal(0, 0.05, len(pos))
        if kind == 7: pos = pos * 0.97
        if pin is not None:
            n, d, mp = pin; k = np.argmin(np.abs(pos - n)); pos[k] = n + d; m[k] = mp
            if kind >= 5:  # vacate the pinned point's neighbours
                drop = np.abs(pos - (n + d)) < 1.2; drop[k] = False; pos, m = pos[~drop], m[~drop]
        out.append((pos, m))
    return out
def run(y, pin, n_side=X - 1):
    F = make(y); best = (np.inf, None, None)
    for pos, m in starts(n_side, pin):
        free = np.ones(len(pos), bool)
        if pin is not None: free[np.argmin(np.abs(pos - (pin[0] + pin[1])))] = False
        for it in range(3):
            def f(z):
                u = pos.copy(); u[free] = z; v, g = F(u, m); return v, g[free]
            r = minimize(f, pos[free], jac=True, method='L-BFGS-B', options={'maxiter': 3000})
            pos = pos.copy(); pos[free] = r.x
            # greedy mass flips (1 <-> 2) and removals that lower F
            v0 = F(pos, m)[0]; changed = False
            for i in np.argsort(np.abs(pos)):
                if not free[i] or abs(pos[i]) > 6: continue
                for newm in (1.0, 2.0, 0.0):
                    if newm == m[i]: continue
                    mm = m.copy(); mm[i] = newm; v = F(pos, mm)[0]
                    if v < v0 - 1e-9: m, v0, changed = mm, v, True
            keep = m > 0; pos, m, free = pos[keep], m[keep], free[keep]
            if not changed: break
        v = F(pos, m)[0]
        if v < best[0]: best = (v, pos.copy(), m.copy())
    return best
t0 = time.time()
for y in (0.05, 0.1, 0.2, 0.3, 0.4):
    v, pos, m = run(y, None); o = np.argsort(np.abs(pos))[:6]
    print('y=%.2f  UNPINNED min F = %+.4f  (S0 %.3f) near points %s' % (y, v, S0(y), ' '.join('%+.3f(m%d)' % (pos[i], m[i]) for i in sorted(o, key=lambda i: pos[i]))), flush=True)
    worst = (np.inf,)
    for n in (1, 2):
        for d in (-0.5, -0.35, -0.25, -0.15, 0.15, 0.25, 0.35):
            if n == 2 and d == -0.5: continue
            for mp in (1.0, 2.0):
                v, pos, m = run(y, (n, d, mp))
                if v < worst[0]: worst = (v, n, d, mp, pos, m)
    v, n, d, mp, pos, m = worst; o = np.argsort(np.abs(pos))[:7]
    print('        PINNED (crowding, delta >= 0.15, cells 1-2) min F = %+.4f at n=%d delta=%+.2f m=%d; near points %s  [%.0fs]' % (v, n, d, mp, ' '.join('%+.3f(m%d)' % (pos[i], m[i]) for i in sorted(o, key=lambda i: pos[i])), time.time() - t0), flush=True)
