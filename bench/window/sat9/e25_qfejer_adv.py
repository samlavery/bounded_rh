"""E25 (fresh pre-registration, lead 2026-10-09): adversarial test of the q*Fejer lobe minorant.
phi_d = q (1 - |al|/d)_+, d in the FIXED menu {1/4, 3/8, 1/2};  bound = max_d int phi_d |S_A|^2  (two-sided),
target = 4 g0 P + 4 sum_{p,p'} h(s_p - s_p'),  h = K - g.  The adversary minimises [bound - target] DIRECTLY over
positions and depths (smooth max over the menu during the search, exact max at the end), P = 5,6,8,12,16,24,32,
depths in [0.8, 20]; plus searches with k pairs pinned at Y in {5, 10, 20} (others free in [0.8, Y]).
Decision (pre-registered): min [bound - target] >= 0 for every P >= 5 -> adopt; any negative -> report it."""
import sys, json, numpy as np
from scipy.optimize import minimize
from common import *
MENU = (0.25, 0.375, 0.5)
m = al <= 0.5 + 1e-12; A = al[m]; Wq = W2[m]
WD = np.array([Wq * np.clip(1 - A / d, 0, None) for d in MENU])          # (3, nA)
# tables of K and g (for h = K - g) and derivatives
U = np.linspace(0.0, 48.0, 48001)
Ktab = np.empty_like(U)
for i in range(0, len(U), 4000):
    Ktab[i:i + 4000] = np.cos(2 * np.pi * np.outer(U[i:i + 4000], al)) @ W2
Gtab = g_of(U); Gtab[0] = g0; Htab = Ktab - Gtab; dHtab = np.gradient(Htab, U)
def htab(u):
    a = np.abs(u); return np.interp(a, U, Htab, right=0.0), np.interp(a, U, dHtab, right=0.0) * np.sign(u)
BETA = 4.0
def obj(z, P, pin):
    s = z[:P]; y = z[P:].copy()
    E = np.exp(2j * np.pi * np.outer(A, s)); ch = 2 * np.cosh(2 * np.pi * np.outer(A, y))
    F = (ch * E).sum(1); F2 = np.abs(F) ** 2
    LB = WD @ F2                                                            # (3,)
    d = s[:, None] - s[None, :]; hv, hd = htab(d)
    tgt = 4 * g0 * P + 4 * hv.sum()
    mx = LB.max(); wts = np.exp(BETA * (LB - mx)); sm = mx + np.log(wts.sum()) / BETA; wts /= wts.sum()
    Wc = wts @ WD                                                           # effective weight
    ia = 2j * np.pi * A[:, None]
    gs = Wc @ (2 * np.real(np.conj(F)[:, None] * ch * ia * E))
    dc = 4 * np.pi * A[:, None] * np.sinh(2 * np.pi * np.outer(A, y))
    gy = Wc @ (2 * np.real(np.conj(F)[:, None] * dc * E))
    gs = gs - 8 * hd.sum(1)
    if pin is not None: gy[pin] = 0.0
    return sm - tgt, np.concatenate([gs, gy])
def exact(s, y):
    P = len(s); E = np.exp(2j * np.pi * np.outer(A, s)); ch = 2 * np.cosh(2 * np.pi * np.outer(A, y))
    SA = (ch * E).sum(1); V = E.sum(1); SB = SA - 2 * V
    d = (s[:, None] - s[None, :]).ravel(); tgt = 4 * g0 * P + 4 * float((K_of(d) - g_of(d)).sum())
    parts = []
    for W in WD:
        parts.append((float(W @ (4 * np.abs(V) ** 2)), float(W @ (4 * np.real(np.conj(V) * SB))), float(W @ np.abs(SB) ** 2)))
    tots = [sum(p) for p in parts]; k = int(np.argmax(tots))
    return tots[k] - tgt, tgt, MENU[k], parts[k], tots
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 101)
def starts(P, n):
    out = []
    for t in range(n):
        kind = t % 4
        if kind == 0: s0 = np.sort(rng.uniform(0, rng.uniform(0.3, 1.2) * P, P))
        elif kind == 1: s0 = rng.uniform(0.5, 0.9) * np.arange(P) + rng.normal(0, 0.03, P)
        elif kind == 2:
            k = max(2, P // 3); sites = np.sort(rng.uniform(0, 0.8 * k, k)); s0 = np.sort(sites[rng.integers(0, k, P)] + rng.normal(0, 0.01, P))
        else: s0 = np.sort(np.concatenate([rng.uniform(0, 0.6 * P / 2, P // 2), rng.uniform(0.6 * P / 2 + 2, 0.6 * P + 2, P - P // 2)]))
        out.append(s0)
    return out
mode = sys.argv[1] if len(sys.argv) > 1 else 'free'
Ps = (5, 6, 8, 12, 16, 24, 32)
res = {}
for P in Ps:
    cases = []
    if mode == 'free':
        for s0 in starts(P, 24):
            y0 = np.where(rng.random(P) < 0.8, rng.uniform(0.8, 2.0, P), rng.uniform(0.8, 20.0, P)); cases.append((s0, y0, None, 20.0))
    else:
        for Y in (5.0, 10.0, 20.0):
            for kpin in sorted({1, 2, max(1, P // 4)}):
                for s0 in starts(P, 4):
                    y0 = rng.uniform(0.8, 2.0, P); pin = rng.choice(P, kpin, replace=False); y0[pin] = Y
                    cases.append((s0, y0, pin, Y))
    best = (np.inf, None)
    for s0, y0, pin, Y in cases:
        bnds = [(None, None)] * P + [((Y, Y) if (pin is not None and i in pin) else (0.8, Y)) for i in range(P)]
        try:
            r = minimize(obj, np.concatenate([s0, y0]), args=(P, pin), jac=True, method='L-BFGS-B', bounds=bnds, options={'maxiter': 3000})
        except FloatingPointError:
            continue
        val = exact(r.x[:P], r.x[P:])[0]
        if val < best[0]: best = (val, r.x.copy(), Y, None if pin is None else list(map(int, pin)))
    z = best[1]; s, y = z[:P], z[P:]; o = np.argsort(s)
    val, tgt, dsel, parts, tots = exact(s, y)
    res[P] = {'s': s[o].tolist(), 'y': y[o].tolist(), 'margin': val}
    print('[%s] P=%2d: min [bound - target] = %+9.3f (target %.2f; delta*=%.3f: (i) %.2f (ii) %+.2f (iii) %.2f; menu totals %s) %s'
          % (mode, P, val, tgt, dsel, parts[0], parts[1], parts[2], ['%.1f' % t for t in tots], 'PASS' if val >= 0 else 'FAIL'), flush=True)
    print('      s', np.round(s[o] - s[o][0], 3).tolist(), '\n      y', np.round(y[o], 3).tolist(), flush=True)
json.dump(res, open('e25_%s.json' % mode, 'w'))
