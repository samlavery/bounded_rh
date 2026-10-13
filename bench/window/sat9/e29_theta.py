"""E29 (fresh pre-registration, lead 2026-10-09; LAST relaxation round in this family).  Everything below is fixed BEFORE any run.

BOUND.  q = qT + q(1-T), T = (1-|al|/d)_+, d in {1/4, 3/8, 1/2} (max over the menu = max of valid bounds).
  Lobe: int qT (|S_A|^2 - 4|V|^2) = (ii)_T + (iii)_T, exact, all pairs.
  High band, pointwise in al, with an EXPLICIT depth-class rule:
    Classes (greedy, by depth, width DELTA0 = 0.25): K_1 = {y <= y_min + DELTA0}; K_2 = {y_min^(2) <= y <= y_min^(2) + DELTA0}
    where y_min^(2) is the least depth not in K_1; and so on.  Deeper pairs are thereby kept out of the core's S'.
    Class i: V^i = sum_{p in K_i} e_p, S^i = sum c_p e_p, reference c_i = c(al, min depth of K_i), S'^i = S^i - c_i V^i
    (coefficients c_p - c_i >= 0, at most c_i (e^{2 pi al DELTA0} - 1)).
    Within class (theta-split; theta from {1, 1/2, 1/4}, the best one at each al, i.e. max of valid bounds):
       |S^i|^2 - 4|V^i|^2 >= J_i := (1-theta)(c_i^2-4)|V^i|^2 - (c_i^2/(theta (c_i^2-4)) - 1)|S'^i|^2.
    Between classes (PRIMARY, explicit): Re(conj(S^i) S^j - 4 conj(V^i) V^j) >= -(|S^i||S^j| + 4|V^i||V^j|).
  L = T_g^pp + max_d [ (ii)_T + (iii)_T + int q(1-T) ( sum_i J_i - 2 sum_{i<j} (|S^i||S^j| + 4|V^i||V^j|) ) ].
  DIAGNOSTIC (secondary, declared now): the same with the between-class terms kept EXACT; it upper-bounds what any
  between-class estimate can give, so it says whether the within-class theta-split is the binding loss.
SEARCH.  Adversary minimises L (primary) directly; P = 5, 6, 8, 12, 16, 24, 32; depths in [0.8, 20]; seeds: e25 and e28/e28-diag
  minimisers, hole configurations (min gap 1-1.25, flat and arched), e9, arches (e23), pinned-deep starts (Y = 5, 10, 20, then
  released), random.  e24b gap configurations (P = 26) evaluated and searched separately.  A second search minimises the
  diagnostic.  PASS = min L >= 0 for every P >= 5.
PREDICTION (bridge-port, before the run): PRIMARY FAILS for P >= 5.  Reason: for two depth classes with c_i != c_j the
  pointwise form |c_i V^i + c_j V^j + S'|^2 - 4|V^i + V^j|^2 is indefinite in (V^i, V^j) (determinant -4(c_i - c_j)^2), so any
  pointwise between-class estimate gives up the cancellation structure; the adversary will find a two-class configuration where
  -2(|S^i||S^j| + 4|V^i||V^j|) exceeds the retained class energies.  DIAGNOSTIC (exact between-class) PASSES for P >= 5:
  the within-class theta-split loses at most 1/4 of each class's (c^2-4)|V|^2 plus the bounded S' penalty, and the e28
  failures were driven by discarding all of it."""
import sys, json, numpy as np
from scipy.optimize import minimize
from common import *
DELTA0 = 0.25; THETAS = (1.0, 0.5, 0.25); MENU = (0.25, 0.375, 0.5)
TT = np.array([np.clip(1 - al / d, 0, None) for d in MENU]); WL = W2[None, :] * TT; WH = W2[None, :] * (1 - TT); WH[:, 0] = 0.0
U = np.linspace(0.0, 64.0, 128001); GT = g_of(U); GT[0] = g0; dGT = np.gradient(GT, U)
def gtab(u):
    a = np.abs(u); return np.interp(a, U, GT, right=0.0), np.interp(a, U, dGT, right=0.0) * np.sign(u)
BETA = 4.0; ia = (2j * np.pi * al)[:, None]; EPS = 1e-30
def classes(y):
    order = np.argsort(y); cls = []; i = 0
    while i < len(order):
        y0 = y[order[i]]; grp = [order[i]]; i += 1
        while i < len(order) and y[order[i]] <= y0 + DELTA0 + 1e-12: grp.append(order[i]); i += 1
        cls.append(np.array(grp))
    return cls
def Lval(z, P, mode='primary', grad=True):
    s, y = z[:P], z[P:]
    E = np.exp(2j * np.pi * np.outer(al, s)); C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); D = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    SA = (C * E).sum(1); V = E.sum(1)
    lobe = np.abs(SA) ** 2 - 4 * np.abs(V) ** 2
    gs = np.zeros((len(MENU), P)); gy = np.zeros((len(MENU), P))
    # lobe gradients (per alpha, combined later with WL)
    dlobe_s = 2 * np.real(np.conj(SA)[:, None] * C * ia * E) - 8 * np.real(np.conj(V)[:, None] * ia * E)
    dlobe_y = 2 * np.real(np.conj(SA)[:, None] * D * E)
    cls = classes(y)
    high = np.zeros(len(al)); dh_s = np.zeros((len(al), P)); dh_y = np.zeros((len(al), P))
    Vs, Ss = [], []
    for K in cls:
        k = K[np.argmin(y[K])]; ci = C[:, k]; Vi = E[:, K].sum(1); Si = (C[:, K] * E[:, K]).sum(1); Spi = Si - ci * Vi
        Vs.append(Vi); Ss.append(Si)
        den = ci ** 2 - 4; den[0] = 1.0
        cands = []
        for th in THETAS:
            a = (1 - th) * den; b = ci ** 2 / (th * den) - 1
            cands.append(a * np.abs(Vi) ** 2 - b * np.abs(Spi) ** 2)
        cands = np.array(cands); cands[:, 0] = 0.0; jbest = np.argmax(cands, 0); J = cands[jbest, np.arange(len(al))]
        high += J
        if grad:
            th = np.array(THETAS)[jbest]; a = (1 - th) * den; b = ci ** 2 / (th * den) - 1
            for p in K:
                dV = ia[:, 0] * E[:, p]; dSp = ia[:, 0] * (C[:, p] - ci) * E[:, p]
                dh_s[:, p] += a * 2 * np.real(np.conj(Vi) * dV) - b * 2 * np.real(np.conj(Spi) * dSp)
                dSp_y = D[:, p] * E[:, p] if p != k else D[:, k] * E[:, k] - D[:, k] * Vi
                g = -b * 2 * np.real(np.conj(Spi) * dSp_y)
                if p == k:
                    da = (1 - th) * 2 * ci * D[:, k]; db = -8 * ci * D[:, k] / (th * den ** 2)
                    g = g + da * np.abs(Vi) ** 2 - db * np.abs(Spi) ** 2
                g[0] = 0.0; dh_y[:, p] += g
            dh_s[0, :] = 0.0
    m = len(cls)
    if mode == 'primary':
        for i in range(m):
            for j in range(i + 1, m):
                aS = np.sqrt(np.abs(Ss[i]) ** 2 + EPS); bS = np.sqrt(np.abs(Ss[j]) ** 2 + EPS)
                aV = np.sqrt(np.abs(Vs[i]) ** 2 + EPS); bV = np.sqrt(np.abs(Vs[j]) ** 2 + EPS)
                high -= 2 * (aS * bS + 4 * aV * bV)
                if grad:
                    for (Ki, A_S, B_S, A_V, B_V, Si_, Vi_) in ((cls[i], aS, bS, aV, bV, Ss[i], Vs[i]), (cls[j], bS, aS, bV, aV, Ss[j], Vs[j])):
                        for p in Ki:
                            dS = ia[:, 0] * C[:, p] * E[:, p]; dV = ia[:, 0] * E[:, p]
                            dh_s[:, p] -= 2 * (np.real(np.conj(Si_) * dS) / A_S * B_S + 4 * np.real(np.conj(Vi_) * dV) / A_V * B_V)
                            dSy = D[:, p] * E[:, p]
                            dh_y[:, p] -= 2 * (np.real(np.conj(Si_) * dSy) / A_S * B_S)
    else:
        own = sum(np.abs(Ss[i]) ** 2 - 4 * np.abs(Vs[i]) ** 2 for i in range(m))
        high += lobe - own                                   # exact between-class terms
        if grad:
            dh_s += dlobe_s; dh_y += dlobe_y
            for i, K in enumerate(cls):
                for p in K:
                    dh_s[:, p] -= 2 * np.real(np.conj(Ss[i]) * ia[:, 0] * C[:, p] * E[:, p]) - 8 * np.real(np.conj(Vs[i]) * ia[:, 0] * E[:, p])
                    dh_y[:, p] -= 2 * np.real(np.conj(Ss[i]) * D[:, p] * E[:, p])
    Ld = WL @ lobe + WH @ high
    d = s[:, None] - s[None, :]; gv, gd = gtab(d); np.fill_diagonal(gv, 0.0); np.fill_diagonal(gd, 0.0); Tg = 4 * gv.sum()
    mx = Ld.max(); w = np.exp(BETA * (Ld - mx)); val = Tg + mx + np.log(w.sum()) / BETA; w /= w.sum()
    if not grad: return Tg + Ld.max(), Ld, Tg, len(cls)
    WLc = w @ WL; WHc = w @ WH
    g_s = WLc @ dlobe_s + WHc @ dh_s + 8 * gd.sum(1); g_y = WLc @ dlobe_y + WHc @ dh_y
    return val, np.concatenate([g_s, g_y])
def truth(s, y):
    E = np.exp(2j * np.pi * np.outer(al, s)); SA = (2 * np.cosh(2 * np.pi * np.outer(al, y)) * E).sum(1)
    d = s[:, None] - s[None, :]; gv, _ = gtab(d); np.fill_diagonal(gv, 0.0)
    return float(W2 @ (np.abs(SA) ** 2 - 4 * np.abs(E.sum(1)) ** 2)) + 4 * gv.sum()
def report(tag, s, y):
    s = np.asarray(s, float); y = np.asarray(y, float); P = len(s); z = np.concatenate([s, y])
    L1, Ld1, Tg, m = Lval(z, P, 'primary', False); L2 = Lval(z, P, 'diag', False)[0]
    print('  %-30s P=%2d y∈[%.2f,%.2f] classes %2d | L_primary %+11.4g (d*=%.3f) | L_diag %+11.4g | truth %+11.4g'
          % (tag, P, y.min(), y.max(), m, L1, MENU[int(np.argmax(Ld1))], L2, truth(s, y)), flush=True)
    return L1, L2
def search(P, starts, mode):
    best = (np.inf, None)
    for s0, y0 in starts:
        try:
            r = minimize(Lval, np.concatenate([s0, y0]), args=(P, mode), jac=True, method='L-BFGS-B',
                         bounds=[(None, None)] * P + [(0.8, 20.0)] * P, options={'maxiter': 2000})
            v = Lval(r.x, P, mode, False)[0]
        except (FloatingPointError, ValueError):
            continue
        if v < best[0]: best = (v, r.x.copy())
    return best
if __name__ == '__main__':
    mode = sys.argv[1]; rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 29)
    seeds = {}
    def add(P, s, y): seeds.setdefault(int(P), []).append((np.asarray(s, float), np.asarray(y, float)))
    for P, c in json.load(open('e25_free.json')).items(): add(P, c['s'], c['y'])
    for P in (5, 6, 8, 12, 16, 24, 32):
        for pre in ('e28_free_', 'e28_freediag_'):
            try: c = json.load(open('%s%d.json' % (pre, P))); add(P, c['s'], c['y'])
            except FileNotFoundError: pass
    for P in (6, 8, 12, 16, 24, 32):
        c = json.load(open('e23_arch_%d.json' % P)); add(P, c['s'], c['y'])
    for P in (16, 24, 32):
        c = json.load(open('e9_cfg_%d.json' % P)); add(P, c['s'], c['y'])
    for P in (5, 6, 8, 12, 16, 24, 32):
        for a in (1.0, 1.1, 1.25):
            t = np.arange(P) / (P - 1); s = a * np.arange(P) + rng.normal(0, 0.02, P)
            add(P, s, np.full(P, 0.85)); add(P, s, 0.8 + 0.6 * np.sin(np.pi * t) ** 0.8)
        for Y in (5.0, 10.0, 20.0):
            s = np.sort(rng.uniform(0, 1.2 * P, P)); y = rng.uniform(0.8, 1.5, P); y[rng.choice(P, max(1, P // 4), replace=False)] = Y; add(P, s, y)
        for t in range(6):
            s = np.sort(rng.uniform(0, rng.uniform(0.4, 2.0) * P, P)); y = np.where(rng.random(P) < 0.8, rng.uniform(0.8, 2.0, P), rng.uniform(0.8, 20, P)); add(P, s, y)
    print('== search target: %s' % mode, flush=True)
    worst = {}
    for P in (5, 6, 8, 12, 16, 24, 32):
        b = search(P, seeds[P], mode)
        s, y = b[1][:P], b[1][P:]; o = np.argsort(s)
        L1, L2 = report('min (%s) P=%d' % (mode, P), s[o], y[o])
        v = L1 if mode == 'primary' else L2
        print('      %s  s %s\n      y %s' % ('PASS' if v >= 0 else 'FAIL', np.round(s[o] - s[o][0], 3).tolist(), np.round(y[o], 3).tolist()), flush=True)
        json.dump({'s': s[o].tolist(), 'y': y[o].tolist(), 'L': v}, open('e29_%s_%d.json' % (mode, P), 'w'))
    print('== e24b gap configurations (P=26)', flush=True)
    for Y in (5.0, 10.0):
        for G in (1.0, 3.0):
            blk = 0.6 * np.arange(8); s = np.concatenate([blk, blk + 4.2 + G, blk + 2 * (4.2 + G), [4.2 + G / 2, 2 * (4.2 + G) - G / 2]])
            y = np.concatenate([np.full(24, 0.8), np.full(2, Y)]); report('gap seed Y=%g G=%g' % (Y, G), s, y)
            b = search(26, [(s, y)], mode); report('  -> adversary (%s)' % mode, b[1][:26], b[1][26:])
