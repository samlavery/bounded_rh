"""E28 (pre-registered by the lead, 2026-10-09): the COMBINED partition-of-unity bound for (1').
q = qT + q(1-T), T = (1-|al|/d)_+, d in the FIXED menu {1/4, 3/8, 1/2}.
  lobe  : int qT (|S_A|^2 - 4|V|^2) = (ii)_T + (iii)_T   (exact)
  high  : int q(1-T)(|S_A|^2 - 4|V|^2) >= - 4 int q(1-T) |S_A - c V|^2 / (c^2 - 4)    (pointwise in al, any c(al) > 2)
  Q_pp + T_g^pp >= L := T_g^pp + max_d [ (ii)_T + (iii)_T - err_high ].
PRIMARY (declared before the run): c = c_* = 2cosh(2 pi al y_min)  (global reference depth = minimum depth).
DIAGNOSTIC (declared before the run, secondary): c(al) = pointwise optimum of |S_A - cV|^2/(c^2-4) over c > 2; this upper-bounds
every per-band choice of c, so a FAIL there means no per-band reference can pass.
Adversary minimises L (primary) directly; P = 3,4,5,6,8,12,16,24,32; depths in [0.8, 20]; seeds: e25 sparse minimisers, e24b gap
configurations (P = 26, reported separately), e9, arches (e23, e20 form), pinned deep pairs (Y = 5, 10, 20), random.
Pinned runs (deep pairs held at Y) are reported separately.  PASS = min L >= 0 for every P."""
import sys, json, numpy as np
from scipy.optimize import minimize
from common import *
MENU = (0.25, 0.375, 0.5)
TT = np.array([np.clip(1 - al / d, 0, None) for d in MENU])
WL = W2[None, :] * TT; WH = W2[None, :] * (1 - TT); WH[:, 0] = 0.0
U = np.linspace(0.0, 64.0, 128001); GT = g_of(U); GT[0] = g0; dGT = np.gradient(GT, U)
def gtab(u):
    a = np.abs(u); return np.interp(a, U, GT, right=0.0), np.interp(a, U, dGT, right=0.0) * np.sign(u)
BETA = 4.0; ia = (2j * np.pi * al)[:, None]
def parts(s, y, mode='primary'):
    E = np.exp(2j * np.pi * np.outer(al, s)); C = 2 * np.cosh(2 * np.pi * np.outer(al, y)); D = 4 * np.pi * al[:, None] * np.sinh(2 * np.pi * np.outer(al, y))
    SA = (C * E).sum(1); V = E.sum(1)
    if mode == 'primary':
        k = int(np.argmin(y)); c = C[:, k]
    else:
        A_ = np.abs(SA) ** 2; Cv = np.abs(V) ** 2; B_ = np.real(np.conj(SA) * V)
        c = np.full(len(al), np.inf); best = Cv.copy()          # c -> inf limit: f = |V|^2
        disc = np.sqrt(np.maximum((4 * Cv + A_) ** 2 - 16 * B_ ** 2, 0))
        for sg in (1, -1):
            with np.errstate(divide='ignore', invalid='ignore'):
                cc = ((4 * Cv + A_) + sg * disc) / (2 * B_)
            ok = np.isfinite(cc) & (cc > 2 + 1e-12)
            fv = np.where(ok, (A_ - 2 * cc * B_ + cc ** 2 * Cv) / np.where(ok, cc ** 2 - 4, 1), np.inf)
            better = fv < best; best = np.where(better, fv, best); c = np.where(better, cc, c)
        k = None
    return E, C, D, SA, V, c, k
def L_and_grad(z, P, mode='primary', pin=None, want_grad=True):
    s, y = z[:P], z[P:]
    E, C, D, SA, V, c, k = parts(s, y, mode)
    lobe_int = np.abs(SA) ** 2 - 4 * np.abs(V) ** 2
    if mode == 'primary':
        Sd = SA - c * V; den = c ** 2 - 4; den[0] = 1.0; rat = np.abs(Sd) ** 2 / den; rat[0] = 0.0
    else:
        cf = np.where(np.isfinite(c), c, 0.0)
        Sd = np.where(np.isfinite(c), SA - cf * V, 0.0); den = np.where(np.isfinite(c), cf ** 2 - 4, 1.0)
        rat = np.where(np.isfinite(c), np.abs(Sd) ** 2 / den, np.abs(V) ** 2); rat[0] = 0.0
    Ld = WL @ lobe_int - 4 * (WH @ rat)
    d = s[:, None] - s[None, :]; gv, gd = gtab(d); np.fill_diagonal(gv, 0.0); np.fill_diagonal(gd, 0.0); Tg = 4 * gv.sum()
    mx = Ld.max(); w = np.exp(BETA * (Ld - mx)); val = Tg + mx + np.log(w.sum()) / BETA; w /= w.sum()
    if not want_grad: return val, Ld, Tg
    WLc = w @ WL; WHc = w @ WH
    gs = WLc @ (2 * np.real(np.conj(SA)[:, None] * C * ia * E) - 8 * np.real(np.conj(V)[:, None] * ia * E))
    gy = WLc @ (2 * np.real(np.conj(SA)[:, None] * D * E))
    if mode == 'primary':
        cc = c[:, None]
        gs -= 4 * (WHc / den) @ (2 * np.real(np.conj(Sd)[:, None] * (C - cc) * ia * E))
        gyh = (WHc / den) @ (2 * np.real(np.conj(Sd)[:, None] * D * E))
        Dk = D[:, k]
        dk = (2 * np.real(np.conj(Sd) * Dk * (E[:, k] - V)) * den - np.abs(Sd) ** 2 * 2 * c * Dk) / den ** 2
        dk[0] = 0.0
        gyh[k] = WHc @ dk
        gy -= 4 * gyh
    else:
        fin = np.isfinite(c)[:, None]; cc = np.where(np.isfinite(c), c, 0.0)[:, None]
        gs -= 4 * (WHc / den) @ np.where(fin, 2 * np.real(np.conj(Sd)[:, None] * (C - cc) * ia * E), 2 * np.real(np.conj(V)[:, None] * ia * E))
        gy -= 4 * (WHc / den) @ np.where(fin, 2 * np.real(np.conj(Sd)[:, None] * D * E), 0.0)
    gs = gs + 8 * gd.sum(1)
    g = np.concatenate([gs, gy])
    if pin is not None: g[P + np.asarray(pin)] = 0.0
    return val, g
def report(tag, s, y):
    s = np.asarray(s, float); y = np.asarray(y, float); P = len(s); z = np.concatenate([s, y])
    v1, Ld1, Tg = L_and_grad(z, P, 'primary', want_grad=False); v2, Ld2, _ = L_and_grad(z, P, 'diag', want_grad=False)
    E = np.exp(2j * np.pi * np.outer(al, s)); SA = (2 * np.cosh(2 * np.pi * np.outer(al, y)) * E).sum(1)
    QT = float(W2 @ (np.abs(SA) ** 2 - 4 * np.abs(E.sum(1)) ** 2)) + Tg
    L1 = Tg + Ld1.max(); L2 = Tg + Ld2.max()
    print('  %-34s P=%2d y∈[%.2f,%.2f] | L_primary %+10.4g (d*=%.3f) | L_diag %+10.4g | truth Q_pp+T_g %+10.4g | T_g %.2f'
          % (tag, P, y.min(), y.max(), L1, MENU[int(np.argmax(Ld1))], L2, QT, Tg), flush=True)
    return L1, L2
SEARCH_MODE = 'primary'
def search(P, starts, pin=None, Y=20.0):
    best = (np.inf, None)
    for s0, y0 in starts:
        bnds = [(None, None)] * P + [((y0[i], y0[i]) if (pin is not None and i in pin) else (0.8, 20.0)) for i in range(P)]
        try:
            r = minimize(L_and_grad, np.concatenate([s0, y0]), args=(P, SEARCH_MODE, pin), jac=True, method='L-BFGS-B', bounds=bnds,
                         options={'maxiter': 2500})
            v = L_and_grad(r.x, P, SEARCH_MODE, want_grad=False); L1 = v[2] + v[1].max()
        except (FloatingPointError, ValueError):
            continue
        if L1 < best[0]: best = (L1, r.x.copy())
    return best
if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
    which = sys.argv[1]
    if which.endswith('diag'):
        SEARCH_MODE = 'diag'; which = which[:-4]
        print('== search target: DIAGNOSTIC bound (pointwise-optimal c(al), declared before the run)', flush=True)
    seeds = {}
    def add(P, s, y): seeds.setdefault(P, []).append((np.asarray(s, float), np.asarray(y, float)))
    for P, c in json.load(open('e25_free.json')).items(): add(int(P), c['s'], c['y'])
    for P in (3, 4, 6, 8, 12, 16, 24, 32):
        c = json.load(open('e23_arch_%d.json' % P)); add(P, c['s'], c['y'])
    for P in (16, 24, 32):
        c = json.load(open('e9_cfg_%d.json' % P)); add(P, c['s'], c['y'])
    for P, (a, A, k) in {16: (0.6739, 0.9803, 0.804), 24: (0.7544, 1.2758, 0.790), 32: (0.7552, 1.7195, 0.804)}.items():
        t = np.arange(P) / (P - 1); add(P, a * np.arange(P), 0.8 + A * np.sin(np.pi * t) ** k)
    Ps = (3, 4, 5, 6, 8, 12, 16, 24, 32)
    if which == 'free':
        print('== FREE search (primary c_* = c(y_min)); seeds then random', flush=True)
        for P in Ps:
            st = list(seeds.get(P, []))
            for t in range(10):
                kind = t % 3
                if kind == 0: s0 = np.sort(rng.uniform(0, rng.uniform(0.3, 2.0) * P, P))
                elif kind == 1: s0 = rng.uniform(0.5, 1.9) * np.arange(P) + rng.normal(0, 0.03, P)
                else:
                    k = max(2, P // 3); sites = np.sort(rng.uniform(0, 0.8 * k, k)); s0 = np.sort(sites[rng.integers(0, k, P)] + rng.normal(0, 0.01, P))
                y0 = np.where(rng.random(P) < 0.85, rng.uniform(0.8, 2.0, P), rng.uniform(0.8, 20.0, P)); st.append((s0, y0))
            for Y in (5.0, 10.0, 20.0):     # pinned-deep seeds, then released (free)
                s0 = np.sort(rng.uniform(0, 0.8 * P, P)); y0 = rng.uniform(0.8, 1.5, P); y0[rng.choice(P, max(1, P // 4), replace=False)] = Y
                st.append((s0, y0))
            for s0, y0 in st: report('seed', s0, y0) if False else None
            best = search(P, st)
            s, y = best[1][:P], best[1][P:]; o = np.argsort(s)
            L1, L2 = report('FREE min P=%d' % P, s[o], y[o])
            Ld = L2 if SEARCH_MODE == 'diag' else L1
            print('      %s  s %s\n      y %s' % ('PASS' if Ld >= 0 else 'FAIL', np.round(s[o] - s[o][0], 3).tolist(), np.round(y[o], 3).tolist()), flush=True)
            json.dump({'s': s[o].tolist(), 'y': y[o].tolist(), 'L': Ld}, open('e28_free%s_%d.json' % ('diag' if SEARCH_MODE == 'diag' else '', P), 'w'))
    elif which == 'pinned':
        print('== PINNED search (deep pairs held at Y, primary c_*)', flush=True)
        for P in Ps:
            for Y in (5.0, 10.0, 20.0):
                st = []; pins = []
                for t in range(6):
                    kp = [1, 2, max(1, P // 4)][t % 3]
                    s0 = np.sort(rng.uniform(0, rng.uniform(0.5, 1.8) * P, P)); y0 = rng.uniform(0.8, 1.5, P)
                    pin = rng.choice(P, min(kp, P), replace=False); y0[pin] = Y; st.append((s0, y0)); pins.append(pin)
                best = (np.inf, None)
                for (s0, y0), pin in zip(st, pins):
                    b = search(P, [(s0, y0)], pin=list(pin))
                    if b[0] < best[0]: best = b
                s, y = best[1][:P], best[1][P:]; o = np.argsort(s)
                L1, L2 = report('PINNED Y=%g min P=%d' % (Y, P), s[o], y[o])
                print('      %s  s %s\n      y %s' % ('PASS' if L1 >= 0 else 'FAIL', np.round(s[o] - s[o][0], 3).tolist(), np.round(y[o], 2).tolist()), flush=True)
    elif which == 'gaps':
        print('== e24b gap configurations (P = 26): at seed, then free adversary from the seed', flush=True)
        for Y in (5.0, 10.0):
            for G in (1.0, 2.0, 3.0, 4.0):
                blk = 0.6 * np.arange(8); s = np.concatenate([blk, blk + 4.2 + G, blk + 2 * (4.2 + G), [4.2 + G / 2, 2 * (4.2 + G) - G / 2]])
                y = np.concatenate([np.full(24, 0.8), np.full(2, Y)])
                report('gap seed Y=%g G=%.0f' % (Y, G), s, y)
                b = search(26, [(s, y)]); report('  -> free adversary', b[1][:26], b[1][26:])
                b = search(26, [(s, y)], pin=[24, 25]); report('  -> adversary, deep pinned', b[1][:26], b[1][26:])
