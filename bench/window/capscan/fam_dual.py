"""Dual tightening for the 25-mode FAMILY (all c in R^24, w0 = sqrt 2; f >= 0 not imposed, as in txt:403-404).

The family ceiling for a word set S is min over per-point mixtures of max over c, which by minimax equals max over c of
each window's tightened ceiling.  Bracketing:
  upper U = min over tried two-word mixtures M of r(M) = root of max_c [H - r(1 - Ef)]   (each M obstructs the family)
  lower Lo = max over tried windows c of r_c = that window's tightened ceiling over the word search (a window the
             searched words cannot push below Lo).
Alternation: c(M) = the maximising window at r(M); words(c) = its best words; new mixtures from the word pool."""
import sys, json, math, time, itertools
import numpy as np
import mpmath as mp
from scipy.optimize import minimize
from dual import make_qf, H_of, QFTable, Ef_word, min_word, lower_hull, ceiling_from_hull, envelope_at
from capcore import freqs, Amass, prep, obstruction_pre

K = 24; mp.mp.dps = 30
w = freqs(K, mp.sqrt(2)); A = Amass(mp.sqrt(2))

def exact_word(g):
    L = int(round(sum(g))); s = sum(g)
    return (len(g), L, [mp.mpf(x) * L / mp.mpf(s) for x in g])

def family_ceiling(w1, w2, lo=0.6725, hi=0.6760):
    pre = prep(w, A, [exact_word(w1), exact_word(w2)])
    F = lambda r: obstruction_pre(mp.mpf(r), pre)[0]
    if F(lo) < 0 or F(hi) > 0: return None, None
    a, b = mp.mpf(lo), mp.mpf(hi)
    while b - a > 1e-11:
        m = (a + b) / 2
        if F(m) >= 0: a = m
        else: b = m
    val, lam, cstar, P11 = obstruction_pre(a, pre, ret_c=True)
    return float(a), np.array([float(x) for x in cstar])

def refine(T, g0):
    g0 = np.asarray(g0, float); L = float(round(g0.sum())); g0 = g0 * L / g0.sum(); q = len(g0)
    cons = ({'type': 'eq', 'fun': lambda g: g.sum() - L, 'jac': lambda g: np.ones_like(g)},)
    r = minimize(lambda g: Ef_word(g, T), g0, method='SLSQP', bounds=[(0, L)] * q, constraints=cons,
                 options={'maxiter': 500, 'ftol': 1e-14})
    return float(r.fun), r.x

def window_words(c, qmax=8):
    """tightened ceiling of window c and its best words (q <= qmax at integer periods, plus block words)"""
    H = H_of(c); T = QFTable(make_qf(c)); rng = np.random.default_rng(3); pts = []
    for q in range(1, qmax + 1):
        for L in range(int(math.ceil(0.7 * q)), int(3.0 * q) + 1):
            e, g = min_word(T, q, L / q, starts=10, rng=rng)
            pts.append((L / q, e, q, list(map(float, g))))
    # block words from the best L=3 (q=2) and L=4 (q=3) words
    b2 = min((p for p in pts if p[2] == 2 and abs(p[0] - 1.5) < 1e-9), key=lambda p: p[1])[3]
    b3 = min((p for p in pts if p[2] == 3 and abs(p[0] - 4 / 3) < 1e-9), key=lambda p: p[1])[3]
    for n2 in range(1, 40):
        word = []
        for slot in range(n2 + 1):
            word += (b3 if slot == n2 // 2 else b2)
        e, g = refine(T, word)
        pts.append((sum(g) / len(g), e, len(g), list(map(float, g))))
    hl = lower_hull(pts); r = ceiling_from_hull(H, hl)
    e, (x1, x2, t) = envelope_at(hl, 1 / r)
    used = [h for h in hl if h[0] in (x1, x2)]
    return r, used, hl

if __name__ == '__main__':
    t0 = time.time()
    PA = [5189 / 5000, 9811 / 5000]; PB = [10289 / 10000, 10289 / 10000, 9711 / 5000]
    U, cU = family_ceiling(PB, PA)
    print('control: family ceiling with the paper words %.10f (%.0fs)' % (U, time.time() - t0), flush=True)
    pool = [PA, PB]; best_pair = ('paper', PB, PA); Lo = 0.0; c = cU
    for it in range(6):
        rc, used, hl = window_words(c)
        Lo = max(Lo, rc)
        print('it %d: maximising window -> its tightened ceiling r_c = %.10f; best words q=%s (%.0fs)'
              % (it, rc, [u[2] for u in used], time.time() - t0), flush=True)
        for u in used:
            if not any(len(p) == len(u[3]) and np.allclose(p, u[3], atol=1e-6) for p in pool): pool.append(u[3])
        # all pairs in the pool straddling the current density
        cand = []
        for w1, w2 in itertools.combinations(pool, 2):
            d1, d2 = sum(w1) / len(w1), sum(w2) / len(w2)
            if min(d1, d2) < 1 / U + 0.02 and max(d1, d2) > 1 / U - 0.02 and abs(d1 - d2) > 1e-9:
                cand.append((w1, w2))
        newU = None
        for w1, w2 in cand:
            lo_, hi_ = sorted([w1, w2], key=lambda x: sum(x) / len(x))
            r, cs = family_ceiling(lo_, hi_)
            if r is not None and (newU is None or r < newU[0]): newU = (r, cs, lo_, hi_)
        if newU and newU[0] < U:
            U, c = newU[0], newU[1]; best_pair = ('it%d' % it, newU[2], newU[3])
        else:
            c = newU[1] if newU else c
        print('      family upper U = %.10f, lower Lo = %.10f; best pair q = %d, %d (%.0fs)'
              % (U, Lo, len(best_pair[1]), len(best_pair[2]), time.time() - t0), flush=True)
    json.dump(dict(U=U, Lo=Lo, pair=[list(map(float, best_pair[1])), list(map(float, best_pair[2]))],
                   c=list(map(float, c))), open('fam_dual_K24.json', 'w'), indent=1)
