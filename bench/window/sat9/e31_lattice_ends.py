"""E31: round 1 part (2), bulk/end decomposition for dense chains, the lattice case EXACTLY first.
Equal-depth lattice, spacing a < 1, depth y, P pairs:
  Q_pp(P) = int q (B^2 + 4B) sin^2(pi P a al)/sin^2(pi a al)            (exact; B = B_y)
          = C_end(a,y) - (1/2) int q (B^2+4B) cos(2 pi P a al)/sin^2(pi a al),
  C_end(a,y) = (1/2) int_{-1}^{1} q (B^2+4B)/sin^2(pi a al) dal   (finite: the integrand -> 16 y^2/a^2 q(0) at al = 0;
                                                                    no pole in the band since 1/a > 1)
  T_g^pp(P) = 8 sum_{k=1}^{P-1} (P-k) g(k a) = P tau(a) - 8 sum_k k g(ka) - (tail),   tau(a) = 8 sum_{k>=1} g(k a).
  So (1') on the lattice: Q_pp + T_g^pp = P tau(a) + [C_end - 8 sum_k k g(ka)] + osc(P).
Then the irregular minimisers (e23 refined e19 arches) against: (i) the same depths on the exact lattice of their mean spacing;
(ii) the equal-depth lattice at mean spacing and min / mean depth."""
import json, numpy as np
from common import *
def Qpp(s, y):
    E = np.exp(2j * np.pi * np.outer(al, s)); C = 2 * np.cosh(2 * np.pi * np.outer(al, y))
    return float(W2 @ (np.abs((C * E).sum(1)) ** 2 - 4 * np.abs(E.sum(1)) ** 2))
def Tg(s):
    d = s[:, None] - s[None, :]; off = ~np.eye(len(s), dtype=bool); return 4 * float(g_of(d[off]).sum())
def Cend(a, y):
    B = 2 * np.cosh(2 * np.pi * al * y) - 2; with_ = np.where(al > 0, (B ** 2 + 4 * B) / np.sin(np.pi * a * al) ** 2, 16 * y ** 2 / a ** 2)
    return 0.5 * float(W2 @ with_)
def tau(a): return 8 * float(g_of(a * np.arange(1, 400)).sum())
def endg(a): k = np.arange(1, 400); return 8 * float((k * g_of(a * k)).sum())
print('Equal-depth lattice: C_end(a,y) [exact limit of Q_pp as P->inf], tau(a) = bulk T_g per pair, end deficit 8 sum k g(ka)')
for a in (0.5, 0.6, 0.7, 0.76, 0.8, 0.9, 0.95):
    row = ' '.join('y=%.1f:%9.3f' % (y, Cend(a, y)) for y in (0.8, 1.0, 1.5, 2.0, 3.0))
    print('  a=%.2f  tau %.4f  end-def %.4f | C_end %s' % (a, tau(a), endg(a), row))
print('Finite P check (a=0.76, y=0.8): Q_pp(P), C_end, T_g(P), P tau + C_end - enddef, Q_pp+T_g')
for P in (4, 8, 16, 32, 64, 128):
    s = 0.76 * np.arange(P); y = np.full(P, 0.8)
    print('  P=%3d Q_pp %8.3f (C_end %.3f) T_g %8.3f | P tau + C_end - enddef = %8.3f | Q_pp + T_g = %8.3f'
          % (P, Qpp(s, y), Cend(0.76, 0.8), Tg(s), P * tau(0.76) + Cend(0.76, 0.8) - endg(0.76), Qpp(s, y) + Tg(s)))
print('Irregular minimisers (e23 = refined e19, depths in [0.8, 3]) vs lattice forms')
for P in (6, 8, 12, 16, 24, 32):
    c = json.load(open('e23_arch_%d.json' % P)); s = np.array(c['s']); y = np.array(c['y']); o = np.argsort(s); s, y = s[o], y[o]
    a = (s[-1] - s[0]) / (P - 1); gaps = np.diff(s)
    sl = s[0] + a * np.arange(P)
    v_act = Qpp(s, y) + Tg(s); v_lat = Qpp(sl, y) + Tg(sl)
    v_eq_min = Qpp(sl, np.full(P, y.min())) + Tg(sl); v_eq_mean = Qpp(sl, np.full(P, y.mean())) + Tg(sl)
    print('  P=%2d mean gap %.3f (gaps %.3f-%.3f), depths %.2f-%.2f | actual Q_pp %+8.3f T_g %7.3f total %+8.3f | same depths on lattice: Q_pp %+8.3f total %+8.3f | equal-depth lattice y_min: total %+8.3f, y_mean: %+8.3f | P tau(a) = %.3f'
          % (P, a, gaps.min(), gaps.max(), y.min(), y.max(), Qpp(s, y), Tg(s), v_act, Qpp(sl, y), v_lat, v_eq_min, v_eq_mean, P * tau(a)))
