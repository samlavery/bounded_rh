"""E27: (2) angle bound for the gap cell under phi = q T_d (d = 1/2):
   int phi |c_* V + S_D|^2 >= (1 - |cos th|)(M + R),  M = int phi c_*^2 |V|^2, R = int phi |S_D|^2,
   cos th = Re<c_* V, S_D>_phi / sqrt(M R);  low-alpha pencil source: a^2 = share of M on |al| <= al1, b^2 = share of R there,
   |cos th| <= a b + sqrt((1-a^2)(1-b^2)).
(3) high band for sparse chains: w_h = q (1 - T_{1/2}) (two-sided); Ingham-type ratio r(gamma) = 2 sum_{k>=1} |psi(k gamma)| / psi(0),
   psi = FT(w_h); lattice peak formula; and the high band at the e25 sparse minimisers."""
import json, numpy as np
from common import *
def gapcfg(Y, G):
    blk = 0.6 * np.arange(8); s = np.concatenate([blk, blk + 4.2 + G, blk + 2 * (4.2 + G), [4.2 + G / 2, 2 * (4.2 + G) - G / 2]])
    return s, np.concatenate([np.full(24, 0.8), np.full(2, Y)])
T = np.clip(1 - al / 0.5, 0, None); wphi = W2 * T
print('(2) angle bound, phi = q T_{1/2}')
for Y in (1.5, 3.0, 5.0, 10.0, 20.0):
    for G in (1.0, 2.0, 3.0, 4.0):
        s, y = gapcfg(Y, G); P = len(s)
        E = np.exp(2j * np.pi * np.outer(al, s)); V = E.sum(1)
        ys = y.min(); Bs = 2 * np.cosh(2 * np.pi * al * ys) - 2; cs = 2 + Bs
        Bm = 2 * np.cosh(2 * np.pi * np.outer(al, y)) - 2; SD = ((Bm - Bs[:, None]) * E).sum(1)
        X = cs * V
        M = float(wphi @ np.abs(X) ** 2); R = float(wphi @ np.abs(SD) ** 2); C = float(wphi @ np.real(np.conj(X) * SD))
        cth = C / np.sqrt(M * R) if R > 0 else 0.0
        d = (s[:, None] - s[None, :]).ravel(); tgt = 4 * g0 * P + 4 * float((K_of(d) - g_of(d)).sum())
        lb = (1 - abs(cth)) * (M + R)
        # pencil-style angle from the low-alpha split
        best = 1.0
        for al1 in (0.02, 0.05, 0.1, 0.15, 0.2):
            lo = al <= al1
            a2 = float(wphi[lo] @ np.abs(X[lo]) ** 2) / M; b2 = float(wphi[lo] @ np.abs(SD[lo]) ** 2) / R
            best = min(best, np.sqrt(a2 * b2) + np.sqrt((1 - a2) * (1 - b2)))
        print('  Y=%5.1f G=%.1f: |cos th| = %.6f  (low-alpha pencil bound %.6f) | angle LB %.3g vs target %.1f -> ratio %.3g ; pencil-angle LB ratio %.3g'
              % (Y, G, abs(cth), best, lb, tgt, lb / tgt, (1 - best) * (M + R) / tgt), flush=True)
print('(3) high band, w_h = q (1 - T_{1/2})')
wh = W2 * (1 - T)
psi = lambda u: float(np.cos(2 * np.pi * al * u) @ wh)
p0 = psi(0.0); print('  psi(0) = int w_h = %.4f' % p0)
for gam in (0.8, 1.0, 1.25, 1.5, 2.0, 3.0):
    r = 2 * sum(abs(psi(k * gam)) for k in range(1, 200)) / p0
    print('  gamma=%.2f: Ingham-type ratio r = 2 sum_k |psi(k gamma)|/psi(0) = %.3f  -> int w_h |V|^2 >= %.3f P' % (gam, r, p0 * (1 - r)), flush=True)
for a in (1.0, 1.25, 1.5, 1.7, 2.0, 3.0):
    al_pk = 1 / a
    if al_pk < 1:
        q1 = float(qfun(np.array([al_pk]))[0])
        for y0 in (0.8, 1.0):
            c2 = (2 * np.cosh(2 * np.pi * al_pk * y0)) ** 2
            print('  lattice a=%.2f y=%.1f: peak alpha=%.3f q=%.4f c^2=%.1f -> high-band peak ~ 2 q c^2 P/a = %.1f P (target ~4 P)' % (a, y0, al_pk, q1, c2, 2 * q1 * c2 / a))
r = json.load(open('e25_free.json'))
for P, c in r.items():
    s = np.array(c['s']); y = np.array(c['y']); E = np.exp(2j * np.pi * np.outer(al, s))
    SA = (2 * np.cosh(2 * np.pi * np.outer(al, y)) * E).sum(1)
    d = (s[:, None] - s[None, :]).ravel(); tgt = 4 * g0 * len(s) + 4 * float((K_of(d) - g_of(d)).sum())
    print('  e25 sparse minimiser P=%s: min gap %.2f | high band int w_h |S_A|^2 = %.1f vs target %.1f (ratio %.1f)' % (P, np.diff(s).min(), float(wh @ np.abs(SA) ** 2), tgt, float(wh @ np.abs(SA) ** 2) / tgt))
