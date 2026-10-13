"""E22: sharp-lobe lower bound for (1').  w = kappa T_a^2, T_a = (1-|a|/a0)_+, kappa = min_{|al|<=a0} q/T_a^2 (so w <= q).
Exact lower bound  ||S_A||_q^2 >= int w |S_A|^2 >= int w (4|V|^2 + 4 Re(conj V S_B))  =  4 kappa sum_p D_p + C_B,
D_p = sum_{p'} Phi(s_p - s_p'), Phi = FT(T_a^2) >= 0 (local pair density at scale 1/a0), C_B the low-band B cross term.
Compare with the (1') target 4 g0 P + 4 sum h.  Also the full low band int w |S_A|^2 (keeping |S_B|^2)."""
import json, sys, numpy as np
from common import *
def run(name, s, y, a0s=(0.05, 0.1, 0.15, 0.2, 0.3)):
    s = np.asarray(s, float); y = np.asarray(y, float); P = len(s)
    E = np.exp(2j * np.pi * np.outer(al, s)); Bm = 2 * np.cosh(2 * np.pi * np.outer(al, y)) - 2
    V = E.sum(1); SB = (Bm * E).sum(1); SA = 2 * V + SB
    d = (s[:, None] - s[None, :]).ravel(); tgt = 4 * g0 * P + 4 * float((K_of(d) - g_of(d)).sum())
    tot = float(W2 @ np.abs(SA) ** 2)
    out = []
    for a0 in a0s:
        T = np.clip(1 - al / a0, 0, None); m = T > 0
        kap = float(np.min(qa[m] / T[m] ** 2))
        w2 = 2 * kap * T ** 2 * wa                                # two-sided weight on the grid
        lobeV = float(w2 @ (4 * np.abs(V) ** 2)); CB = float(w2 @ (4 * np.real(np.conj(V) * SB)))
        full = float(w2 @ np.abs(SA) ** 2)
        out.append('a0=%.2f k=%.3f: 4kΣD %.1f + C_B %+.1f = %.1f (full lobe %.1f)' % (a0, kap, lobeV, CB, lobeV + CB, full))
    print('%-16s P=%2d ||S_A||^2 %.1f target %.1f |' % (name, P, tot, tgt), ' | '.join(out), flush=True)
cf = {}
for P in (16, 24, 32, 48):
    c = json.load(open('e9_cfg_%d.json' % P)); cf['e9 P=%d' % P] = (c['s'], c['y'])
for a in (0.6, 0.76, 1.0):
    for yy in (0.8, 2.0):
        cf['lat a=%.2f y=%.1f' % (a, yy)] = (a * np.arange(32), [yy] * 32)
e12 = json.load(open('e12_k6.json'))
for m in ('8', '32'):
    e = e12[m]; cf['e12 m=%s' % m] = (np.repeat(e['s'], np.array(e['m']).astype(int)), np.repeat(e['y'], np.array(e['m']).astype(int)))
for k, (s, y) in cf.items(): run(k, s, y)
