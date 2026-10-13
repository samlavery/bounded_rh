"""E24: depth-spread x density cells for (1'), with large depths (y = 5, 10, 20).
w = kappa T^2 (Lemma SL weight; T = (1-|al|/a0)_+, kappa = min q/T^2), a0 scanned.
Exact on the lobe:  int w |S_A|^2 = int w |c_* V + S_D|^2,  c_* = 2 + B_*,  B_* = B at the minimum depth,
S_D = sum_p (B_p - B_*) e_p  (depth-difference spectrum, coefficients >= 0).
  E_low  = int w |S_A|^2                      (best any lobe argument can do)
  cellA  = (sqrt M - sqrt R)^2,  M = int w c_*^2 |V|^2, R = int w |S_D|^2      (small depth spread)
  cellB  = int w (4 + 4 B_*)|V|^2 + 4 Re int w conj(V) S_D                     (lead's exact C_B split, |S_B|^2 dropped)
  ΔB-part = 4 Re int w conj(V) S_D  (the only term that can be negative in cellB)
Target: 4 g0 P + 4 sum_{p,p'} h.  Full ||S_A||_q^2 is the truth."""
import json, numpy as np
from common import *
A0 = (0.01, 0.02, 0.04, 0.08, 0.125, 0.19, 0.25, 0.375)
def evalcfg(name, s, y):
    s = np.asarray(s, float); y = np.asarray(y, float); P = len(s)
    E = np.exp(2j * np.pi * np.outer(al, s)); V = E.sum(1)
    Bm = 2 * np.cosh(2 * np.pi * np.outer(al, y)) - 2; ys = y.min(); Bs = 2 * np.cosh(2 * np.pi * al * ys) - 2
    SA = 2 * V + (Bm * E).sum(1); SD = ((Bm - Bs[:, None]) * E).sum(1); cs = 2 + Bs
    d = (s[:, None] - s[None, :]).ravel(); tgt = 4 * g0 * P + 4 * float((K_of(d) - g_of(d)).sum())
    full = float(W2 @ np.abs(SA) ** 2)
    best = {'E_low': (-1e300, 0), 'cellA': (-1e300, 0), 'cellB': (-1e300, 0, 0)}
    for a0 in A0:
        T = np.clip(1 - al / a0, 0, None); m = T > 0; kap = float(np.min(qa[m] / T[m] ** 2)); w2 = 2 * kap * T ** 2 * wa
        El = float(w2 @ np.abs(SA) ** 2)
        M = float(w2 @ (cs ** 2 * np.abs(V) ** 2)); R = float(w2 @ np.abs(SD) ** 2); cA = (np.sqrt(M) - np.sqrt(R)) ** 2 if M >= R else 0.0
        dB = float(w2 @ (4 * np.real(np.conj(V) * SD))); cB = float(w2 @ ((4 + 4 * Bs) * np.abs(V) ** 2)) + dB
        if El > best['E_low'][0]: best['E_low'] = (El, a0)
        if cA > best['cellA'][0]: best['cellA'] = (cA, a0)
        if cB > best['cellB'][0]: best['cellB'] = (cB, a0, dB)
    f = lambda v: ('%.3g' % v)
    print('%-34s P=%2d y∈[%.1f,%.1f] tgt %6.1f full %9s | E_low %s (a0=%.3f) %s | cellA %s (a0=%.3f) %s | cellB %s (a0=%.3f, ΔB-part %s) %s'
          % (name, P, y.min(), y.max(), tgt, f(full), f(best['E_low'][0]), best['E_low'][1], 'ok' if best['E_low'][0] >= tgt else 'FAIL',
             f(best['cellA'][0]), best['cellA'][1], 'ok' if best['cellA'][0] >= tgt else 'FAIL',
             f(best['cellB'][0]), best['cellB'][1], f(best['cellB'][2]), 'ok' if best['cellB'][0] >= tgt else 'FAIL'), flush=True)
for P in (16, 24, 32, 48):
    c = json.load(open('e9_cfg_%d.json' % P)); evalcfg('e9 P=%d' % P, c['s'], c['y'])
for P in (3, 4, 6, 8, 12, 16, 24, 32):
    c = json.load(open('e23_arch_%d.json' % P)); evalcfg('arch (e19 min) P=%d' % P, c['s'], c['y'])
for Y in (5.0, 10.0, 20.0):
    for P in (8, 16, 32):
        for a in (0.6, 0.75, 1.0):
            t = np.arange(P) / (P - 1); evalcfg('arch Y=%g P=%d a=%.2f' % (Y, P, a), a * np.arange(P), 0.8 + (Y - 0.8) * np.sin(np.pi * t) ** 0.8)
    for m in (4, 8, 16):
        # two stacks of m at depth Y, chain of 6 shallow pairs between; and the inverse
        s = np.concatenate([np.zeros(m), 0.43 * np.arange(1, 7), np.full(m, 3.0)])
        evalcfg('stacks@Y=%g m=%d chain@0.8' % (Y, m), s, np.concatenate([np.full(m, Y), np.full(6, 0.8), np.full(m, Y)]))
        evalcfg('stacks@0.8 m=%d chain@Y=%g' % (m, Y), s, np.concatenate([np.full(m, 0.8), np.full(6, Y), np.full(m, 0.8)]))
    # dense shallow block with 3 deep pairs in the middle
    s = 0.75 * np.arange(24); y = np.full(24, 0.8); y[[11, 12, 13]] = Y; evalcfg('block24@0.8 + 3@Y=%g' % Y, s, y)
    # sparse alternating
    s = 1.5 * np.arange(16); y = np.where(np.arange(16) % 2 == 0, 0.8, Y); evalcfg('sparse a=1.5 alt 0.8/%g' % Y, s, y)
