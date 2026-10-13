"""Exact LP quantity on the DP's binding chains (mirrored two-sided, full T_g with all pairs, field with exact L):
LP_exact >= T_g(full) + int qf B^2 + 4 L(0) + 2 sum_env m L(x).  Chains: (a) doubles at n - 1/32 (n = 1..10) then spacing 0.9375
to 24 (the y <= 0.5 pattern); (b) dense cluster of alternating doubles/simples at spacing 1/32 on [0.5, 0.95] (the y >= 0.7 pattern)."""
import sys, numpy as np
exec(open('chain_dp.py').read().split("h = 1.0 / HD")[0].replace("HD, XMAX, MS = int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]", "HD, XMAX, MS = 32, 24.0, '12'"))
def LPexact(xr, mr, y):
    x = np.concatenate([xr, -xr]); m = np.concatenate([mr, mr])
    allx = np.concatenate([[0.0], x]); allm = np.concatenate([[2.0], m])
    D = np.abs(allx[:, None] - allx[None, :]); M = allm[:, None] * allm[None, :]
    Tg = float(np.sum(M * gfun(D.ravel()).reshape(D.shape)) - np.sum(allm ** 2) * gfun(0.0)[0])
    return Tg + SB2(y) + 4 * Lfun(y, 0.0)[0] + 2 * float(np.sum(m * Lfun(y, x))), Tg
xa = np.concatenate([np.arange(1, 11) - 1 / 32, 10 - 1 / 32 + 0.9375 * np.arange(1, 15)]); ma = np.full(len(xa), 2.0)
xa_int = np.arange(1, 25).astype(float)
xb = np.arange(0.5, 0.96, 1 / 32); mb = np.array([2.0 if i % 2 == 0 else 1.0 for i in range(len(xb))])
for y in (0.1, 0.2, 0.3, 0.5, 0.7, 1.0):
    a, ta = LPexact(xa, ma, y); ai, tai = LPexact(xa_int, np.full(24, 2.0), y); b, tb = LPexact(xb, mb, y)
    print('y=%.2f: (a) DP pattern LP %+.4e (T_g %.3f) | doubles exactly at integers 1..24 LP %+.4e (= int qfB^2 %.3e + T_g %.4f + truncation) | (b) dense cluster LP %+.4e (T_g %.1f)'
          % (y, a, ta, ai, SB2(y), tai, b, tb), flush=True)
