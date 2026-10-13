"""kappa with edge windows (exact arithmetic, mpmath 50 digits; rational targets):
  A = c(m-q) + 2 sum_k c_t(k),  R = gtau(8/7, A),  P = B(m-q) + 2 sum_k B_t(k),  kappa = (H - P/m)/(1 - R/m),
  c = cN/SA (805124/10^8), c_t(k) = floor(floor_k (1 - delta_t) SA)/SA, B = 404350/10^8, H = 67216841/10^8, q = 7.
usage: python3 kappa_edge.py DELTA_T [k6_floor_override]"""
import sys, json, math
import mpmath as mp
mp.mp.dps = 50
H = mp.mpf(67216841) / 10**8; B = mp.mpf(404350) / 10**8; SA = 10**8; q = 7; tau = mp.mpf(8) / 7
def g(E): return E if E <= tau else 2 * mp.sqrt(tau * E) - tau
dt = float(sys.argv[1]); fl = {}
for k in (3, 4, 5, 6):
    d = json.load(open('edge_k%d.json' % k)); fl[k] = (d['eps_strong'], d['B_SA'])
if len(sys.argv) > 2: fl[6] = (float(sys.argv[2]), fl[6][1])
def kappa(m, ks, cN=805124):
    c = mp.mpf(cN) / SA
    ct = sum(mp.mpf(int(math.floor(fl[k][0] * (1 - dt) * SA))) / SA for k in ks)
    Bt = sum(mp.mpf(fl[k][1]) / SA for k in ks)
    A = c * (m - q) + 2 * ct; R = g(A); P = B * (m - q) + 2 * Bt
    return (H - P / m) / (1 - R / m)
for ks in ((), (6,), (5, 6), (4, 5, 6), (3, 4, 5, 6)):
    best = max((kappa(m, ks), m) for m in range(100, 260))
    k7 = mp.floor(best[0] * 10**7) / 10**7
    print('edge set %-12s best m %d: kappa %s  -> 7-digit target %s  (gain over no-edge best %s)'
          % (str(ks), best[1], mp.nstr(best[0], 12), mp.nstr(k7, 8), mp.nstr(best[0] - max(kappa(mm, ()) for mm in range(100, 260)), 4)))
# item 4: main certificate delta 0.005% -> 0.003%
eps = 805165.0008812845
for d in (0.00005, 0.00003):
    cN = int(math.floor(eps * (1 - d)))
    b0 = max((kappa(m, (), cN), m) for m in range(100, 260)); b1 = max((kappa(m, (4, 5, 6), cN), m) for m in range(100, 260))
    print('main delta %.3f%% (cN %d): no edge %s (m %d); with edge {4,5,6} %s (m %d)' % (100 * d, cN, mp.nstr(b0[0], 10), b0[1], mp.nstr(b1[0], 10), b1[1]))
