"""Report for the n = 8 B-scan: per weights file, the exact-fraction ceiling at H floor 67216841/10^8, cN, sum b,
ratio (cN - 0.8 sum b)/cN and mvt-engine's volume proxy (cN - 0.8 sum b)^7/(7! prod b)/2 (MT8 = 84).
usage: python3 bscan8.py DELTA FILE..."""
import sys, json, math
from fractions import Fraction as Fr
H = Fr(67216841, 10**8); n = 8; q = n - 1; SA = 10**8
delta = float(sys.argv[1])
print('%-24s %8s %8s %8s %7s %8s %6s %4s %11s' % ('file', 'eps', 'cN', 'sumb', 'ratio', 'vol', 'xMT8', 'm', 'Phi'))
for f in sys.argv[2:]:
    r = json.load(open(f)); b = [Fr(x, SA) for x in r['bN']]; B = sum(b)
    cN = int(math.floor(r['eps_strong'] * (1 - delta) * SA)); C = Fr(cN, SA)
    best = max(((H - B * Fr(m - q, m)) / (1 - C * Fr(m - q, m)), m) for m in range(2 * n, 2000) if C * (m - q) <= 1)
    s = float(sum(b)); c = cN / SA
    vol = (c - 0.8 * s) ** 7 / (math.factorial(7) * math.prod(float(x) for x in b)) / 2
    print('%-24s %8.6f %8d %8.6f %7.4f %8.1f %6.2f %4d %11.9f' % (f, r['eps_strong'], cN, s, (c - 0.8 * s) / c, vol, vol / 84,
                                                         best[1], float(best[0])))
