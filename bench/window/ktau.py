"""kappa_tau for an n-point weights file (AMTOPA band profile, tau = n/(n-1)):
  kappa_tau = max_m (m H - B (m - q)) / (m - R(c (m - q))),  q = n - 1,
  R(A) = A (A <= tau),  (A + m (2 sqrt(A/tau) - 1)) / (1 + m/tau)  (A > tau);
H = the file's H floored at 1e-10 (or --H NUM/DEN), c = floor(eps_strong (1 - delta) 1e8)/1e8.  mpmath at 50 digits.
usage: python3 ktau.py [--H NUM/DEN] FILE..."""
import sys, json, math
import mpmath as mp
from decimal import Decimal
mp.mp.dps = 50
args = sys.argv[1:]; Hover = None
LIN = '--lin' in args; args = [a for a in args if a != '--lin']   # linear branch only (c(m-q) <= tau)
if args and args[0] == '--H': Hover = args[1]; args = args[2:]
def ktau(H, B, c, n, mmax=4000):
    q = n - 1; tau = mp.mpf(n) / q; best = (mp.mpf(-1), 0, '')
    for m in range(2 * n, mmax):
        A = c * (m - q)
        if A <= tau: R = A; br = 'lin'
        elif LIN: continue
        else: R = (A + m * (2 * mp.sqrt(A / tau) - 1)) / (1 + m / tau); br = 'sqrt'
        den = m - R
        if den <= 0: continue
        k = (m * H - B * (m - q)) / den
        if k > best[0]: best = (k, m, br)
    return best
for f in args:
    r = json.load(open(f)); n = r['n']
    if Hover: a, b = Hover.split('/'); H = mp.mpf(int(a)) / int(b)
    else: H = mp.mpf(int(Decimal(r['H']) * 10**10)) / 10**10
    B = mp.mpf(sum(r['bN'])) / 10**8
    out = []
    for d in (0, 0.0005, 0.001):
        cN = int(r['eps_strong'] * (1 - d) * 1e8); k, m, br = ktau(H, B, mp.mpf(cN) / 10**8, n)
        out.append('%s(m%d %s)' % (mp.nstr(k, 10), m, br))
    print('%-26s n %d B %.6f eps %.9f H %s | %s' % (f, n, float(B), r['eps_strong'], mp.nstr(H, 10), '  '.join(out)))
