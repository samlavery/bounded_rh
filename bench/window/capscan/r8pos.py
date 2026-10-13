"""Where a fixed window sits under the obstruction: G(r) = H(f) - r(1 - Ef) for the paper mixture (lam(r) as in
txt:366-370), at r = 0.674034, and its root r_f (the obstruction value for this single window)."""
import sys, json
import mpmath as mp
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from capcore import *
from ceiling import PAPER
mp.mp.dps = 30
def window_G(r, c, pre):
    r = mp.mpf(r); lam = (1 / r - pre['da']) / (pre['db'] - pre['da'])
    Q = (1 - lam) * pre['QA'] + lam * pre['QB']
    z = mp.matrix([1] + c)
    H = 2 - (z.T * pre['Cm'] * z)[0, 0] / pre['A'] ** 2
    Ef = (z.T * Q * z)[0, 0] - 1
    return H - r * (1 - Ef), H, Ef
for name, f in (('R8 (rwin8.json, PC8SF window)', '/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'),
                ('R7 (rwin7.json)', '/Users/samuellavery/work/riemann-submission/bench/window/rwin7.json'),
                ('typh7 (rwin_typh7.json)', '/Users/samuellavery/work/riemann-submission/bench/window/rwin_typh7.json')):
    cn = json.load(open(f))['cnum']
    c = [mp.mpf(x) / 10**9 for x in cn[1:]] + [mp.mpf(0)] * (24 - 12)
    w = freqs(24, mp.sqrt(2)); A = Amass(mp.sqrt(2)); pre = prep(w, A, PAPER)
    g, H, Ef = window_G(mp.mpf(337017) / 500000, c, pre)
    a, b = mp.mpf('0.670'), mp.mpf('0.676')
    for _ in range(60):
        mid = (a + b) / 2
        if window_G(mid, c, pre)[0] >= 0: a = mid
        else: b = mid
    print('%-32s H %s  Ef %s  G(0.674034) %s  own root r_f %s' % (name, mp.nstr(H, 10), mp.nstr(Ef, 10), mp.nstr(g, 6), mp.nstr(a, 10)))
