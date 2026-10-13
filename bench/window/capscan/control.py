"""Positive control: reproduce Gebendorfer Prop. 6.1 (txt:408-426): at r = 337017/500000 with configurations A, B
(txt:362-364) and lam = 11051/112339 (txt:366-369), max_c [H - r(1 - Ef)] = -0.00000092349008875104269... (txt:425)."""
import sys, time
import mpmath as mp
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from capcore import *

mp.mp.dps = 50
t0 = time.time()
w0 = mp.sqrt(2); K = 24
w = freqs(K, w0); A = Amass(w0)
a0 = w0 / 2
print('A =', mp.nstr(A, 20), ' sin(a0)/a0 =', mp.nstr(mp.sin(a0) / a0, 20))
Cm = Cmat(w)
# check (5): H = 2 - z^t Cm z / A^2 against H0 - c^t D c, for a random c
H0 = mp.mpf(3) / 2 - a0 * mp.cot(a0)
import random
random.seed(1)
c = [mp.mpf(random.uniform(-0.02, 0.02)) for _ in range(K)]
z = mp.matrix([1] + c)
Hq = 2 - (z.T * Cm * z)[0, 0] / A ** 2
Hd = H0 - sum(c[j - 1] ** 2 * (1 - 1 / (2 * j ** 2 * mp.pi ** 2)) / (2 * A ** 2) for j in range(1, K + 1))
print('H via C(f): %s   via (5): %s   diff %s' % (mp.nstr(Hq, 20), mp.nstr(Hd, 20), mp.nstr(Hq - Hd, 3)))
r = mp.mpf(337017) / 500000
confs = [(2, 3, [mp.mpf(5189) / 5000, mp.mpf(9811) / 5000]),
         (3, 4, [mp.mpf(10289) / 10000, mp.mpf(10289) / 10000, mp.mpf(9711) / 5000])]
val, lam, cstar, P11 = obstruction(r, w, A, confs, Cm=Cm, ret_c=True)
print('lam =', mp.nstr(lam, 20), ' 11051/112339 =', mp.nstr(mp.mpf(11051) / 112339, 20))
print('P11 positive definite:', min(mp.eig(P11, left=False, right=False)).real > 0 if False else 'chol', end=' ')
try:
    mp.cholesky(P11); print('ok')
except Exception as e:
    print('FAILED', e)
print('max_c [H - r(1-Ef)] at r = 337017/500000:', mp.nstr(val, 25))
print('paper (txt:425):                           -0.0000009234900887510426958262744573708873')
print('(%.0fs)' % (time.time() - t0))
