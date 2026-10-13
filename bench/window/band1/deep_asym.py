"""Deep single-pair regime, y >= Y: analytic version of the half-bin bound (deep_cert.py) with explicit constants.
With beta = 2 pi y, E = e^beta, alpha0 = 1/2, kap1 = |qf'(1)|, kap2 = sup_[1/2,1]|qf''|/2, qbar = sup qf, Q0 = int_0^1 qf:
  (a) |phi_y(u)| <= Lam <= 4 I(beta),  I(beta) = int qf e^{beta a} <= E (kap1/beta^2 + 2 kap2/beta^3) + qbar E^{1/2}/beta;
  (b) |phi_y(u)| <= T(u) = E (tau2/u^2 + tau3/u^3)   (three integrations by parts, p = qf (cosh(beta a) - 1), p(1) = p'(0) = 0),
      tau2 = kap1/pi^2,  tau3 = 8 (|qf''(1)|/2 + kap1 beta + J3)/(2 pi)^3,  int|p'''| <= E J3;
  (c) self = 4 int qf (cosh(2 beta a) - 1) >= (E^2/y^2) s0  for y >= Y  (s0 = the bracket below at y = Y, each correction decreasing);
  (d) per side sum_j |b_j| <= 2 sum Phi_j + sum Phi_j^2/(4a), Phi_j <= min(Lam, T(j/2)); bins j < 2V use Lam, j >= 2V use T,
      V = y:  sum Phi <= (2V+1) Lam + T(V) + 2 int_V^inf T,  sum Phi^2 <= (2V+1) Lam^2 + T(V)^2 + 2 int_V^inf T^2.
  LP >= self - 4 sum Phi - sum Phi^2/(2a) > 0  iff  R(y) < 1;  R(y) y^{-2}... is bounded by a positive sum of monomials
  C y^k e^{-n pi y}; each is checked decreasing on [Y, inf) (k <= 0, or n > 0 and Y >= k/(n pi)), so R(y) <= R_bound(Y) for all y >= Y.
Constants of qf by finite differences on its closed form, x 1.05 (same standard as the tail constants of crowd_dp.py).
usage: python3 deep_asym.py Y [CV]   (V = CV * y)"""
import sys, json, math, numpy as np
from collections import defaultdict
Y = float(sys.argv[1]); CV = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
from fractions import Fraction
cj = json.load(open('cert_R8_backed.json')); yk = np.array([float(Fraction(v)) for v in cj['knots_rational']]); Dk = 1 / 32
def gfun(u):
    th = 2 * np.pi * Dk * u; C = yk[0] + 2 * float(np.cos(th * np.arange(1, 96)) @ yk[1:]); return Dk * np.sinc(Dk * u) ** 2 * C
a = gfun(0.5) * (1 - 1e-9)
SF = 1.05
al = np.linspace(0, 1, 200001); h = al[1]; q = qf(np.minimum(al, 1 - 1e-13)); q[-1] = 0.0
d1 = np.gradient(q, h, edge_order=2); d2 = np.gradient(d1, h, edge_order=2); d3 = np.gradient(d2, h, edge_order=2)
hi_ = al >= 0.5
kap1 = SF * abs(d1[-1]); kap2 = SF * np.max(np.abs(d2[hi_])) / 2; qbar = SF * q.max(); Q0 = SF * np.trapezoid(q, al)
qpp1 = SF * abs(d2[-1]); s1p, s2p, s3p = (SF * np.max(np.abs(d[hi_])) for d in (d1, d2, d3)); s1, s2, s3 = (SF * np.max(np.abs(d)) for d in (d1, d2, d3))
# check the Taylor envelope used for I(beta) and the lower bound: |qf - kap1 (1-a)| <= kap2 (1-a)^2 on [1/2, 1]
env = np.max(np.abs(q[hi_] - kap1 / SF * (1 - al[hi_])) / np.maximum((1 - al[hi_]) ** 2, 1e-300)) if True else 0
print('constants: g(1/2) %.6f kap1 %.5f kap2 %.5f qbar %.5f Q0 %.5f |qf\'\'(1)| %.5f s\'1..3 %.4f %.4f %.4f s1..3 %.4f %.4f %.4f; Taylor envelope ratio %.4f <= kap2 %.4f'
      % (a, kap1, kap2, qbar, Q0, qpp1, s1p, s2p, s3p, s1, s2, s3, env, kap2), flush=True)
assert env <= kap2
# term algebra: dict (k, n) -> coeff, meaning coeff * y^k * e^{-n pi y}  (all coefficients >= 0)
def T_(d): return defaultdict(float, d)
def add(*ps):
    out = defaultdict(float)
    for p in ps:
        for key, c in p.items(): out[key] += c
    return out
def mul(p, r):
    out = defaultdict(float)
    for (k1, n1), c1 in p.items():
        for (k2, n2), c2 in r.items(): out[(k1 + k2, n1 + n2)] += c1 * c2
    return out
def sc(p, s): return defaultdict(float, {k: c * s for k, c in p.items()})
tp = 2 * math.pi
# all quantities below are divided by the appropriate power of E: Lam/E, T/E (functions of y)
lam = T_({(-2, 0): 4 * kap1 / tp ** 2, (-3, 0): 8 * kap2 / tp ** 3, (-1, 1): 4 * qbar / tp})          # Lam/E   (E^{1/2}/E = e^{-pi y})
J3 = T_({(-1, 0): 0.5 * s3p / tp, (0, 0): 0.5 * 3 * s2p + kap2, (1, 0): 0.5 * 3 * tp * s1p + 0.5 * kap1 * tp,
         (-1, 1): 0.5 * s3 / tp, (0, 1): 0.5 * 3 * s2, (1, 1): 0.5 * 3 * tp * s1, (2, 1): 0.5 * qbar * tp ** 2})
tau2 = T_({(0, 0): kap1 / math.pi ** 2})
tau3 = sc(add(T_({(0, 0): qpp1 / 2, (1, 0): kap1 * tp}), J3), 8 / tp ** 3)
yinv = lambda k: T_({(k, 0): 1.0})
TV = add(sc(mul(tau2, yinv(-2)), CV ** -2), sc(mul(tau3, yinv(-3)), CV ** -3))                # T(V)/E at V = CV y
intT = add(sc(mul(tau2, yinv(-1)), CV ** -1), sc(mul(tau3, yinv(-2)), 0.5 * CV ** -2))    # int_V^inf T / E
intT2 = add(sc(mul(tau2, mul(tau2, yinv(-3))), CV ** -3 / 3), sc(mul(tau2, mul(tau3, yinv(-4))), CV ** -4), sc(mul(tau3, mul(tau3, yinv(-5))), CV ** -5 / 5))
nb = T_({(1, 0): 2.0 * CV, (0, 0): 1.0})                                              # 2V + 1 bins
SPhi_E = add(mul(nb, lam), TV, sc(intT, 2))                                          # sum Phi / E
SPhi2_E2 = add(mul(nb, mul(lam, lam)), mul(TV, TV), sc(intT2, 2))                   # sum Phi^2 / E^2
# numerator / E^2 = 4 sum Phi / E^2 + sum Phi^2/(2a E^2); 4 sum Phi / E^2 = 4 (sum Phi / E) e^{-2 pi y}
num = add(sc(mul(SPhi_E, T_({(0, 2): 1.0})), 4), sc(SPhi2_E2, 1 / (2 * a)))
# self lower bound: self >= (E^2 / y^2) * s(y), s(y) = 2 kap1/(4pi)^2 - 4 kap2/((4pi)^3 y) - 2 kap1 (1 + 4 pi y) e^{-2 pi y}/(4pi)^2 - 4 Q0 y^2 e^{-4 pi y}
kap1_lo = abs(d1[-1]) / SF       # deflated: the lower bound of self needs a LOWER bound of |qf'(1)|
def s_of(yv): return 2 * kap1_lo / (4 * math.pi) ** 2 - 4 * kap2 / ((4 * math.pi) ** 3 * yv) - 2 * kap1_lo * (1 + 4 * math.pi * yv) * math.exp(-2 * math.pi * yv) / (4 * math.pi) ** 2 - 4 * Q0 * yv ** 2 * math.exp(-4 * math.pi * yv)
# the subtracted corrections in s are decreasing in y for y >= Y (checked below), so s(y) >= s(Y) =: s0 on [Y, inf)
s0 = s_of(Y)
for yv in np.linspace(Y, Y + 50, 2001): assert s_of(yv) >= s0 - 1e-15
Rterms = mul(num, yinv(2))                                                            # R(y) <= (y^2 num)/s0
bad = [(k, n) for (k, n), c in Rterms.items() if c > 0 and not (k <= 0 or (n > 0 and Y >= k / (n * math.pi)))]
assert not bad, 'non-decreasing terms: %s' % bad
Rb = sum(c * Y ** k * math.exp(-n * math.pi * Y) for (k, n), c in Rterms.items()) / s0
lead = sorted(((c * Y ** k * math.exp(-n * math.pi * Y) / s0, k, n) for (k, n), c in Rterms.items()), reverse=True)[:5]
print('Y = %g, V = %.2f y: s0 = %.6e ; R_bound(Y) = %.4f  (R(y) <= R_bound(Y) for all y >= Y, every term decreasing)' % (Y, CV, s0, Rb), flush=True)
print('  largest terms (value at Y, power of y, multiple of pi y in the exponent): %s' % ', '.join('%.4f (y^%d e^-%d pi y)' % t for t in lead), flush=True)
print('  => LP >= self (1 - R) >= %.3f self > 0 for every y >= %g' % (1 - Rb, Y) if Rb < 1 else '  => NOT closed at this Y', flush=True)
