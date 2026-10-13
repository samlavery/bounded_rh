"""Shared objects for the step-9(e) cluster study (bridge-port).
q = qf of the R8 window (two-sided, int_{-1}^{1} q = 1); B_y(a) = 2 cosh(2 pi a y) - 2; continuum alpha grid on [0, 1].
||F||^2 := int_{-1}^{1} q |F|^2 = 2 int_0^1 q |F|^2 for F with |F(-a)| = |F(a)| (real positions, even weights).
The backed R8 certificate g (for T_g) is read from band1/cert_R8_backed.json as in band1/lemmaP.py."""
import sys, json, numpy as np
from fractions import Fraction
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
B1 = '/Users/samuellavery/work/riemann-submission/bench/window/band1/'
_c = window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24)
qfun = make_qf(_c)
NA = 6001
al = np.linspace(0.0, 1.0, NA)
wa = np.full(NA, al[1]); wa[0] /= 2; wa[-1] /= 2            # trapezoid weights on [0, 1]
qa = qfun(np.minimum(al, 0.9999999)); qa[-1] = 0.0
W2 = 2 * qa * wa                                              # two-sided weight: ||F||^2 = sum W2 |F|^2

def B(y):
    return 2 * np.cosh(2 * np.pi * al * y) - 2

# certificate g (backed R8)
_cj = json.load(open(B1 + 'cert_R8_backed.json'))
yk = np.array([float(Fraction(v)) for v in _cj['knots_rational']]); Dk = 1 / 32; nb = len(yk)
g0 = Dk * (yk[0] + 2 * yk[1:].sum()); gh0 = yk[0]
def g_of(u):
    u = np.atleast_1d(np.asarray(u, float)); out = np.empty(len(u))
    z = np.abs(u) < 1e-9
    th = 2 * np.pi * Dk * u[~z]
    C = yk[0] + 2 * (np.cos(np.outer(th, np.arange(1, nb))) @ yk[1:])
    out[~z] = Dk * (np.sinc(Dk * u[~z])) ** 2 * C
    out[z] = g0
    return out

def K_of(u):
    """pair kernel K(u) = int q cos(2 pi a u) (two-sided)"""
    u = np.atleast_1d(np.asarray(u, float))
    return np.cos(2 * np.pi * np.outer(u, al)) @ W2

def L_of(u, y):
    """field L_y(u) = int q B_y cos(2 pi a u) (two-sided)"""
    u = np.atleast_1d(np.asarray(u, float))
    return np.cos(2 * np.pi * np.outer(u, al)) @ (W2 * B(y))

def normB(y):
    return float(np.sqrt(W2 @ B(y) ** 2))
