"""Numerical facts about the AMTOPA 17-term window that size the Lean obligations (stage B/F of SCOPE.md)."""
import numpy as np, mpmath as mp
import sys; sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp/att940_amtopa_n8')
from famq import AMTOPA_C, frequencies, H_of, kernel
c = AMTOPA_C; w = frequencies(17)
s = np.linspace(0, 0.5, 2_000_001); h = s[1] - s[0]
v = (c[:, None] * np.cos(w[:, None] * s[None, :])).sum(0)
dv = -(c[:, None] * w[:, None] * np.sin(w[:, None] * s[None, :])).sum(0)
pv = np.clip(dv, 0, None).sum() * h
runs = np.sum(np.diff((dv > 0).astype(int)) == 1) + (dv[0] > 0)
print('v on [0,1/2]: min %.6f max %.6f v(0) %.6f v(1/2) %.6f' % (v.min(), v.max(), v[0], v[-1]))
print('positive variation PV(v) on [0,1/2] = %.6f over %d increasing runs' % (pv, runs))
print('sum_{j>=1}|c_j| = %.6f   sum |c_j| w_j = %.4f   sum |c_j| w_j^2 = %.3f' % (np.abs(c[1:]).sum(), (np.abs(c[1:]) * w[1:]).sum(), (np.abs(c[1:]) * w[1:] ** 2).sum()))
for M in (1.0083, 1.03, 1.0652):
    f0 = np.sqrt(v[0] / M); pvf = (np.clip(np.diff(np.sqrt(v / M)), 0, None)).sum()
    pv2 = (np.clip(np.diff(v / M), 0, None)).sum()
    a = 2 * np.trapezoid(v / M, s); b = 2 * np.trapezoid((v / M) ** 2, s)
    print('M=%.4f: TV(phi)/2 = f(0)+2PV(f) = %.5f   TV(phi^2)/2 = %.5f   a=%.4f b=%.4f   (need <=1, <=1, b>=1/2)' % (M, f0 + 2 * pvf, v[0] / M + 2 * pv2, a, b))
print('H(AMTOPA) = %.10f   H(MT) = %.10f' % (H_of(c, w), H_of(np.array([1.0]), np.array([np.sqrt(2)]))))
# kernel: K_v(x) = c0 K_MT(x) + (x sin(pi x)/pi) sum_j (-1)^j c_j/(x^2-j^2)
x = np.linspace(0.013, 19.97, 4001)
K = kernel(x, c, w)
j = np.arange(1, 17)
R = ((-1.0) ** j * c[1:] / (x[:, None] ** 2 - j[None, :] ** 2)).sum(1)
K2 = c[0] * kernel(x, np.array([1.0]), np.array([np.sqrt(2)])) + x * np.sin(np.pi * x) / np.pi * R
print('closed form K_v = c0 K_MT + x sin(pi x) R(x)/pi : max abs err %.2e' % np.abs(K - K2).max())
k0 = kernel(0.0, c, w)[0]
print('K_v(0) = %.10f = c0*sqrt2*sin(1/sqrt2) = %.10f' % (k0, c[0] * np.sqrt(2) * np.sin(1 / np.sqrt(2))))
km = kernel(x, np.array([1.0]), np.array([np.sqrt(2)])) / kernel(0.0, np.array([1.0]), np.array([np.sqrt(2)]))[0]
print('max |k_v - k_MT| on [0,20] = %.4f ; |k_v - k_MT| at x=1.04,1.97,2.91: %s' % (np.abs(K / k0 - km).max(), np.round(np.interp([1.04, 1.97, 2.91], x, K / k0 - km), 5)))
