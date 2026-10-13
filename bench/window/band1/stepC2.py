"""C (corrected): find y_s where L_y(1) changes sign; verify L_y(n) < 0 for all n in 1..200 on y in (0, y_s); Psi(y) = int qf B^2 -
4 sum_n L_y(n)^+ on [y_s, 3]; size the certified cell check (N0 for the asymptotic tail, y-cell count from Lipschitz margins)."""
import sys, json, numpy as np
from scipy.optimize import brentq
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from dual import make_qf, window_from_cnum
qf = make_qf(window_from_cnum(json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum'], 24))
al = np.linspace(0, 1, 40001); wa = np.full(len(al), al[1]); wa[0] /= 2; wa[-1] /= 2; qa = qf(np.minimum(al, 0.999999)); qa[-1] = 0
qfp1 = (qf(np.array([0.999999]))[0] - qf(np.array([0.999]))[0]) / (0.999999 - 0.999)
def B(y): return 2 * (np.cosh(2 * np.pi * al * y) - 1)
def Ln(y, ns): return 2 * (np.cos(2 * np.pi * np.outer(ns, al)) @ (qa * B(y) * wa))
def SB2(y): return float(2 * np.sum(qa * B(y) ** 2 * wa))
ys_ = brentq(lambda y: Ln(y, np.array([1]))[0], 0.9, 1.4, xtol=1e-10)
print('y_s (L_y(1) = 0): %.6f' % ys_)
ns = np.arange(1, 401)
ygrid = np.concatenate([np.geomspace(1e-3, 0.1, 40), np.linspace(0.1, ys_ - 1e-4, 200)])
worst_scaled, N0max, cells = np.inf, 0, 0
for i, y in enumerate(ygrid):
    L = Ln(y, ns); assert np.all(L < 0), (y, ns[L >= 0][:5])
    lead = qfp1 * 2 * (np.cosh(2 * np.pi * y) - 1) / (2 * np.pi ** 2 * ns ** 2)
    rel = np.abs(L - lead) / np.abs(lead); N0 = int(ns[np.where(rel > 0.5)[0].max()] + 1) if np.any(rel > 0.5) else 1; N0max = max(N0max, N0)
    # Lipschitz in y of L/y^2 (scaled) to size y-cells: cell width ~ min_n |L|/sup_n |dL/dy|
    dB = 4 * np.pi * al * np.sinh(2 * np.pi * al * y); D = 2 * np.sum(qa * dB * wa)
    width = float(np.min(np.abs(L[:max(N0, 1)])) / D); worst_scaled = min(worst_scaled, width / y)
print('L_y(n) < 0 for n = 1..400 on %d y-points in (0, y_s): yes' % len(ygrid))
print('tail cutoff: leading asymptotic qf\'(1)B_y(1)/(2 pi^2 n^2) within 50%% for n >= N0, worst N0 = %d  (qf\'(1) = %.4f)' % (N0max, qfp1))
print('y-cell width needed (Lipschitz): >= %.3e * y  -> ~ log(y_s/y_min)/%.3e cells; with y_min = 1e-3: ~%d cells'
      % (worst_scaled, worst_scaled, int(np.log(ys_ / 1e-3) / worst_scaled) + 1))
print('Psi(y) = int qf B^2 - 4 sum_n L_y(n)^+ on [y_s, 3]:')
for y in np.concatenate([np.linspace(ys_, 1.6, 6), [2.0, 2.5, 3.0]]):
    L = Ln(y, np.arange(1, 2001)); psi = SB2(y) - 4 * np.sum(np.maximum(L, 0))
    print('  y=%.4f: Psi/int qf B^2 = %.5f  (positive L_y(n) at n = %s)' % (y, psi / SB2(y), list(np.arange(1, 2001)[L > 0][:6])))
