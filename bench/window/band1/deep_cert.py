"""Deep single-pair regime: certified half-bin bound on y in [Y0, Y1] (certificate v1, line model, any real D, masses <= 2).
  LP(D, y) >= self(y) + 2 sum_{j >= 0} b_j,   self(y) = 2[K(2iy) - K(0)] = 4 int_0^1 qf (cosh(4 pi a y) - 1) da  (increasing),
  half bins H_j = [j/2, (j+1)/2) on each side of s;  per unit mass a point in H_j gains at most
  Phi_j = sup_{u in H_j} ( -phi_y(u) - 4 g(u) )^+,  phi_y(u) = 8 int_0^1 qf (cosh(2 pi a y) - 1) cos(2 pi a u) da;
  k >= 2 points in H_j (total mass M, masses <= 2) pay T_g >= g(1/2)(M^2 - sum m^2) >= g(1/2)(M^2 - 2M), so
  b_j = -2 Phi_j if Phi_j <= 2 g(1/2), else -g(1/2)(1 + Phi_j/(2 g(1/2)))^2.     (P_h and inter-bin T_g dropped.)
Cell bounds: phi on a (u, y) grid; on each rectangle max(-phi) <= max over the 4 corners + (M2 ETA^2 + Myy DY^2)/8 (bilinear
interpolation), M2 = 8 int qf (cosh - 1)(2 pi a)^2, Myy = 8 int qf (2 pi a)^2 cosh(2 pi a y_hi);
g from the certified block minima of crowd_dp.py.  Half bins with u >= U use |phi_y(u)| <= y^2 (A2/u^2 + A3/u^3).
usage: python3 deep_cert.py Y0 Y1 DY [U]"""
import os, sys, time, numpy as np
Y0, Y1, DY = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]); U = float(sys.argv[4]) if len(sys.argv) > 4 else 64.0
sys.argv = ['crowd_dp.py', '128', '8', '', '1e-8']
import crowd_dp as C
t0 = time.time()
a = float(C.gmin_range(np.array([0.0]), np.array([0.5]))[0])
xg, wg = np.polynomial.legendre.leggauss(1200); al = (xg + 1) / 2; wa = wg / 2; qa = C.qf(al)
xg2, wg2 = np.polynomial.legendre.leggauss(1600); al2 = (xg2 + 1) / 2; wa2 = wg2 / 2; qa2 = C.qf(al2)
ETA = 1 / 512; ug = np.arange(0, U + ETA / 2, ETA); nu = len(ug)
glo = C.gmin_range(ug[:-1], ug[1:])                       # certified lower bound of g on each u-cell
nper = int(round(0.5 / ETA)); nbins = (nu - 1) // nper
def ints(y):
    ch = np.cosh(2 * np.pi * al2 * y) - 1
    self_ = 4 * float(np.sum(qa2 * wa2 * (np.cosh(4 * np.pi * al2 * y) - 1)))
    M2 = 8 * float(np.sum(qa2 * wa2 * ch * (2 * np.pi * al2) ** 2))
    Dy = 8 * float(np.sum(qa2 * wa2 * 2 * np.pi * al2 * np.sinh(2 * np.pi * al2 * y)))
    return self_, M2, Dy
def b_of(Phi):
    return np.where(Phi <= 2 * a, -2 * Phi, -a * (1 + Phi / (2 * a)) ** 2)
# quadrature check at the largest y
for yc in (Y1,):
    uu = np.array([0.0, 0.8, 7.3, U]); B1 = np.cosh(2 * np.pi * al * yc) - 1; B2 = np.cosh(2 * np.pi * al2 * yc) - 1
    v1 = 8 * (np.cos(2 * np.pi * np.outer(uu, al)) @ (qa * wa * B1)); v2 = 8 * (np.cos(2 * np.pi * np.outer(uu, al2)) @ (qa2 * wa2 * B2))
    print('a = g(1/2) = %.6f; u-grid %d points to U = %g; quadrature check at y=%.2f: max rel diff (1200 vs 1600 nodes) %.2e'
          % (a, nu, U, yc, np.max(np.abs(v1 - v2)) / np.max(np.abs(v2))), flush=True)
yg = np.arange(Y0, Y1 + DY / 2, DY); ncell = len(yg) - 1
worst = (np.inf, None, None); BATCH = 64
def phi_cols(ys):
    V = (qa * wa)[:, None] * (np.cosh(2 * np.pi * np.outer(al, ys)) - 1); P = np.empty((nu, len(ys)))
    for r0 in range(0, nu, 4096): P[r0:r0 + 4096] = 8 * (np.cos(2 * np.pi * np.outer(ug[r0:r0 + 4096], al)) @ V)
    return P
prev = phi_cols(yg[:1])[:, 0]
for i0 in range(0, ncell, BATCH):
    cols = phi_cols(yg[i0 + 1:i0 + 1 + BATCH])
    for c in range(cols.shape[1]):
        k = i0 + c; ylo, yhi = yg[k], yg[k + 1]; cur = cols[:, c]
        self_lo = ints(ylo)[0]; _, M2, _ = ints(yhi)
        Myy = 8 * float(np.sum(qa2 * wa2 * (2 * np.pi * al2) ** 2 * np.cosh(2 * np.pi * al2 * yhi)))
        n1, n2 = -prev, -cur
        up = np.maximum(np.maximum(n1[:-1], n1[1:]), np.maximum(n2[:-1], n2[1:])) + (M2 * ETA ** 2 + Myy * (yhi - ylo) ** 2) / 8 - 4 * glo
        Phi = np.maximum(up[:nbins * nper].reshape(nbins, nper).max(1), 0.0)
        A2, A3 = C.Btail(yhi); jj = np.arange(2 * int(U), 2 * int(U) + 2000000) / 2.0
        Pt = yhi ** 2 * (A2 / jj ** 2 + A3 / jj ** 3); bt = float(np.sum(b_of(Pt))) - 2 * yhi ** 2 * 2 * (A2 / jj[-1] + A3 / jj[-1] ** 2)
        tot = self_lo + 2 * (float(np.sum(b_of(Phi))) + bt); ratio = tot / self_lo
        if ratio < worst[0]: worst = (ratio, (ylo, yhi), tot)
        if k % max(1, int(round(0.1 / DY))) == 0:
            print('  y in [%.4f, %.4f]: self %.4e | LP >= %+.4e | ratio to self %.4f  [%.0fs]' % (ylo, yhi, self_lo, tot, ratio, time.time() - t0), flush=True)
        prev = cur
print('CERTIFIED (half-bin bound) on [%.4f, %.4f], %d y-cells of width %g: min LP/self = %.4f at %s (LP >= %.4e); total %.0fs'
      % (Y0, yg[-1], ncell, DY, worst[0], worst[1], worst[2], time.time() - t0), flush=True)
