"""Deep single-pair regime, crude half-bin bound (no DP; any real D, masses <= 2, P_h and inter-bin T_g dropped):
  LP >= 2[K(2iy) - K(0)] + 2 sum_{j >= 0} b_j(y),  half bins H_j = [j/2, (j+1)/2) on each side of s,
  Phi_j = max_{u in H_j} ( -phi_y(u) - 4 g(u) )^+  (net gain per unit mass; phi_y = 4[Re K(u+iy) - K(u)]),
  b_j = -2 Phi_j if Phi_j <= 2a, else -a (1 + Phi_j/(2a))^2,  a = g(1/2)   (k >= 2 points in a half bin pay a (M^2 - sum m^2)).
Exploratory scan in y (fine grid sampling of u; not yet cell-certified)."""
import sys, numpy as np
sys.argv = ['crowd_dp.py', '128']
import crowd_dp as C
a = float(C.gfun(0.5)[0])
uu = np.arange(0, 64, 1 / 512); gu = C.gfun(uu); gu[0] = float(C.gfun(1e-9)[0])
xg, wg = np.polynomial.legendre.leggauss(1200); al = (xg + 1) / 2; wa = wg / 2; qa = C.qf(al)
def phi(u, y):
    B = np.cosh(2 * np.pi * al * y) - 1; out = np.empty(len(u))
    for i in range(0, len(u), 4000): out[i:i + 4000] = 8 * (np.cos(2 * np.pi * np.outer(u[i:i + 4000], al)) @ (qa * wa * B))
    return out
def bound(y):
    ph = phi(uu, y); net = np.maximum(-ph - 4 * gu, 0.0)
    nb = len(uu) // 256; Phi = net[:nb * 256].reshape(nb, 256).max(1)
    b = np.where(Phi <= 2 * a, -2 * Phi, -a * (1 + Phi / (2 * a)) ** 2)
    A2, A3 = C.Btail(y); jj = np.arange(128, 400000) / 2.0; tail = -2 * y ** 2 * np.sum(A2 / jj ** 2 + A3 / jj ** 3)
    selfterm = C.S0(y) * y ** 2
    return selfterm, 2 * (b.sum() + tail), Phi[:6]
for y in (0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.4, 1.7, 2.0, 2.5, 3.0, 4.0, 5.0):
    s, f, P = bound(y)
    print('y=%.2f: self 2[K(2iy)-K(0)] %.4e | half-bin field+cluster %+.4e | LP >= %+.4e (ratio %.3f) | Phi_0..5 %s' % (y, s, f, s + f, (s + f) / s, np.array2string(P, precision=3)), flush=True)
