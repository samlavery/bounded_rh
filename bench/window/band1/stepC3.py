"""C sizing (split design): (i) y <= 0.1: series L_y(n) = -y^2 K''(n) (1 + O(y^2)), no cells; (ii) y in [0.1, yc]: sign check with
Lipschitz cells for n < N0 plus the asymptotic tail; (iii) y >= yc: magnitude check int qf B^2 >= 4 sum_{n != 0} |L_y(n)|."""
import numpy as np
exec(open('stepC2.py').read().split("ys_ = brentq")[0])
for yc in (0.8, 0.9, 1.0):
    ns = np.arange(1, 401); yg = np.linspace(0.1, yc, 300); worst = np.inf
    for y in yg:
        L = Ln(y, ns); dB = 4 * np.pi * al * np.sinh(2 * np.pi * al * y); D = 2 * np.sum(qa * dB * wa)
        worst = min(worst, float(np.min(np.abs(L[:3])) / D))
    ncells = int(np.ceil((yc - 0.1) / worst))
    # magnitude regime
    ok, minratio = True, np.inf
    for y in np.linspace(yc, 6, 400):
        L = Ln(y, np.arange(1, 3001)); r = SB2(y) / (4 * 2 * np.sum(np.abs(L))); minratio = min(minratio, r)
    print('yc=%.1f: sign-check cells on [0.1, yc] (uniform width %.2e): %d cells x N0 = 3 terms (+ tail) | magnitude regime y in [yc, 6]: min int qfB^2 / (8 sum_{n>=1}|L|) = %.2f'
          % (yc, worst, ncells, minratio))
# small-y series regime: check the O(y^2) relative remainder at y = 0.1 for n = 1, 2
for n in (1, 2, 3):
    y = 0.1; L = Ln(y, np.array([n]))[0]; Kpp = 2 * np.sum(qa * (-(2 * np.pi * al) ** 2) * np.cos(2 * np.pi * al * n) * wa)
    print('series check y=0.1, n=%d: L/(-y^2 K\'\') = %.4f' % (n, L / (-y ** 2 * Kpp)))
