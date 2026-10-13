"""Multi-pair shallow probe (periodic model, certificate v1): a block of P equal-depth pairs on consecutive sites (their
doubles are the pair centres), singles on the other sites, P vacancies placed as far as possible from the block (total mass N).
Reports LP_total = E(Z) - F_C(D(Z)) (two-sided) per pair, in units of y^2, at the lattice positions and after relaxing all
positions (L-BFGS), and the split slack / Delta_B."""
import sys, numpy as np
from scipy.optimize import minimize
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', 64"))
def config(P):
    cen = np.arange(P, dtype=float); far = (P // 2 + N // 2 + np.arange(P) - P // 2) % N
    rest = np.array([t for t in range(N) if t >= P and t not in set(far.astype(int))], float)
    return rest, cen
print('N = %d; LP_total per pair / y^2 (two-sided) for a block of P consecutive equal-depth pairs' % N, flush=True)
for y in (0.1, 0.2, 0.3, 0.4):
    row = []
    for P in (1, 2, 4, 8, 16):
        rest, cen = config(P); n1 = len(rest); z = np.concatenate([rest, cen]); yv = np.full(P, y)
        d, _ = d_and_grad(z, n1, 0, P, yv); W = d / N - N * (gN0 - gh0) / 2 - gN0 * P
        r = minimize(lambda zz: d_and_grad(zz, n1, 0, P, yv), z, jac=True, method='L-BFGS-B', options={'maxiter': 3000})
        Wr = r.fun / N - N * (gN0 - gh0) / 2 - gN0 * P
        xr = np.concatenate([r.x[:n1], r.x[n1:]]); mr = np.concatenate([np.ones(n1), np.full(P, 2.0)]); dD = d_real(xr, mr)
        sl = dD / N - N * (gN0 - gh0) / 2 - gN0 * P
        row.append('P=%2d: lattice %+.2f relaxed %+.2f (slack/pair %.3f)' % (P, 2 * W / P / y ** 2, 2 * Wr / P / y ** 2, 2 * sl / P))
    print('  y=%.1f | %s' % (y, ' | '.join(row)), flush=True)
