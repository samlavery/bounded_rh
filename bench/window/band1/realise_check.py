"""(i) basin-vs-depth check at the free-depth 'drops': re-optimise positions of the free optimum with every depth set to 0;
(ii) continuum constants of the R8 window: int_0^1 qf, int_0^1 qf a, qf(0), the termwise (Montgomery-class) value at this
window, and the dilute-defect ceiling 1 - 2 (TGT/N^2)/(Delta_1/N).  usage: python3 realise_check.py N k t STARTS"""
import sys, numpy as np
from scipy.optimize import minimize
from scipy.integrate import quad
N, K, T, ST = map(int, sys.argv[1:5]); sys.argv = ['x', str(N), '0.5', str(ST)]
exec(open('realise.py').read().split("if __name__ == '__main__':")[0])
d0, z0 = dmin(K, T, 0.0, ST, yfix=0.0)
dF, zF = dmin(K, T, 0.5, ST, seeds=[z0] * 3)
n1 = N - 2 * K - 3 * T; n = n1 + K + T
r = minimize(lambda x: (lambda dg: (dg[0], dg[1][:n]))(datum(np.concatenate([x, np.zeros(K)]), n1, K, T)), zF[:n], jac=True, method='L-BFGS-B')
print('N=%d type (k=%d,t=%d): d_min y=0 multistart %.4f | free-depth best %.4f (depths %s) | free positions re-optimised at y=0: %.4f'
      % (N, K, T, d0, dF, np.round(zF[n:], 4), r.fun))
qf = make_qf(c); I0 = quad(qf, 0, 1, limit=200)[0]; I1 = quad(lambda a: qf(a) * a, 0, 1, limit=200)[0]
print('R8 window: qf(0) %.6f  int_0^1 qf %.6f  int_0^1 qf a %.6f | termwise (Montgomery-class) simple fraction at this window: %.6f'
      % (qf(0.0), I0, I1, 2 - (qf(0.0) + 2 * I1) / (2 * I0)))
d1, _ = dmin(1, 0, 0.0, ST, yfix=0.0)
print('  Delta_1/N %.6f, TGT/N^2 %.6f, dilute-defect value 1 - 2 (TGT/N^2)/(Delta_1/N) = %.6f; continuum TGT/N^2 -> %.6f'
      % (d1 / N, TGT / N ** 2, 1 - 2 * (TGT / N ** 2) / (d1 / N), I1))
