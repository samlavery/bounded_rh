"""Pre-registered refutation check for the local-route stop-claim: truncated per-defect energy delta_R at R = 16, 24,
N = 256, from the dilated (delocalised-vacancy) start; prediction delta_R < 0.45 (best window; delta_true 0.484424)."""
import sys
sys.argv = ['local_route.py', 'winopt_smoothfit_single_N24.json', '0.154656']
src = open('local_route.py').read().split("tR = lambda R:")[0].replace("N = 64", "N = 256")
exec(src)
xl, ml = lattice()
for R in (16, 24):
    P0 = Phi(xl, ml, R)
    xs = np.arange(N - 1) * N / (N - 1.0); ms = np.ones(N - 1); ms[(N - 1) // 2] = 2.0
    r1 = minimize(lambda z: Phi(z, ms, R, grad=True), xs, jac=True, method='L-BFGS-B', options={'maxiter': 20000})
    xd, md = dipole_cfg([N // 2]); r2 = minimize(lambda z: Phi(z, md, R, grad=True), xd, jac=True, method='L-BFGS-B', options={'maxiter': 20000})
    print('N=%d R=%d: delta_R from dilated start %.6f (%.1f%% of delta_true) | from localized dipole %.6f | prediction < 0.45: %s'
          % (N, R, (r1.fun - P0) / 4, 100 * (r1.fun - P0) / 4 / 0.484424, (r2.fun - P0) / 4, 'HELD' if min(r1.fun, r2.fun) / 1 - P0 < 4 * 0.45 else 'REFUTED'), flush=True)
