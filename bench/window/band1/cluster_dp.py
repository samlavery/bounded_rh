"""Multi-pair clusters by CONCAVITY of the environment response (certificate v1, line model).
For pairs p in a cluster (centres s_p, depths y_p), with all environment T_g allocated to the cluster:
  V(sum_p phi_p(. - s_p)) >= sum_p lam_p V(phi_p/lam_p; double at s_p) - sum_{p != q} 2 phi_p(s_q - s_p),   sum lam_p = 1,
because V(Phi) = min_c [<c, Phi> + T(c)] is concave in Phi, and a forced double at s_q in the environment of p is worth
-2 phi_p(s_q - s_p) at most.  The subtracted terms cancel the pair-on-double fields in the pair-pair part, so
  LP_C >= sum_p [ self_p + lam_p V(mu_p phi_p) ] + sum_{p<q} [ 2 X_pq + 8 g(d_pq) ],   mu_p = 1/lam_p,
and each bracket m(y, mu) = S0(y) + 2 V_side(mu psi_y)/mu (in units of y^2) is a single-pair DP with the field amplified by mu.
This script tabulates m(y, mu) with the localised-slack cluster DP of crowd_dp2.py (window LOC, cluster parts anywhere).
usage: python3 cluster_dp.py YLO YHI NY MU1,MU2,... [LOC] [P]"""
import sys, time, numpy as np
YLO, YHI, NY = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]); MUS = [float(v) for v in sys.argv[4].split(',')]
LOCv = sys.argv[5] if len(sys.argv) > 5 else '8'; PC = sys.argv[6] if len(sys.argv) > 6 else '32'
sys.argv = ['crowd_dp2.py', '0', '1', '1', PC, LOCv]
import crowd_dp2 as D2
C = D2.C
orig_one_body = C.one_body
def run(mu, ylo, yhi):
    C.one_body = lambda a, b: (lambda r: (mu * r[0], r[1]))(orig_one_body(a, b))
    try:
        s0, tx, V = D2.dp2(ylo, yhi)
    finally:
        C.one_body = orig_one_body
    return s0 + 2 * V / mu
if __name__ == '__main__':
    t0 = time.time(); yb = np.linspace(YLO, YHI, NY + 1)
    print('m(y, mu) = S0 + 2 V_side(mu psi)/mu (certified lower bound per pair, units y^2); slack window %s, cap %s' % (LOCv, PC), flush=True)
    print('  y-interval      ' + ' '.join('mu=%-7.3g' % m for m in MUS), flush=True)
    for ylo, yhi in zip(yb[:-1], yb[1:]):
        row = []
        for mu in MUS:
            try: row.append('%+9.4f' % run(mu, ylo, yhi))
            except AssertionError: row.append('   FAIL  ')
        print('  [%.4f,%.4f] %s  [%.0fs]' % (ylo, yhi, ' '.join(row), time.time() - t0), flush=True)
