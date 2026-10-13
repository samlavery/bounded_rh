import sys
WIN, DT = sys.argv[1], float(sys.argv[2]); AS = [float(a) for a in sys.argv[3].split(',')]
src = open('global_cert3.py').read().split("out = {}")[0]
sys.argv = [sys.argv[0], WIN, str(DT)]
exec(src)
for A in AS:
    g0, Tmin, exmax, rd, y = solve(A, 1 / 32)
    print('  exact LP A=%.2f Dk=1/32: g(0) %.6f -> delta\' %.6f = %.2f%% of delta_true  (min T %+.1e, max(g^-qf) %+.1e, %d refinements)'
          % (A, g0, g0 / 2, 100 * g0 / 2 / DT, Tmin, exmax, rd), flush=True)
