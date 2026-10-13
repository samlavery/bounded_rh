"""Full verification (as winopt_verify.py) of 25-mode windows given by c: R8 and the smooth family fit."""
import sys, json, numpy as np
src = sys.argv[1:]
sys.argv = [sys.argv[0]]
code = open('winopt_verify.py').read()
exec(code.split("kc, dc, ic = verify('continuum LP window', qc)")[0])
res = {}
for name in src:
    cc = R8C if name == 'R8' else np.array(json.load(open(name))['c'])
    k_, d_, i_ = verify(name, lambda a, cc=cc: make_qf(cc)(np.atleast_1d(a)))
    res[name] = (k_, d_, i_)
    print('SHARPNESS %s: kappa %.7f, delta_true %.6f, int q a %.6f: to beat 0.6735 need %.4f%% of delta_true; to reach 0.676 %.4f%%'
          % (name, k_, d_, i_, 100 * i_ / (1 - 0.6735) / d_, 100 * i_ / (1 - 0.676) / d_), flush=True)
json.dump(res, open('winopt_verify2.json', 'w'), indent=1)
