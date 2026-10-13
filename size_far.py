import sys, os; sys.set_int_max_str_digits(0); sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
from fractions import Fraction as Fr
import gen_w
pairs, A, Bv = gen_w.load_weights(os.path.expanduser(sys.argv[1]), 5)
print(f"RULE={gen_w.RULE} WFRAC={gen_w.WFRAC} HALF={gen_w.HALF} XFAR={gen_w.XFAR} FARG={gen_w.FARG}", flush=True)
gen_w.size(5, pairs, A, Bv, Fr(int(sys.argv[2]), 10**8), max_leaves=3*10**6)
