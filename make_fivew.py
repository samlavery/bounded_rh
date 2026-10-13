import sys, os
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
import gen_w, gen_data_N
Q = 4; SA = 10**8
npz = os.path.expanduser("~/work/helix_frobenius/tmp/att940_amtopa_n8/wq_Q4_B0.00320.npz")
pairs, A, Bv = gen_w.load_weights(npz, Q, da=10**6, db=10**8)
floor = 0.00559077
delta = float(sys.argv[1]) if len(sys.argv) > 1 else 0.01
c = Fr(int(floor * (1 - delta) * 10**8), 10**8)
info = gen_data_N.emit(Q, pairs, A, Bv, c, SA, "FiveW", CH=250, TABD=5)
open("fivew_params.txt", "w").write(f"{Q} {SA} {','.join(map(str, info['aN']))} {','.join(map(str, info['bN']))} {info['cN']} FiveW\n")
print("params:", open("fivew_params.txt").read())
