import sys, os
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
import gen_w, gen_data_N
Q = int(sys.argv[1]); npz = os.path.expanduser(sys.argv[2]); floor = float(sys.argv[3]); delta = float(sys.argv[4]); NAME = sys.argv[5]
CH = int(sys.argv[6]) if len(sys.argv) > 6 else 250
SA = 10**8
pairs, A, Bv = gen_w.load_weights(npz, Q, da=10**6, db=10**8)
c = Fr(int(os.environ["CN"]), 10**8) if os.environ.get("CN") else Fr(int(floor * (1 - delta) * 10**8), 10**8)
info = gen_data_N.emit(Q, pairs, A, Bv, c, SA, NAME, CH=CH, TABD=5, out=f"data_{NAME}.lean")
open(f"{NAME}_params.txt", "w").write(f"{Q} {SA} {','.join(map(str, info['aN']))} {','.join(map(str, info['bN']))} {info['cN']} {NAME} 96 {os.environ.get('XFAR', '0')} {os.environ.get('FARG', '0')}\n")
print("params:", open(f"{NAME}_params.txt").read())
