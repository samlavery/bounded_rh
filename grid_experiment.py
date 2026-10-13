"""Count leaves and distinct cells when term ranges are rounded outward to a grid of 1/2^g before lookup."""
import sys, os, itertools, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
import gen_w
import three_point_gen as G
g = int(sys.argv[1]); Q = 5
npz = os.path.expanduser("~/work/helix_frobenius/tmp/att940_amtopa_n8/wq_Q5_B0.00180.npz")
pairs, A, Bv = gen_w.load_weights(npz, Q)
c = Fr(347539, 10**8)
step = Fr(1, 2**g)
orig_Wmulti = G.Wmulti
cells_used = set()
def Wmulti_grid(lo, hi):
    lo2 = (lo // step) * step; hi2 = -((-hi) // step) * step
    pcs = G.quarter_pieces(lo2, hi2)
    for pc in pcs: cells_used.add(pc)
    return min(G.W_of(*pc)[0] for pc in pcs)
G.Wmulti = Wmulti_grid
t = time.time()
ok, leaves, covers = gen_w.size(Q, pairs, A, Bv, c, max_leaves=2*10**6, verbose=False)
print(f"grid 2^-{g}: ok={ok} leaves={leaves} distinct cells={len(cells_used)} ({time.time()-t:.0f}s)", flush=True)
