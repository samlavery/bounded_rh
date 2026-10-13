import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
import gen_w
import three_point_gen as G
mode = sys.argv[1]; Q = 5
npz = os.path.expanduser("~/work/helix_frobenius/tmp/att940_amtopa_n8/wq_Q5_B0.00180.npz")
pairs, A, Bv = gen_w.load_weights(npz, Q)
floor = 0.003582881
if mode.startswith("pieces"):
    k = int(mode[6:])   # cut at multiples of 1/k
    def pieces_k(l, u):
        cuts = [l]; q = (l // Fr(1, k) + 1) * Fr(1, k)
        while q < u: cuts.append(q); q += Fr(1, k)
        cuts.append(u)
        return [(cuts[i], cuts[i+1]) for i in range(len(cuts)-1) if cuts[i] < cuts[i+1]]
    G.quarter_pieces = pieces_k
    G._cache.clear()
    def Wmulti(l, u): return min(G.W_of(*pc)[0] for pc in pieces_k(l, u))
    G.Wmulti = Wmulti
for delta in (0.02,):
    c = Fr(int(floor * (1 - delta) * 10**8), 10**8)
    print(f"[{mode}] delta={delta}", flush=True)
    gen_w.size(Q, pairs, A, Bv, c, max_leaves=10**6)
