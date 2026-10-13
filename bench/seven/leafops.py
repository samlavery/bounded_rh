"""operation counts of the slope leaves of a walk chunk (decoded from data_<NAME>.lean)"""
import re, sys, json
sys.set_int_max_str_digits(0)
sys.path.insert(0, '.'); sys.path.insert(0, '../pyr')
from size7s import make_q, PAIRS, NP, Q
from pyr_table import Pyr
from w2cell import conv_ok, chain
NAME = sys.argv[1]; CH = sys.argv[2:]
d = open(f"../../data_{NAME}.lean").read()
regs = [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+), \[", d[d.index("def REG"):d.index("theorem hR")])]
def inreg(lo, hi): return any(a <= lo and hi <= b for a, b in regs)
dec = make_q(8)
PZ = Pyr(PE=5, PB=10, MAXA=4, FUEL=14); PD = Pyr(PE=6, PB=10, MAXA=4, FUEL=14)
def ngroups(X, lo, hi):
    cv = X.cover(lo, hi); return 0 if not cv else len(cv)
def nlb3(lo, hi):
    w = hi - lo
    if w < 1024: return ngroups(PZ, lo, hi), 1
    a = w >> 4
    return ngroups(PZ, lo, lo + a) + ngroups(PZ, lo + a, hi - a) + ngroups(PZ, hi - a, hi), 3
for m in re.finditer(r"theorem (wk\d+) : \S+ ([\d ]+) :=\n  \S+covered_of_walk lbS lbD ptS hR hbas (0x[0-9a-f]+|\d+) (\d+) ([\d ]+) (\d+)", d):
    name = m.group(1)
    if name not in CH: continue
    bits = int(m.group(3), 0); coords = [int(x) for x in m.group(5).split()]
    pos = 1; stack = [tuple((coords[2 * r], coords[2 * r + 1]) for r in range(Q))]
    tot = dict(S=0, exp=0, exp_reg=0, exp_der=0, dgroups=0, zo=0, zgroups=0, zreads=0, zg1=0); WD = [0] * 6
    while stack:
        box = stack.pop(); w = bits >> pos
        if w & 1:
            ax = (w >> 1) & 7; l, u = box[ax]; q = (l + u) >> 1
            A = list(box); A[ax] = (l, q); B = list(box); B[ax] = (q, u); pos += 4; stack += [tuple(B), tuple(A)]; continue
        kind = (w >> 1) & 3
        if box[Q - 1][1] < box[0][0] or kind != 1: pos += 3; continue
        modes = [((w >> (3 + 2 * r)) & 3) for r in range(Q)]
        fl = (w >> 15) & 1
        T = (1 << NP) - 1 if fl else (w >> 16) & ((1 << NP) - 1)
        pos += 16 if fl else 37
        q = [dec(modes[r], box[r][0], box[r][1]) for r in range(Q)]
        tot['S'] += 1
        for t, (i, j) in enumerate(PAIRS):
            lo = sum(box[k][0] for k in range(i, j)); hi = sum(box[k][1] for k in range(i, j)); qt = sum(q[i:j])
            if T >> t & 1:
                tot['exp'] += 1
                if inreg(lo, hi): tot['exp_reg'] += 1
                else:
                    tot['exp_der'] += 1
                    if hi > qt: tot['dgroups'] += ngroups(PD, qt, hi)
                    if qt > lo: tot['dgroups'] += ngroups(PD, lo, qt)
            else:
                tot['zo'] += 1; g, r_ = nlb3(lo, hi); tot['zgroups'] += g; tot['zreads'] += r_; WD[min(5, (hi - lo).bit_length() - 9) if hi - lo >= 256 else 0] += 1; tot['zg1'] += ngroups(PZ, lo, hi)
    print(name, {k: (round(v / tot['S'], 2) if k != 'S' else v) for k, v in tot.items()}, 'widths <256,512,1k,2k,4k,8k+:', WD)
