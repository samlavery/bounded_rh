"""Distinct term queries (lo, hi) per sampled walk theorem (SixW7 bench sample), to read the kernel's whnf cache effect."""
import re, sys, os
sys.setrecursionlimit(100000); sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE, "..", "count_ops.py")).read().split("# SPANS order check")[0].replace('os.path.dirname(os.path.abspath(__file__))', repr(os.path.join(HERE, ".."))))
Q = set(); P = set()
_term = termWN
def termWN2(lo, hi):
    Q.add((lo, hi))
    for pc in piecesN(64, lo, hi): P.add(pc)
    return _term(lo, hi)
termWN = termWN2
names = "wk0 wk5 wk13 wk14 wk15 wk18 wk21 wk22 wk27 wk46".split()
tl = tq = tp = 0
for n in names:
    m = re.search(rf"theorem {n} : SixW7.walk table bits (\d+) (\d+) (bx\d+) = some (\d+)", sol)
    fuel, pos, b, end = int(m.group(1)), int(m.group(2)), m.group(3), int(m.group(4))
    for k in C: C[k] = 0
    Q.clear(); P.clear()
    r = walk(fuel, pos, bx[b])
    print(f"{n:6s} leaves={C['leaves']:5d} terms={C['terms']:6d} distinct_queries={len(Q):6d} distinct_pieces={len(P):5d} q/leaf={len(Q)/C['leaves']:.2f}")
    tl += C['leaves']; tq += len(Q); tp += len(P)
print(f"TOTAL leaves={tl} distinct_queries={tq} ({tq/tl:.2f}/leaf) distinct_pieces={tp}")
