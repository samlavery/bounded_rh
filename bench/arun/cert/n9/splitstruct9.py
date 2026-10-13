#!/usr/bin/env python3
"""splitstruct9.py DUMP.pkl CAP [PEEL]: for every root with more than CAP leaves, the split structure walkCut needs:
the peel chain from the root (larger child kept while the smaller child has < PEEL leaves, default 32), then the first real
split (both children >= PEEL) with its children's sizes and walk-bit spans; recursing into any child still above CAP."""
import pickle, sys
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/eight/am8"); sys.path.insert(0, ".")
d = pickle.load(open(sys.argv[1], "rb")); CAP = int(sys.argv[2]); PEEL = int(sys.argv[3]) if len(sys.argv) > 3 else 32
def nl(nd): return 1 if nd[0] != 'split' else nl(nd[4]) + nl(nd[5])
def show(nd, path, ind):
    chain = []
    while nd[0] == 'split':
        a, b = nl(nd[4]), nl(nd[5])
        if min(a, b) >= PEEL: break
        chain.append((a, b, nd[3])); nd = nd[4] if a >= b else nd[5]; path += "A" if a >= b else "B"
    if nd[0] != 'split': print(f"{ind}leaf after {len(chain)} peels"); return
    a, b = nl(nd[4]), nl(nd[5])
    print(f"{ind}peel chain {len(chain)} (peeled {sum(min(x[0], x[1]) for x in chain)} leaves); real split at path {path or '-'} "
          f"axis {nd[3]}: A {a} | B {b}")
    for c, tag in ((nd[4], "A"), (nd[5], "B")):
        if nl(c) > CAP: print(f"{ind}  {tag} ({nl(c)}) still > {CAP}:"); show(c, path + tag, ind + "    ")
for n, t in enumerate(d["trees"]):
    if nl(t) > CAP:
        print(f"root {n}: {nl(t)} leaves"); show(t, "", "  ")
