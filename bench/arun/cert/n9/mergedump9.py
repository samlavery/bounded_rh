#!/usr/bin/env python3
"""mergedump9.py OUT.pkl N DUMP1:i,j,k-l ... (bridge-port, 2026-10-11): merge sizing dumps whose trees are given roots of
one N-root product (root sizing is per-root deterministic: a root sized alone equals the same root in a full run) into one
dump with trees in product order, for emit9qr.py's REPLAY (which checks every root cell against the covers).
Each argument maps a dump's trees, in its own order, to product indices (a-b ranges allowed)."""
import pickle, sys
out, N = sys.argv[1], int(sys.argv[2])
trees = [None] * N; leaves = []
for arg in sys.argv[3:]:
    p, spec = arg.rsplit(":", 1)
    idx = []
    for s in spec.split(","):
        a, _, b = s.partition("-"); idx += list(range(int(a), int(b) + 1)) if b else [int(a)]
    d = pickle.load(open(p, "rb"))
    assert len(d["trees"]) == len(idx), (p, len(d["trees"]), len(idx))
    for t, i in zip(d["trees"], idx):
        assert trees[i] is None, ("index twice", i); trees[i] = t
    leaves += d["leaves"]
miss = [i for i, t in enumerate(trees) if t is None]
assert not miss, ("missing roots", miss)
pickle.dump(dict(leaves=leaves, trees=trees, nroots=N), open(out, "wb"))
def nl(nd): return 1 if nd[0] != 'split' else nl(nd[4]) + nl(nd[5])
print(f"{out}: {N} roots, {sum(nl(t) for t in trees)} leaves; largest {max(nl(t) for t in trees)}")
