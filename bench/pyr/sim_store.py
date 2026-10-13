import collections
exec(open("sim_reads.py").read().split("for e in (4, 5):")[0])
qs = set()
for b in leaves:
    for t in terms(b): qs.add(t)
for e in (4, 5):
    cov = cov_pyr(e)
    cells = set()
    for (lo, hi) in qs: cells.update(cov(lo, hi))
    lv = collections.Counter(k for k, i in cells)
    print(f"e={e}: cells read by level {sorted(lv.items())}")
    for B in (10, 11, 12, 13):
        # dense blocks at level B (block j = cells of size 2^B); finest level r_j = min level read in the block
        fin = {}
        for k, i in cells:
            if k > B: continue
            j = i >> (B - k)
            fin[j] = min(fin.get(j, B), k)
        nfin = sum(1 << (B - r) for r in fin.values())
        ntot = sum((1 << (B - r + 1)) - 1 for r in fin.values())
        print(f"   B={B} ({(1<<B)/32768:.4f} unit): blocks {len(fin)}  finest cells {nfin}  stored entries {ntot}")
