import sys, collections
sys.argv = sys.argv[:1]
import size_m
from size_m import run, Q, PAIRS
for JC in [int(a) for a in sys.stdin.read().split()]:
    r = run(354704, JC=JC, verbose=False)
    pts = r["PT"]
    blocks = collections.defaultdict(list)
    for x in pts: blocks[x >> 10].append(x)
    # per-block resolution: min trailing zeros of the points (capped at 10)
    def tz(x): return min(10, (x & -x).bit_length() - 1) if x else 10
    slots = sum(1 << (10 - min(tz(x) for x in xs)) for xs in blocks.values())
    print(f"JC={JC}: leaves {r['nleaves']} (Z {r['nZ']}, M {r['nM']}), points {len(pts)}, point blocks {len(blocks)}, dense slots {slots}", flush=True)
