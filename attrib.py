import re, sys
from collections import defaultdict
log = open(sys.argv[1], encoding="utf-8").read().split("\n")
src = open(sys.argv[2], encoding="utf-8").read().split("\n")
vals = [int(l) for l in log if re.match(r"^\d{6,}$", l)]
pos = [i for i, l in enumerate(src) if l.strip() == "#eval IO.monoMsNow"]
def decl_after(i):
    for l in src[i+1:i+4]:
        m = re.match(r"(?:noncomputable )?(theorem|def)\s+(\w+)", l)
        if m: return m.group(2)
    return "?"
rows = [(decl_after(pos[i]), (vals[i+1]-vals[i])/1000) for i in range(min(len(vals), len(pos))-1)]
agg = defaultdict(lambda: [0, 0.0])
for n, t in rows:
    k = re.sub(r"\d+", "N", n); agg[k][0] += 1; agg[k][1] += t
print(f"stamps {len(vals)}/{len(pos)}; stamped total {sum(t for _, t in rows):.1f} s")
print(f"{'kind':12s} {'count':>6s} {'total s':>9s} {'mean ms':>9s}")
for k, (c, t) in sorted(agg.items(), key=lambda kv: -kv[1][1])[:8]:
    print(f"{k:12s} {c:6d} {t:9.1f} {1000*t/c:9.1f}")
