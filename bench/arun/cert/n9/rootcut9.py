"""leaf distribution of the QZ32 tree along each gap axis: for a cover-level cut m on gap a (applied to every root
whose interval on a contains m), the leaves below / above / straddling, per root"""
import pickle, sys
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/eight/am8"); sys.path.insert(0, ".")
d = pickle.load(open(sys.argv[1] if len(sys.argv) > 1 else "dump_full_t570_qz32.pkl", "rb"))
Q = 8
def leaves(nd, out):
    if nd[0] == 'split': leaves(nd[4], out); leaves(nd[5], out)
    else: out.append(nd[1])
R = []
for t in d["trees"]:
    o = []; leaves(t, o); R.append((t[1], o))
print("roots", [len(o) for _, o in R])
def scan(a, cuts):
    best = []
    for m in cuts:
        rows = []
        for (box, o) in R:
            l, u = box[a]
            if not (l < m < u): rows.append((len(o), 0, 0)); continue
            b = sum(1 for c in o if c[a][1] <= m); ab = sum(1 for c in o if c[a][0] >= m)
            rows.append((b, ab, len(o) - b - ab))
        mx = max(max(x[0] + x[2], x[1] + x[2]) for x in rows); st = sum(x[2] for x in rows)
        nroots = sum(2 if (x[1] + x[2]) and (x[0] + x[2]) else 1 for x in rows)
        best.append((mx, st, m, nroots, rows))
    return sorted(best)[:3]
for a in range(Q):
    lo = min(box[a][0] for box, _ in R); hi = max(box[a][1] for box, _ in R)
    cuts = sorted({c[a][0] for _, o in R for c in o} | {c[a][1] for _, o in R for c in o})
    cuts = [m for m in cuts if lo < m < hi]
    for mx, st, m, nr, rows in scan(a, cuts):
        print(f"gap {a}: cut {m} ({m / 32768:.4f})  max side {mx}  straddle {st}  roots {nr}  big: " +
              " ".join(f"r{i}:{rows[i][0]}/{rows[i][1]}/{rows[i][2]}" for i in (9, 5, 10, 4, 2, 6)))

# ---- per-root cuts (one boundary per root): any gap or pair-sum axis, the cut chosen per root
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
def rng(c, cons, key):
    if key[0] == 'g': return c[key[1]]
    t = key[1]
    if t in cons: return cons[t]
    i, j = PAIRS[t]; return (sum(c[r][0] for r in range(i, j)), sum(c[r][1] for r in range(i, j)))
def leaves2(nd, out):
    if nd[0] == 'split': leaves2(nd[4], out); leaves2(nd[5], out)
    else: out.append((nd[1], nd[2] if isinstance(nd[2], dict) else {}))
print("\nper-root best single cut (max side, straddle, axis, m) and the first split's balance")
for n, t in enumerate(d["trees"]):
    o = []; leaves2(t, o)
    if len(o) <= 650: continue
    keys = [('g', a) for a in range(Q)] + [('s', k) for k in range(len(PAIRS))]
    res = []
    for key in keys:
        rs = [rng(c, cons, key) for c, cons in o]
        cuts = sorted({x for r in rs for x in r})
        for m in cuts[1:-1:max(1, len(cuts) // 400)]:
            b = sum(1 for r in rs if r[1] <= m); ab = sum(1 for r in rs if r[0] >= m); st = len(o) - b - ab
            res.append((max(b, ab) + st, st, key, m))
    res.sort()
    ok = [x for x in res if x[0] <= 650]
    best = min(ok, key=lambda x: x[1]) if ok else res[0]
    A = []; leaves2(t[4], A); B = []; leaves2(t[5], B)
    print(f"root {n}: {len(o)} leaves; first split {len(A)}/{len(B)} on axis {t[3]}; best ≤650 cut: side {best[0]} straddle {best[1]} on {best[2]} at {best[3]}")
