"""Operation counts for the sampled SixW7 walks (independent re-implementation of the Lean `walk`).
Parses BenchData.lean (table, bits, bx boxes), replays `walk` on each sampled theorem, checks the
returned position against the theorem statement, and counts: leaves, leaves reaching `leafCheck`,
termWN calls, pieces, `CTN.find` node visits, chain failures.
Usage: python3 count_ops.py [wk0 wk5 ...]"""
import re, sys, os
sys.setrecursionlimit(100000); sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, "BenchData.lean")).read()
sol = open(os.path.join(HERE, "..", "SolutionSixW7.lean")).read()

KB = 1048576; SC = 32768; SW = 10000000000000; cN = 333207; XFARN = 98304

# ---- table ----
defs = dict(re.findall(r"noncomputable def (tab\d+|table) : CTN :=\n  (.*)", src))
TOK = re.compile(r"\(|\)|N|E|⟨(\d+),(\d+)⟩|(tab\d+)")
def parse(name):
    toks = [m for m in TOK.finditer(defs[name])]
    i = 0
    def expr():
        nonlocal i
        t = toks[i]; s = t.group(0)
        if s == "E": i += 1; return None
        if t.group(3): i += 1; return parse(t.group(3))
        assert s == "("; i += 1
        assert toks[i].group(0) == "N"; i += 1
        l = expr(); c = toks[i]; i += 1
        cell = (int(c.group(1)), int(c.group(2)))
        r = expr(); assert toks[i].group(0) == ")"; i += 1
        return (l, cell, r)
    return expr()
table = parse("table")
def size(t): return 0 if t is None else 1 + size(t[0]) + size(t[2])
def depth(t): return 0 if t is None else 1 + max(depth(t[0]), depth(t[2]))

bits = int(re.search(r"^def bits : ℕ := (\d+)", src, re.M).group(1))

# ---- boxes ----
def axOf(pos): return (bits >> (pos + 1)) & 7
def mid(b, ax): ax = min(ax, 4); return (b[2*ax] + b[2*ax+1]) // 2
def setHi(b, ax, q): ax = min(ax, 4); b = list(b); b[2*ax+1] = q; return tuple(b)
def setLo(b, ax, q): ax = min(ax, 4); b = list(b); b[2*ax] = q; return tuple(b)
bx = {}
for name, body in re.findall(r"noncomputable def (bx\d+) : SixW7.Box := (.*)", src):
    m = re.match(r"\(SixW7.Box.mk ([\d ]+)\)", body)
    if m: bx[name] = tuple(int(x) for x in m.group(1).split()); continue
    m = re.match(r"\((bx\d+)\)\.(setHi|setLo) \(SixW7.axOf bits (\d+)\) \(SixW7.Box.mid (bx\d+) \(SixW7.axOf bits (\d+)\)\)", body)
    p, op, pos = m.group(1), m.group(2), int(m.group(3))
    ax = axOf(pos); q = mid(bx[p], ax)
    bx[name] = (setHi if op == "setHi" else setLo)(bx[p], ax, q)

C = dict(leaves=0, leafchecks=0, terms=0, pieces=0, find_visits=0, find_miss=0, chain_fail=0, leaf_fail=0, max_pieces=0)
def find(q):
    t = table
    while t is not None:
        C["find_visits"] += 1
        l, (key, wn), r = t
        if q < key: t = l
        elif key < q: t = r
        else: return (key, wn)
    C["find_miss"] += 1
    return None
def roundFar(a, b): return (((a >> 7) << 7), (((b + 127) >> 7) << 7)) if XFARN <= a else (a, b)
def piecesN(fuel, a, hi):
    out = []
    while True:
        if fuel == 0: out.append(roundFar(a, hi)); return out
        q = ((a >> 13) + 1) << 13
        if q < hi: out.append(roundFar(a, q)); a = q; fuel -= 1
        else: out.append(roundFar(a, hi)); return out
def termWN(lo, hi):
    C["terms"] += 1
    ps = piecesN(64, lo, hi); C["pieces"] += len(ps); C["max_pieces"] = max(C["max_pieces"], len(ps))
    cs = []
    for (a, b) in ps:          # lookupAllN: stops at the first miss (matcher cases on the find first)
        c = find(a * KB + b)
        if c is None: return 0
        cs.append(c)
    x = lo
    for (key, wn) in cs:
        if not key // KB <= x: C["chain_fail"] += 1; return 0
        x = key % KB
    if not hi <= x: C["chain_fail"] += 1; return 0
    return min(wn for _, wn in cs)
W = [25326800, 62369200, 40126500, 99999900, 200000000, 48244400, 37630700, 119746800, 99999900, 52857300, 37630700, 40126500, 48244400, 62369200, 25326800]
SPANS = [(i, j) for i in range(5) for j in range(i, 5)]
def leafCheck(b):
    C["leafchecks"] += 1
    l = b[0::2]; u = b[1::2]
    tot = 0
    for wgt, (i, j) in zip(W, SPANS):
        tot += wgt * termWN(sum(l[i:j+1]), sum(u[i:j+1]))
    lin = 24896*l[0] + 42034*l[1] + 46137*l[2] + 42034*l[3] + 24896*l[4]
    return cN * SC * SW <= lin * SW + tot * SC
def walk(fuel, pos, b):
    if fuel == 0: return None
    fuel -= 1
    if (bits >> pos) & 1:
        ax = axOf(pos); q = mid(b, ax)
        r = walk(fuel, pos + 4, setHi(b, ax, q))
        if r is None: return None
        return walk(fuel, r, setLo(b, ax, q))
    C["leaves"] += 1
    if b[9] < b[0] or leafCheck(b): return pos + 1   # b.u4 < b.l0  (Box.mk l0 u0 l1 u1 ... l4 u4)
    C["leaf_fail"] += 1; return None

# SPANS order check against leafCheck's term order: (0..0),(0..1),...,(0..4),(1..1),...,(4..4)
names = sys.argv[1:] or "wk0 wk5 wk13 wk14 wk15 wk18 wk21 wk22 wk27 wk46".split()
print(f"table: {size(table)} cells, depth {depth(table)}")
print("thm      leaves  leafChk  terms  pieces  pcs/term  maxpcs  findVisits  visits/find  chainFail  ok")
tot = {k: 0 for k in C}
for n in names:
    m = re.search(rf"theorem {n} : SixW7.walk table bits (\d+) (\d+) (bx\d+) = some (\d+)", sol)
    fuel, pos, b, end = int(m.group(1)), int(m.group(2)), m.group(3), int(m.group(4))
    for k in C: C[k] = 0
    r = walk(fuel, pos, bx[b])
    print(f"{n:7s} {C['leaves']:7d} {C['leafchecks']:8d} {C['terms']:6d} {C['pieces']:7d} {C['pieces']/max(1,C['terms']):9.2f} {C['max_pieces']:7d} {C['find_visits']:11d} {C['find_visits']/max(1,C['pieces']):12.2f} {C['chain_fail']:10d}  {r == end}")
    for k in C: tot[k] = tot[k] + C[k] if k != "max_pieces" else max(tot[k], C[k])
print(f"TOTAL   {tot['leaves']:7d} {tot['leafchecks']:8d} {tot['terms']:6d} {tot['pieces']:7d} {tot['pieces']/max(1,tot['terms']):9.2f} {tot['max_pieces']:7d} {tot['find_visits']:11d} {tot['find_visits']/max(1,tot['pieces']):12.2f} {tot['chain_fail']:10d}")
