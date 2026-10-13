import re, sys, itertools
from collections import Counter
sys.set_int_max_str_digits(0)
name = sys.argv[1] if len(sys.argv) > 1 else "SixW15"
params = open(f"{name}_params.txt").read().split()
Q = int(params[0]); SA = int(params[1]); aN = [int(x) for x in params[2].split(",")]; bN = [int(x) for x in params[3].split(",")]; cN = int(params[4])
SCE = int(params[6]) if len(params) > 6 else 96
SC = 2**SCE; SW = 10**13; SHIFT = SCE - 2
pairs = [(i, j) for i in range(Q+1) for j in range(i+1, Q+1)]
s = open(f"data_{name}.lean", encoding="utf-8").read()
cells = {}
for m in re.finditer(r"⟨([0-9a-z,\s]+?)⟩", s):
    f = [x for x in m.group(1).replace(" ", "").split(",") if x != ""]
    if not f or not f[0].isdigit(): continue
    if len(f) == 2: cells[(int(f[0]) // 1048576, int(f[0]) % 1048576)] = int(f[1])
    elif len(f) == 3: cells[(int(f[0]), int(f[1]))] = int(f[2])
    elif len(f) == 5: cells[(int(f[0]), int(f[1]))] = int(f[4])
bits = int(re.search(r"def bits : ℕ := (\d+)", s).group(1))
AXISIN = "(axis-coded walk)" in s
HALF = "(half-space)" in s
covers = []
for r in range(Q):
    body = re.search(rf"def cover{r} : List \(ℕ × ℕ × Bool\) := \[(.*?)\]", s, re.S).group(1)
    segs = [(int(a), int(b), c == "true") for a, b, c in re.findall(r"\((\d+), (\d+), (true|false)\)", body)]
    covers.append([(a, b) for a, b, cl in segs if not cl])
print(f"{name}: cells={len(cells)} bits={bits.bit_length()} bits  bad segments per gap={[len(c) for c in covers]}")
FUEL = int(sys.argv[2]) if len(sys.argv) > 2 else 64
XFARN = int(params[7]) * SC if len(params) > 7 else 0; FARG = int(params[8]) if len(params) > 8 else 0
FSH = (SCE - FARG.bit_length() + 1) if FARG else 0
def rnd(a, b):
    if FARG and a >= XFARN: return ((a >> FSH) << FSH, ((b + (1 << FSH) - 1) >> FSH) << FSH)
    return (a, b)
def pieces(a, hi, fuel=FUEL):
    out = []
    while True:
        if fuel == 0: out.append(rnd(a, hi)); return out
        q = ((a >> SHIFT) + 1) << SHIFT
        if q < hi: out.append(rnd(a, q)); a = q; fuel -= 1
        else: out.append(rnd(a, hi)); return out
stats = Counter(); finds_per_leaf = []; pieces_per_term = Counter(); maxp = 0
# tableless data: compute the piece bound with the integer pipeline (the kernel's WZ), scaled back to SC
if not cells:
    import importlib.util
    spec = importlib.util.spec_from_file_location("okz", "/Users/samuellavery/work/riemann-submission/okz_check.py")
    src_ok = open("/Users/samuellavery/work/riemann-submission/okz_check.py").read().split("for fn in sys.argv[1:]:")[0]
    okns = {}; exec(src_ok, okns)
    okns["SC"] = SC
    _wz = {}
    class _WZ(dict):
        def get(self, key, default=0):
            if key in _wz: return _wz[key]
            LN, UN = key; SCk = SC
            k = (2 * (LN + UN) + SCk) // (2 * SCk); side = k * SCk <= 2 * LN
            conds, (NLOZ, DHIZ, _) = okns["okZ"](LN, UN, k, side, 0, why=True)
            v = (NLOZ * NLOZ * SW) // (DHIZ * DHIZ) if all(conds[:9]) else 0
            _wz[key] = v; return v
        def __contains__(self, key): return True
    cells = _WZ()
    print("tableless data: piece bounds computed by the integer pipeline replica")
def termWN(lo, hi):
    global maxp
    ps = pieces(lo, hi); pieces_per_term[len(ps)] += 1; maxp = max(maxp, len(ps))
    cs = []
    for a, b in ps:
        w = cells.get((a, b))
        if w is None: return 0, len(ps)
        cs.append((a, b, w))
    # chainOK
    cur = lo
    for a, b, w in cs:
        if not (a <= cur): return 0, len(ps)
        cur = b
    if not (hi <= cur): return 0, len(ps)
    return min(w for _, _, w in cs), len(ps)
def leafCheck(b):
    l = b[0::2]; u = b[1::2]
    lin = sum(bN[r] * l[r] for r in range(Q))
    wsum = 0; nf = 0
    for t, (i, j) in enumerate(pairs):
        w, k = termWN(sum(l[i:j]), sum(u[i:j])); wsum += aN[t] * w; nf += k
    finds_per_leaf.append(nf)
    return cN * SC * SW <= lin * SW + wsum * SC
def widthArg(b):
    ws = [b[2*r+1] - b[2*r] for r in range(Q)]
    for r in range(Q-1):
        if all(ws[s2] <= ws[r] for s2 in range(r+1, Q)): return r
    return Q-1
sys.setrecursionlimit(100000)
leaves = 0; fails = 0
def walk(pos, b, fuel=64):
    global leaves, fails
    if fuel == 0: raise RuntimeError("fuel")
    if (bits >> pos) & 1:
        ax = ((bits >> (pos + 1)) & 7) if AXISIN else widthArg(b); q = (b[2*ax] + b[2*ax+1]) // 2
        bl = list(b); bl[2*ax+1] = q
        pos2 = walk(pos + (4 if AXISIN else 1), tuple(bl), fuel - 1)
        br = list(b); br[2*ax] = q
        return walk(pos2, tuple(br), fuel - 1)
    leaves += 1
    if HALF and b[0] > b[2*Q-1]: return pos + 1
    if not leafCheck(b): fails += 1
    return pos + 1
pos = 0
for idx in itertools.product(*[range(len(c)) for c in covers]):
    b = tuple(x for r in range(Q) for x in covers[r][idx[r]])
    pos = walk(pos, b)
print(f"roots={len(list(itertools.product(*[range(len(c)) for c in covers])))} leaves={leaves} leaf failures={fails} bits consumed={pos} (bit length {bits.bit_length()})")
print(f"max pieces per term = {maxp}; pieces histogram = {sorted(pieces_per_term.items())}")
fp = sorted(finds_per_leaf); print(f"finds per leaf: mean={sum(fp)/len(fp):.1f} median={fp[len(fp)//2]} max={fp[-1]} total={sum(fp)}")
