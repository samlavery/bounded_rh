"""Sizing of the weighted six-point certificate under the pyramid oracle (integer arithmetic throughout, coordinates
n / 2^15, oracle values in units of 1/U).  Mirrors gen_w.size (RULE=passfirst_sum, WFRAC=4, HALF=1) with:
  * the per-gap 1-D cover decided by the integer cell bound WZ of each dyadic segment (the kernel recomputes it),
  * leaves decided by the pyramid oracle: during the bisection with the direct-entry estimate E (every read cell
    carries its own cell bound; cells wider than a quarter the min of their halves), which never exceeds what the
    built table stores (min over finer descendants dominates the direct bound), then re-verified on the built table.
Usage (module): run(cN, PE, PB, MAXA, ...) -> dict(tree, covers, table, stats)"""
import os, sys, time, itertools, math
from functools import lru_cache
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.setrecursionlimit(1000000)
from wz import WZ, SW
from pyr_table import Pyr
SC = 1 << 15; Q = 5; QUARTER = 1 << 13; X0 = 1 << 14
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
# weights of the RKF certificate (symmetric under reversal), over SA = 10^8
AN = [25326800, 62369200, 40126500, 99999900, 200000000, 48244400, 37630700, 119746800, 99999900, 52857300, 37630700, 40126500, 48244400, 62369200, 25326800]
BN = [24896, 42034, 46137, 42034, 24896]
SA = 10**8
WFRAC = 4

# ---------------- float steering for the 1-D cover (as three_point_gen.wmin_true) ----------------
S2 = math.sqrt(2.0); GAMf = (1 / S2) * math.cos(1 / S2) / math.sin(1 / S2)
def wtrue(x):
    b = math.pi * x
    return ((math.cos(b) - 2 * GAMf * b * math.sin(b)) / (1 - 2 * b * b)) ** 2
def wmin_true(l, u, n=120):
    return min(wtrue((l + (u - l) * i / n) / SC) for i in range(n + 1))

def phase1(cN, aAdjN, S):
    """per-gap cover of [1/2, S] (units 2^-15): clear dyadic segments (cN*SW <= aAdjN*WZ) and merged bad runs"""
    roots = []; a = X0
    while a < S:
        b = min(a + QUARTER, S); roots.append((a, b)); a = b
    clear, bad = [], []
    stack = list(reversed(roots))
    while stack:
        l, u = stack.pop()
        if cN * SW <= aAdjN * WZ(l, u): clear.append((l, u)); continue
        if wmin_true(l, u) * aAdjN < cN and (u - l) <= SC // 64: bad.append((l, u)); continue
        if u - l <= SC // 4096: bad.append((l, u)); continue
        m = (l + u) // 2; stack.append((m, u)); stack.append((l, m))
    bad.sort(); merged = []
    for iv in bad:
        if merged and merged[-1][1] == iv[0]: merged[-1] = (merged[-1][0], iv[1])
        else: merged.append(iv)
    clear.sort()
    return clear, merged

def run(cN, PE=5, PB=10, MAXA=4, U=10**10, FUEL=14, max_leaves=4 * 10**6, verbose=True, aN=AN, bN=BN):
    t0 = time.time()
    P = Pyr(PE=PE, PB=PB, MAXA=MAXA, U=U, FUEL=FUEL)
    adj = [aN[PAIRS.index((r, r + 1))] for r in range(Q)]
    S = [-(-(4 * cN * SC) // (bN[r] * 4 * QUARTER)) * QUARTER for r in range(Q)]   # c / b_r rounded up to a quarter, in units
    # check: S_r * b_r >= c  (Lean of_check hS: cN * SC <= bN * S)
    for r in range(Q): assert cN * SC <= bN[r] * S[r]
    covers = [phase1(cN, adj[r], S[r]) for r in range(Q)]
    bads = [cv[1] for cv in covers]
    if verbose: print(f"cN={cN}: covers done ({time.time()-t0:.0f}s) bad sizes {[len(b) for b in bads]}", flush=True)
    # ---- direct-entry estimate ----
    @lru_cache(maxsize=None)
    def E(l, i):
        if l <= 13: return min(WZ(i << l, (i + 1) << l) * U // SW, P.EM)
        return min(E(l - 1, 2 * i), E(l - 1, 2 * i + 1))
    @lru_cache(maxsize=None)
    def lbE(lo, hi):
        cv = P.cover(lo, hi)
        if not cv or cv[-1] is None: return 0
        return min(E(l, i) for (l, i) in cv)
    CSU = cN * SC * U
    def lower(box, lb):
        lin = 0
        for r in range(Q): lin += bN[r] * box[r][0]
        tot = lin * U; s = 0
        for t, (i, j) in enumerate(PAIRS):
            lo = 0; hi = 0
            for r in range(i, j): lo += box[r][0]; hi += box[r][1]
            s += aN[t] * lb(lo, hi)
        return tot + s * SC
    def choose_axis(box, lb):
        w = [b[1] - b[0] for b in box]; mw = max(w); best = None
        for k in range(Q):
            if w[k] == 0: continue
            m = (box[k][0] + box[k][1]) // 2
            a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
            la, lb2 = lower(tuple(a), lb), lower(tuple(b2), lb)
            both = la >= CSU and lb2 >= CSU
            if w[k] * WFRAC < mw and not both: continue
            score = ((la >= CSU) + (lb2 >= CSU), la + lb2)
            if best is None or score > best[0]: best = (score, k)
        return best[1]
    count = [0]
    def subdivide(box, lb, depth=0):
        """('leaf', box) or ('split', box, k, m, A, B); None on failure"""
        if box[0][0] > box[Q - 1][1]: count[0] += 1; return ('leaf', box)
        if sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: count[0] += 1; return ('leaf', box)
        if lower(box, lb) >= CSU: count[0] += 1; return ('leaf', box)
        if depth > 60 or count[0] > max_leaves: return None
        if max(b[1] - b[0] for b in box) <= 1: return None
        k = choose_axis(box, lb); m = (box[k][0] + box[k][1]) // 2
        a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
        A = subdivide(tuple(a), lb, depth + 1)
        if A is None: return None
        B = subdivide(tuple(b2), lb, depth + 1)
        if B is None: return None
        return ('split', box, k, m, A, B)
    nodes = {}
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        if sum(bN[r] * box[r][0] for r in range(Q)) >= cN * SC: nodes[tup] = ('leaf', box); count[0] += 1; continue
        nd = subdivide(box, lbE)
        if nd is None:
            if verbose: print("FAIL at root", tup, count[0])
            return None
        nodes[tup] = nd
    nleaves = count[0]
    if verbose: print(f"  bisection: {nleaves} leaves ({time.time()-t0:.0f}s)", flush=True)
    # ---- build the table from the queries the leaves make, then verify every leaf on it ----
    leaves = []
    def collect(nd):
        if nd[0] == 'leaf': leaves.append(nd[1])
        else: collect(nd[4]); collect(nd[5])
    for nd in nodes.values(): collect(nd)
    def terms(box):
        out = []
        for (i, j) in PAIRS:
            out.append((sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))))
        return out
    qs = set()
    for b in leaves:
        if b[0][0] > b[Q - 1][1]: continue
        qs.update(terms(b))
    P.need(qs); P.build()
    bad_leaves = 0
    for b in leaves:
        if b[0][0] > b[Q - 1][1]: continue
        if sum(bN[r] * b[r][0] for r in range(Q)) >= cN * SC: continue
        if lower(b, P.lb) < CSU: bad_leaves += 1
    st = P.stats()
    if verbose:
        print(f"  table: {st}; distinct queries {len(qs)}; leaves failing on the built table: {bad_leaves} ({time.time()-t0:.0f}s)", flush=True)
    return dict(P=P, nodes=nodes, covers=covers, bads=bads, S=S, nleaves=nleaves, bad_leaves=bad_leaves, stats=st,
                cN=cN, aN=aN, bN=bN, nq=len(qs))

if __name__ == "__main__":
    delta = float(sys.argv[1]); PE = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    PB = int(sys.argv[3]) if len(sys.argv) > 3 else 10; MAXA = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    cN = round(358287 * (1 - delta))
    run(cN, PE=PE, PB=PB, MAXA=MAXA)
