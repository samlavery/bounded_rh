#!/usr/bin/env python3
"""Second prototype: per term choose among valid linear minorants — the current constant min (exact, G.Wmulti),
tangents at the grid point just below lo / above hi (valid when w is convex on the span), chord minus sag — and
take the best of several consistent leaf bounds (each is a valid lower bound, so their max is).
Usage: size_slope2.py Q npz cN rule hexp"""
import sys, os, time, itertools, math
sys.set_int_max_str_digits(0); sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
from fractions import Fraction as Fr
import gen_w
from gen_w import G
Q = int(sys.argv[1]); npz = os.path.expanduser(sys.argv[2]); c = Fr(int(sys.argv[3]), 10**8); rule = sys.argv[4]; hexp = int(sys.argv[5])
h = 2.0 ** -hexp
pairs, A, Bv = gen_w.load_weights(npz, Q)
adj = [A[(r, r+1)] for r in range(Q)]
S = [Fr(-(-(4 * c) // Bv[r]), 4) for r in range(Q)]
covers = [G.phase1(c / adj[r], S[r]) for r in range(Q)]
bads = [cv[1] for cv in covers]
termsF = [(A[(i, j)], tuple(range(i, j))) for (i, j) in pairs]
Bf = [float(b) for b in Bv]; cf = float(c)
S2 = math.sqrt(2.0); GAM = (1/S2)*math.cos(1/S2)/math.sin(1/S2)
def wd(x):
    b = math.pi * x; sb, cb = math.sin(b), math.cos(b)
    N = cb - 2*GAM*b*sb; N1 = -sb - 2*GAM*(sb + b*cb); N2 = -cb - 2*GAM*(2*cb - b*sb)
    D = 1 - 2*b*b; D1 = -4*b; D2 = -4.0
    f = N/D; f1 = (N1*D - N*D1)/D**2; f2 = (N2*D - N*D2)/D**2 - 2*D1*(N1*D - N*D1)/D**3
    return f*f, 2*f*f1*math.pi, 2*(f1*f1 + f*f2)*math.pi**2
XMAX = float(sum(S)) + 1.0
ngrid = int(XMAX / h) + 2
GV = [wd(i * h) for i in range(ngrid)]            # (w, w', w'') at grid points
NB = 256; hb = 1.0 / NB
nblk = int(XMAX * NB) + 2
K2lo = [0.0] * nblk; K2hi = [0.0] * nblk           # enclosure of w'' per block (sampled, with margin)
for j in range(nblk):
    vals = [wd(j * hb + hb * i / 16)[2] for i in range(17)]
    K2lo[j] = min(vals) - 0.02; K2hi[j] = max(vals) + 0.02
def convex_on(a, b): return min(K2lo[int(a * NB): int(b * NB) + 1]) >= 0
def Kmax(a, b): return max(abs(v) for v in K2lo[int(a * NB): int(b * NB) + 1] + K2hi[int(a * NB): int(b * NB) + 1])
_wm = {}
def Wconst(lo, hi):
    key = (lo, hi)
    if key not in _wm: _wm[key] = float(G.Wmulti(lo, hi))
    return _wm[key]
def minorants(loF, hiF, lo, hi):
    """list of (alpha, sigma) valid on [lo, hi] (floats), keyed by kind"""
    out = {"const": (Wconst(loF, hiF), 0.0)}
    ia = int(math.floor(lo / h)); ib = int(math.ceil(hi / h))
    if ib <= ia: ib = ia + 1
    a, b = ia * h, ib * h
    if convex_on(a, b):
        wa, s1a, _ = GV[ia]; wb, s1b, _ = GV[ib]
        out["tlo"] = (wa - s1a * a - 1e-9, s1a)       # tangent at a (slope lower-bounded in the real thing)
        out["thi"] = (wb - s1b * b - 1e-9, s1b)       # tangent at b
    K = Kmax(a, b); sag = K * (b - a) ** 2 / 8
    sg = (GV[ib][0] - GV[ia][0]) / (b - a)
    out["chord"] = (GV[ia][0] - sg * a - sag - 1e-9, sg)
    return out
def corner_min(const, C, bx):
    return const + sum(C[k] * (bx[k][0] if C[k] >= 0 else bx[k][1]) for k in range(Q))
def lower(box):
    bx = [(float(l), float(u)) for l, u in box]
    per = []
    for coef, idxs in termsF:
        if coef == 0: continue
        loF = sum(box[i][0] for i in idxs); hiF = sum(box[i][1] for i in idxs)
        per.append((float(coef), idxs, minorants(loF, hiF, float(loF), float(hiF))))
    best = -1e9
    for choice in ("const", "tlo", "thi", "chord", "minside", "mixlo", "mixhi"):
        const = 0.0; C = [Bf[r] for r in range(Q)]
        for coef, idxs, ms in per:
            if choice in ("const", "tlo", "thi", "chord"):
                al, sg = ms.get(choice, ms["const"])
            elif choice == "minside":   # tangent at the side where w is smaller, else const
                if "tlo" in ms:
                    lo = sum(bx[i][0] for i in idxs); hi = sum(bx[i][1] for i in idxs)
                    al, sg = ms["tlo"] if ms["tlo"][0] + ms["tlo"][1] * lo <= ms["thi"][0] + ms["thi"][1] * hi else ms["thi"]
                else: al, sg = ms["const"]
            elif choice == "mixlo":     # tangent where available, const otherwise; evaluate at the lo corner consistently
                al, sg = ms.get("tlo", ms["const"])
            else:
                al, sg = ms.get("thi", ms["const"])
            const += coef * al
            for k in idxs: C[k] += coef * sg
        best = max(best, corner_min(const, C, bx))
    return best - 1e-9
count = [0]; widths = []
def children(box, k):
    m = (box[k][0] + box[k][1]) / 2
    a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
    return tuple(a), tuple(b2)
def subdivide(box, depth=0):
    if sum(Bf[r] * float(box[r][0]) for r in range(Q)) >= cf: count[0] += 1; return True
    if lower(box) >= cf: count[0] += 1; widths.append(max(float(u - l) for l, u in box)); return True
    if depth > 80 or count[0] > 3 * 10**6: return False
    w = [b[1] - b[0] for b in box]
    if rule == "widest": k = w.index(max(w))
    else:
        best = None
        for kk in range(Q):
            if w[kk] == 0: continue
            a, b2 = children(box, kk); la, lb = lower(a), lower(b2)
            both = la >= cf and lb >= cf
            if w[kk] * 4 < max(w) and not both: continue
            score = ((la >= cf) + (lb >= cf), la + lb)
            if best is None or score > best[0]: best = (score, kk)
        k = best[1]
    a, b2 = children(box, k)
    return subdivide(a, depth + 1) and subdivide(b2, depth + 1)
t = time.time(); ok = True
for tup in itertools.product(*[range(len(bd)) for bd in bads]):
    box = tuple(bads[r][tup[r]] for r in range(Q))
    if sum(Bf[r] * float(box[r][0]) for r in range(Q)) >= cf: count[0] += 1; continue
    if not subdivide(box): ok = False; break
ws = sorted(widths)
print(f"slope2 rule={rule} h=2^-{hexp} c={float(c):.8f}: {'OK' if ok else 'FAIL'} leaves={count[0]} ({time.time()-t:.0f}s); leaf max-width median={ws[len(ws)//2] if ws else 0:.4f} p10={ws[len(ws)//10] if ws else 0:.4f}", flush=True)
