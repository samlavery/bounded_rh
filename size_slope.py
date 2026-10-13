#!/usr/bin/env python3
"""Feasibility prototype of the SLOPE-AWARE certificate (float arithmetic, indicative only):
per term, a linear minorant of w on the term interval = the chord of w between the enclosing grid points
(spacing h) minus the curvature sag K (b-a)^2 / 8, K = max |w''| over the blocks spanned (x units);
the leaf test is the corner minimum of the resulting linear function of the gaps.
Usage: size_slope.py Q npz cN rule hexp blockexp KFAC   (h = 2^-hexp, K blocks of 2^-blockexp)"""
import sys, os, time, itertools, math
sys.set_int_max_str_digits(0); sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.expanduser("~/work/riemann-submission"))
from fractions import Fraction as Fr
import gen_w
from gen_w import G
Q = int(sys.argv[1]); npz = os.path.expanduser(sys.argv[2]); c = Fr(int(sys.argv[3]), 10**8); rule = sys.argv[4]
hexp = int(sys.argv[5]); bexp = int(sys.argv[6]); KFAC = float(sys.argv[7])
h = 2.0 ** -hexp; hb = 2.0 ** -bexp
pairs, A, Bv = gen_w.load_weights(npz, Q)
adj = [A[(r, r+1)] for r in range(Q)]
S = [Fr(-(-(4 * c) // Bv[r]), 4) for r in range(Q)]
covers = [G.phase1(c / adj[r], S[r]) for r in range(Q)]
bads = [cv[1] for cv in covers]
terms = [(float(A[(i, j)]), tuple(range(i, j))) for (i, j) in pairs]
Bf = [float(b) for b in Bv]; cf = float(c)
# ---- the kernel w(x) = (N/D)^2, N = cos b - 2 gam b sin b, D = 1 - 2 b^2, b = pi x, and its derivatives ----
S2 = math.sqrt(2.0); GAM = (1/S2)*math.cos(1/S2)/math.sin(1/S2)
def w_and_derivs(x):
    b = math.pi * x; sb, cb = math.sin(b), math.cos(b)
    N = cb - 2*GAM*b*sb; N1 = -sb - 2*GAM*(sb + b*cb); N2 = -cb - 2*GAM*(2*cb - b*sb)
    D = 1 - 2*b*b; D1 = -4*b; D2 = -4.0
    f = N/D; f1 = (N1*D - N*D1)/D**2; f2 = (N2*D - N*D2)/D**2 - 2*D1*(N1*D - N*D1)/D**3
    w = f*f; w1 = 2*f*f1*math.pi; w2 = 2*(f1*f1 + f*f2)*math.pi**2
    return w, w1, w2
# sanity: analytic w'' vs finite differences
for x in (0.6, 1.3, 2.7, 5.1):
    d = 1e-4; w0 = w_and_derivs(x)[0]; fd = (w_and_derivs(x+d)[0] - 2*w0 + w_and_derivs(x-d)[0])/d**2
    assert abs(fd - w_and_derivs(x)[2]) < 1e-3*max(1, abs(fd)), (x, fd, w_and_derivs(x)[2])
XMAX = float(sum(S)) + 1.0
nblk = int(XMAX / hb) + 1
Kblk = [0.0] * nblk
for j in range(nblk):
    x0 = j * hb; m = 0.0
    for i in range(33):
        m = max(m, abs(w_and_derivs(x0 + hb * i / 32)[2]))
    Kblk[j] = m * 1.05 * KFAC
ngrid = int(XMAX / h) + 2
V = [w_and_derivs(i * h)[0] - 1e-9 for i in range(ngrid)]
def minorant(lo, hi):
    """(alpha, sigma): w(s) >= alpha + sigma s on [lo, hi]"""
    ia = int(math.floor(lo / h)); ib = int(math.ceil(hi / h))
    if ib <= ia: ib = ia + 1
    a, b = ia * h, ib * h
    K = max(Kblk[int(a / hb): int(b / hb) + 1])
    sag = K * (b - a) ** 2 / 8
    sigma = (V[ib] - V[ia]) / (b - a)
    alpha = V[ia] - sigma * a - sag
    # the zero line is also a valid minorant; keep whichever is higher at the worse end of the interval
    if min(alpha + sigma * lo, alpha + sigma * hi) < 0: return 0.0, 0.0
    return alpha, sigma
def lower(box):
    bx = [(float(l), float(u)) for l, u in box]
    const = 0.0; C = [Bf[r] for r in range(Q)]
    for coef, idxs in terms:
        if coef == 0: continue
        lo = sum(bx[i][0] for i in idxs); hi = sum(bx[i][1] for i in idxs)
        al, sg = minorant(lo, hi)
        const += coef * al
        for k in idxs: C[k] += coef * sg
    return const + sum(C[k] * (bx[k][0] if C[k] >= 0 else bx[k][1]) for k in range(Q)) - 1e-9
count = [0]; widths = []
def children(box, k):
    m = (box[k][0] + box[k][1]) / 2
    a = list(box); a[k] = (box[k][0], m); b2 = list(box); b2[k] = (m, box[k][1])
    return tuple(a), tuple(b2)
def subdivide(box, depth=0):
    if sum(Bf[r] * float(box[r][0]) for r in range(Q)) >= cf: count[0] += 1; return True
    if lower(box) >= cf:
        count[0] += 1; widths.append(max(float(u - l) for l, u in box)); return True
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
print(f"slope-aware rule={rule} h=2^-{hexp} Kblocks=2^-{bexp} KFAC={KFAC} c={float(c):.8f}: {'OK' if ok else 'FAIL'} leaves={count[0]} "
      f"grid points={ngrid} ({time.time()-t:.0f}s); leaf max-width median={ws[len(ws)//2] if ws else 0:.4f} p10={ws[len(ws)//10] if ws else 0:.4f}", flush=True)
