#!/usr/bin/env python3
"""Sizing prototype (floats, no certification): leaf count of the n = 8 AM certificate when the bisection may split on
pair distances s_t = g_i + ... + g_{j-1} as well as on gaps, so that cells are polytopes
{l <= g <= u, Lb_t <= s_t <= Ub_t}.  The leaf test is the LP over the cell with each pair term replaced by the lower
convex hull of w on the term's range (the best any per-term affine-minorant certificate can do), so both modes share
one leaf test and differ only in what they may split:
  MODE=box   gaps only (control);
  MODE=pair  gaps or pair distances (the term with the largest relaxation error at the LP point, at its range midpoint).
Usage: AMWIN=W.json psum8.py W.json DELTA MODE [ROOTSEL e.g. 4,17]"""
import os, sys, time, json, ast, itertools
import numpy as np
from scipy.optimize import linprog
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.environ.setdefault("NOS", "1")
import size8amz as S8
from amk import w as wf

J = json.load(open(sys.argv[1])); DELTA = float(sys.argv[2]); MODE = sys.argv[3]
ROOTSEL = [int(x) for x in sys.argv[4].split(",")] if len(sys.argv) > 4 else None
Q = S8.Q; PAIRS = S8.PAIRS; NP = len(PAIRS); SC = S8.SC
aJ = ast.literal_eval(J["aN"]) if isinstance(J["aN"], str) else J["aN"]
aN = [int(aJ[f"{i},{j}"]) for (i, j) in PAIRS]; bN = [int(x) for x in J["bN"]]
gmin = float(J["eps_strong"]) * 1e8; cN = int(gmin * (1 - DELTA))
a = np.array(aN, float) / 1e8; b = np.array(bN, float) / 1e8; cF = cN / 1e8
ACT = [t for t in range(NP) if aN[t] > 0]
INC = np.zeros((NP, Q))
for t, (i, j) in enumerate(PAIRS): INC[t, i:j] = 1.0

# roots exactly as size8amz.run
adj = [aN[PAIRS.index((r, r + 1))] for r in range(Q)]
Sx = [-(-(4 * cN * SC) // (bN[r] * 4 * S8.QUARTER)) * S8.QUARTER for r in range(Q)]
bads = [S8.phase1(cN, adj[r], Sx[r])[1] for r in range(Q)]

# w on a fine grid and the per-range lower hull
H = 4096; XMAX = 96
XS = np.arange(0, XMAX * H + 2) / H; WS = wf(XS)
_hc = {}
def hull_lines(L, U):
    i0 = max(0, int(np.floor(L * H))); i1 = min(len(XS) - 1, int(np.ceil(U * H)))
    k = (i0, i1)
    if k in _hc: return _hc[k]
    x = XS[i0:i1 + 1]; y = WS[i0:i1 + 1]
    n = len(x)
    if n > 6000:   # decimate by block minima (keeps the lower hull to within the block's variation)
        B = -(-n // 3000); m = (n // B) * B
        yb = y[:m].reshape(-1, B); ib = yb.argmin(axis=1) + np.arange(0, m, B)
        idx = np.concatenate([[0], ib, np.arange(m, n), [n - 1]]); idx = np.unique(idx)
        x = x[idx]; y = y[idx]
    hull = []
    for px, py in zip(x, y):
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (x2 - x1) * (py - y1) - (y2 - y1) * (px - x1) <= 0: hull.pop()
            else: break
        hull.append((px, py))
    lines = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        sl = (y2 - y1) / (x2 - x1); lines.append((y1 - sl * x1 - 1e-12, sl))
    if not lines: lines = [(float(y.min()) - 1e-12, 0.0)]
    _hc[k] = lines
    return lines

CAND = os.environ.get("CAND", "hull")
from amk import w1 as w1f
W1S = w1f(XS); W2S = np.gradient(W1S, 1.0 / H)
GSH = int(os.environ.get("GSH", "5")); NPOS = int(os.environ.get("NPOS", "8"))
def prod_lines(L, U):
    """production-like candidates (sizing semantics): the constant min w on the range, and tangents at the grid points
    ((L + (U - L) j / 8) >> g) << g (units 2^-15; g = 8 and GSH) lying where w'' >= 0, kept when they stay below w on the
    whole range (checked on the 1/4096 grid)"""
    i0 = max(0, int(np.floor(L * H))); i1 = min(len(XS) - 1, int(np.ceil(U * H)))
    k = ("p", i0, i1)
    if k in _hc: return _hc[k]
    y = WS[i0:i1 + 1]; x = XS[i0:i1 + 1]
    out = [(float(y.min()) - 1e-12, 0.0)]
    Li = int(L * SC); Ui = int(U * SC); seen = set()
    if Ui - Li >= 64:
        for gs in (8, GSH):
            ga = ((Li + (1 << gs) - 1) >> gs) << gs; gb = (Ui >> gs) << gs
            if ga > gb: continue
            for j in range(NPOS + 1):
                p = ((Li + ((Ui - Li) * j // NPOS)) >> gs) << gs; p = min(gb, max(ga, p))
                if p in seen: continue
                seen.add(p); ip = int(round(p / SC * H))
                if W2S[ip] < 0: continue
                wp = WS[ip]; dp = W1S[ip]; al = wp - dp * (p / SC)
                if (y - (al + dp * x)).min() < -1e-13: continue
                out.append((al - 1e-12, dp))
    _hc[k] = out
    return out
_hull_full = hull_lines
def tan_lines(L, U):
    """the hull's tangent edges only (both ends within 4 fine samples, i.e. w itself is on the hull there) plus the
    constant: what dense tangents can do without lines that bridge a lobe"""
    k = ("t", int(np.floor(L * H)), int(np.ceil(U * H)))
    if k in _hc: return _hc[k]
    i0 = max(0, k[1]); i1 = min(len(XS) - 1, k[2]); y = WS[i0:i1 + 1]
    out = [(float(y.min()) - 1e-12, 0.0)]
    # rebuild the hull with its vertices to measure edge lengths
    x = XS[i0:i1 + 1]
    hull = []
    for px, py in zip(x, y):
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (x2 - x1) * (py - y1) - (y2 - y1) * (px - x1) <= 0: hull.pop()
            else: break
        hull.append((px, py))
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        if x2 - x1 <= 4.0 / H + 1e-12:
            sl = (y2 - y1) / (x2 - x1); out.append((y1 - sl * x1 - 1e-12, sl))
    if len(out) > 400: out = [out[0]] + out[1::max(1, len(out) // 400)]
    _hc[k] = out
    return out
if CAND == "prod": hull_lines = prod_lines
if CAND == "tan": hull_lines = tan_lines

NOSUMROWS = os.environ.get("NOSUMROWS") == "1"; NOFBBT = os.environ.get("NOFBBT") == "1"
def tighten(l, u, Lb, Ub):
    if NOFBBT:
        for t in Lb.keys() | Ub.keys():
            i, j = PAIRS[t]
            if max(Lb.get(t, -1e9), l[i:j].sum()) > min(Ub.get(t, 1e9), u[i:j].sum()) + 1e-12: return False
        return True
    for _ in range(4):
        ch = False
        for t in Lb.keys() | Ub.keys():
            i, j = PAIRS[t]; sl = l[i:j].sum(); su = u[i:j].sum()
            Le = max(Lb.get(t, -1e9), sl); Ue = min(Ub.get(t, 1e9), su)
            if Le > Ue + 1e-12: return False
            for r in range(i, j):
                nu = Ue - (sl - l[r]); nl = Le - (su - u[r])
                if nu < u[r] - 1e-12: u[r] = nu; ch = True
                if nl > l[r] + 1e-12: l[r] = nl; ch = True
                if l[r] > u[r] + 1e-12: return False
        if not ch: break
    return True

stats = dict(lp=0, leaves=0, empty=0, refl=0, lin=0, lpleaf=0, gsplit=0, ssplit=0, stuck=0)
def lp(l, u, Lb, Ub):
    A = []; bu = []; rng = {}
    for t in ACT:
        i, j = PAIRS[t]; Le = max(Lb.get(t, -1e9), l[i:j].sum()); Ue = min(Ub.get(t, 1e9), u[i:j].sum())
        rng[t] = (Le, Ue)
        for al, sl in hull_lines(Le, Ue):
            row = np.zeros(Q + NP); row[:Q] = sl * INC[t]; row[Q + t] = -1.0; A.append(row); bu.append(-al)
    for t in ([] if NOSUMROWS else Lb.keys() | Ub.keys()):
        if t in Ub: row = np.zeros(Q + NP); row[:Q] = INC[t]; A.append(row); bu.append(Ub[t])
        if t in Lb: row = np.zeros(Q + NP); row[:Q] = -INC[t]; A.append(row); bu.append(-Lb[t])
    c = np.concatenate([b, a])
    bounds = list(zip(l, u)) + [(None, None) if aN[t] > 0 else (0, 0) for t in range(NP)]
    r = linprog(c, A_ub=np.array(A), b_ub=np.array(bu), bounds=bounds, method="highs")
    stats["lp"] += 1
    if r.status == 2: return "empty", None, rng
    if r.status != 0: return None, None, rng
    return r.fun, r.x, rng

REFB = int(os.environ.get("REFB", "0")); REFMIX = os.environ.get("REFMIX", "1") == "1"
rstat = dict(leaves=0, mixed=0, tang=0, const=0, ymult=0)
def ref_lp(l, u, Lb, Ub, x):
    """reference-point leaf: the leaf stores g_ref (REFB bits per gap within [l_r, u_r]); every term's tangent point is
    the grid point nearest INC_t g_ref, clamped into its effective range; the term's minorant is that tangent when it is
    valid on the range (REFMIX: the LP may also mix it with the constant), else the constant"""
    gs = x[:Q]; wd = np.maximum(u - l, 1e-15)
    gr = l + wd * np.round((1 << REFB) * np.clip((gs - l) / wd, 0, 1)) / (1 << REFB)
    sr = INC @ gr
    A = []; bu = []; kinds = {}
    G = 1 << GSH
    for t in ACT:
        i, j = PAIRS[t]; Le = max(Lb.get(t, -1e9), l[i:j].sum()); Ue = min(Ub.get(t, 1e9), u[i:j].sum())
        i0 = max(0, int(np.floor(Le * H))); i1 = min(len(XS) - 1, int(np.ceil(Ue * H))); y = WS[i0:i1 + 1]; xx = XS[i0:i1 + 1]
        lines = [(float(y.min()) - 1e-12, 0.0)]
        Li = int(np.ceil(Le * SC / G)) * G; Ui = int(np.floor(Ue * SC / G)) * G
        tang = None
        if Ui >= Li:
            p = min(Ui, max(Li, int(round(sr[t] * SC / G)) * G)); ip = int(round(p / SC * H))
            if W2S[ip] >= 0:
                dp = W1S[ip]; al = WS[ip] - dp * (p / SC)
                if (y - (al + dp * xx)).min() >= -1e-13: tang = (al - 1e-12, dp)
        if tang is not None: lines = (lines + [tang]) if REFMIX else [tang]
        kinds[t] = len(lines)
        for al, sl in lines:
            row = np.zeros(Q + NP); row[:Q] = sl * INC[t]; row[Q + t] = -1.0; A.append(row); bu.append(-al)
    srows = []
    for t in Lb.keys() | Ub.keys():
        if t in Ub: row = np.zeros(Q + NP); row[:Q] = INC[t]; A.append(row); bu.append(Ub[t]); srows.append(len(A) - 1)
        if t in Lb: row = np.zeros(Q + NP); row[:Q] = -INC[t]; A.append(row); bu.append(-Lb[t]); srows.append(len(A) - 1)
    c = np.concatenate([b, a])
    bounds = list(zip(l, u)) + [(None, None) if aN[t] > 0 else (0, 0) for t in range(NP)]
    r = linprog(c, A_ub=np.array(A), b_ub=np.array(bu), bounds=bounds, method="highs")
    if r.status != 0: return -1.0, None
    mu = -r.ineqlin.marginals; k = 0; nm = nt = nc = 0
    for t in ACT:
        m_ = mu[k:k + kinds[t]]; k += kinds[t]
        if kinds[t] == 2 and (m_ > 1e-12 * a[t]).sum() == 2: nm += 1
        elif kinds[t] == 2 and m_[1] > m_[0]: nt += 1
        elif kinds[t] == 1 and not REFMIX and len(m_) == 1: nt += 0
        else: nc += 1
    ny = int((mu[srows] > 1e-12).sum()) if srows else 0
    return r.fun, (nm, nt, nc, ny)

MAXN = int(os.environ.get("MAXN", "2000000"))
def run_root(box):
    l0 = np.array([x[0] for x in box], float) / SC; u0 = np.array([x[1] for x in box], float) / SC
    stack = [(l0, u0, {}, {}, 0)]; n0 = stats["leaves"]
    while stack:
        l, u, Lb, Ub, d = stack.pop()
        if not tighten(l, u, Lb, Ub): stats["empty"] += 1; stats["leaves"] += 1; continue
        if l[0] > u[Q - 1]: stats["refl"] += 1; stats["leaves"] += 1; continue
        if b @ l >= cF: stats["lin"] += 1; stats["leaves"] += 1; continue
        v, x, rng = lp(l, u, Lb, Ub)
        if v == "empty": stats["empty"] += 1; stats["leaves"] += 1; continue
        if v is not None and v >= cF and REFB:
            vr, info = ref_lp(l, u, Lb, Ub, x)
            if vr >= cF:
                stats["lpleaf"] += 1; stats["leaves"] += 1; rstat["leaves"] += 1
                for k_, v_ in zip(("mixed", "tang", "const", "ymult"), info): rstat[k_] += v_
                continue
            v = -1.0
        if v is not None and v >= cF: stats["lpleaf"] += 1; stats["leaves"] += 1; continue
        if stats["leaves"] > MAXN or d > 200: stats["stuck"] += 1; return False
        if x is None:
            r_ = int(np.argmax(u - l)); m = (l[r_] + u[r_]) / 2
            A_ = (l.copy(), u.copy(), dict(Lb), dict(Ub), d + 1); A_[1][r_] = m
            B_ = (l.copy(), u.copy(), dict(Lb), dict(Ub), d + 1); B_[0][r_] = m
            stats["gsplit"] += 1; stack.append(B_); stack.append(A_); continue
        g = x[:Q]; s = INC @ g
        err = np.zeros(NP)
        for t in ACT: err[t] = a[t] * (float(np.interp(s[t], XS, WS)) - x[Q + t])
        viol = []
        if NOSUMROWS:
            for t_ in Lb.keys() | Ub.keys():
                v_ = max(s[t_] - Ub.get(t_, 1e9), Lb.get(t_, -1e9) - s[t_])
                if v_ > 1e-9: viol.append((v_ * a[t_], t_))
        if MODE == "pair" and viol:
            t = max(viol)[1]; i, j = PAIRS[t]; r_ = i + int(np.argmax((u - l)[i:j])); m = (l[r_] + u[r_]) / 2
            A_ = (l.copy(), u.copy(), dict(Lb), dict(Ub), d + 1); A_[1][r_] = m
            B_ = (l.copy(), u.copy(), dict(Lb), dict(Ub), d + 1); B_[0][r_] = m
            stats["gsplit"] += 1
        elif MODE == "pair":
            t = int(np.argmax(err)); Le, Ue = rng[t]; i, j = PAIRS[t]
            if j - i == 1:
                r_ = i; m = (l[r_] + u[r_]) / 2
                A_ = (l.copy(), u.copy(), dict(Lb), dict(Ub), d + 1); A_[1][r_] = m
                B_ = (l.copy(), u.copy(), dict(Lb), dict(Ub), d + 1); B_[0][r_] = m
                stats["gsplit"] += 1
            else:
                m = (Le + Ue) / 2
                A_ = (l.copy(), u.copy(), dict(Lb), {**Ub, t: m}, d + 1)
                B_ = (l.copy(), u.copy(), {**Lb, t: m}, dict(Ub), d + 1)
                stats["ssplit"] += 1
        else:
            sc = np.array([sum(err[t] for t in range(NP) if PAIRS[t][0] <= r < PAIRS[t][1]) for r in range(Q)])
            sc = sc * (u - l > 1e-9)
            r_ = int(np.argmax(sc)) if sc.max() > 0 else int(np.argmax(u - l)); m = (l[r_] + u[r_]) / 2
            A_ = (l.copy(), u.copy(), Lb, Ub, d + 1); A_[1][r_] = m
            B_ = (l.copy(), u.copy(), Lb, Ub, d + 1); B_[0][r_] = m
            stats["gsplit"] += 1
        stack.append(B_); stack.append(A_)
    return stats["leaves"] - n0

t0 = time.time()
print(f"MODE={MODE} delta={DELTA} cN={cN} roots={np.prod([len(x) for x in bads])}", flush=True)
for ri, tup in enumerate(itertools.product(*[range(len(bd)) for bd in bads])):
    if ROOTSEL is not None and ri not in ROOTSEL: continue
    box = tuple(bads[r][tup[r]] for r in range(Q))
    n = run_root(box)
    print(f"  root {ri} {tup}: {n} leaves  stats {stats} ({time.time()-t0:.0f}s)", flush=True)
    if n is False: break
print(f"total {stats} ref {rstat} ({time.time()-t0:.0f}s)", flush=True)
