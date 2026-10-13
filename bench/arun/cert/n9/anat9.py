"""bridge-port 2026-10-10: leaf anatomy and parent-split reasons of a 9-point (or any-n) sizing dump, in float.
Pre-registration and the classification rules: ANATOMY.md §0.  Usage:
    python3 anat9.py DUMP.pkl WEIGHTS.json DELTA BASINS.json OUT.json [NLEAF_SAMPLE] [NPARENT_SAMPLE]
BASINS.json: a json with near-binding gap vectors under 'basins_excess_le_2e-4' (list of {'gaps': ...}) or
'root_hints_near_binding' (list of vectors or of {'gaps': ...}).
Everything here is a float model (sizing-only), not a certificate."""
import sys, os, json, pickle, math, time
import numpy as np
from scipy.optimize import linprog, minimize
os.environ.setdefault("AMWIN", "/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json")
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/window/amg")
sys.path.insert(0, "/Users/samuellavery/work/riemann-submission/bench/pyr")
import amk
DUMP, WJ, DELTA, BJ, OUT = sys.argv[1], sys.argv[2], float(sys.argv[3]), sys.argv[4], sys.argv[5]
NLS = int(sys.argv[6]) if len(sys.argv) > 6 else 3000
NPS = int(sys.argv[7]) if len(sys.argv) > 7 else 1500
rng = np.random.default_rng(20261010)
J = json.load(open(WJ)); n = J["n"]; Q = n - 1
PAIRS = [(i, j) for i in range(n) for j in range(i + 1, n)]; NP = len(PAIRS)
aN = np.array([int(J["aN"][f"{i},{j}"]) for (i, j) in PAIRS]); bN = np.array([int(x) for x in J["bN"]])
a = aN / 1e8; b = bN / 1e8
cTrue = float(J["eps_strong"]); cN = int(cTrue * 1e8 * (1 - DELTA)); cNf = cN / 1e8
SC = 32768; LS = 256; JSH = 5; GS = 5; JLO = (1 << JSH) + 1
ACT = [t for t in range(NP) if aN[t] > 0]
INC = np.zeros((NP, Q))
for t, (i, j) in enumerate(PAIRS): INC[t, i:j] = 1
# float kernel tables on 1/4096 (enough for exact-validity and min checks, as the sizer's EXACTV)
HX = 4096; XS = np.arange(0, 80 * HX + 2) / HX
WS = amk.w(XS); W1S = amk.w1(XS); W2S = np.gradient(W1S, 1.0 / HX)
def w(x): return amk.w(x)
def w1(x): return amk.w1(x)
def F(g):
    s = INC @ g; return float(b @ g + a @ w(s))
def Fgrad(g):
    s = INC @ g; return float(b @ g + a @ w(s)), b + INC.T @ (a * w1(s))
def gi(xsc): return int(xsc * HX // SC)
def wmin(L, U): i0 = gi(L); i1 = -(-U * HX // SC); return float(WS[i0:i1 + 1].min())
def w2min(L, U): i0 = gi(L); i1 = -(-U * HX // SC); return float(W2S[max(i0 - 1, 0):i1 + 2].min())
def w2max(L, U): i0 = gi(L); i1 = -(-U * HX // SC); return float(W2S[max(i0 - 1, 0):i1 + 2].max())
def tvalid(L, U, p):
    i0 = gi(L); i1 = -(-U * HX // SC); x = XS[i0:i1 + 1]
    return bool((WS[i0:i1 + 1] - (float(w(p / SC)) + float(w1(p / SC)) * (x - p / SC))).min() >= -1e-13)
def gpt(L, U_, jj):
    if jj == JLO: return L
    gs = GS if jj >> (JSH + 1) else 8; j = jj & ((1 << (JSH + 1)) - 1); gm = (1 << gs) - 1
    ga = ((L + gm) >> gs) << gs; gb = (U_ >> gs) << gs; x = ((L + (((U_ - L) * j) >> JSH)) >> gs) << gs
    r = ga if x <= ga else (gb if gb <= x else x)
    return r if ga <= gb else (r if L <= r <= U_ else None)
JJ = [j + (1 << (JSH + 1)) * f for f in (0, 1) for j in range((1 << JSH) + 1)] + [JLO]
def iv(box, cons):
    out = []
    for t, (i, j) in enumerate(PAIRS):
        L = sum(box[r][0] for r in range(i, j)); U = sum(box[r][1] for r in range(i, j))
        if t in cons:
            Lb, Ub = cons[t]
            if Lb is not None: L = max(L, Lb)
            if Ub is not None: U = min(U, Ub)
        out.append((L, U))
    return out
def polycons(box, cons):
    """box bounds (gap units) and pair-sum rows A g <= c from the explicit constraints"""
    bnds = [(l / SC, u / SC) for (l, u) in box]; A = []; c = []
    for t, (Lb, Ub) in cons.items():
        if Ub is not None: A.append(INC[t]); c.append(Ub / SC)
        if Lb is not None: A.append(-INC[t]); c.append(-Lb / SC)
    return bnds, (np.array(A) if A else None), (np.array(c) if c else None)
def lp_relax(box, cons, cands):
    """min b.g + sum a_t z_t, z_t >= every candidate line of t, g in the cell polytope; cands[t] = list of (v, d, p) in
    gap units: z >= v + d (s - p)"""
    bnds, A0, c0 = polycons(box, cons)
    rows = []; rhs = []
    for t in ACT:
        for (v, d, p) in cands[t]:
            r = np.zeros(Q + NP); r[:Q] = d * INC[t]; r[Q + t] = -1.0; rows.append(r); rhs.append(-(v - d * p))
    if A0 is not None:
        for k in range(len(A0)):
            r = np.zeros(Q + NP); r[:Q] = A0[k]; rows.append(r); rhs.append(c0[k])
    cost = np.concatenate([b, a])
    zb = [(None, None) if aN[t] > 0 else (0, 0) for t in range(NP)]
    res = linprog(cost, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=bnds + zb, method="highs")
    if res.status == 2: return float("inf")
    if res.status != 0: return float("nan")
    return (res.fun - cNf) / cNf
def cands_first(box, cons, so=False, const_only=False):
    I = iv(box, cons); out = {}
    for t in ACT:
        L, U = I[t]; cs = [(wmin(L, U), 0.0, L / SC)]
        if not const_only and U > L:
            seen = set()
            for jj in JJ:
                p = gpt(L, U, jj)
                if p is None or p in seen: continue
                seen.add(p)
                if tvalid(L, U, p): cs.append((float(w(p / SC)), float(w1(p / SC)), p / SC))
            if so:
                m2 = w2min(L, U) - 1e-9
                for fr in (1, 2, 3):
                    p = L + ((U - L) * fr) // 4; wp = float(w(p / SC)); dp = float(w1(p / SC))
                    if m2 >= 0: cs.append((wp, dp, p / SC))
                    else:
                        ql = wp + dp * (L - p) / SC + 0.5 * m2 * ((L - p) / SC) ** 2
                        qh = wp + dp * (U - p) / SC + 0.5 * m2 * ((U - p) / SC) ** 2
                        cs.append((ql, (qh - ql) / ((U - L) / SC), L / SC))
        out[t] = cs
    return out
def true_slack(box, cons, extra_starts=()):
    bnds, A0, c0 = polycons(box, cons)
    lo = np.array([x[0] for x in bnds]); hi = np.array([x[1] for x in bnds])
    starts = [0.5 * (lo + hi)] + list(extra_starts)
    best = math.inf
    consl = [] if A0 is None else [{"type": "ineq", "fun": (lambda g, A0=A0, c0=c0: c0 - A0 @ g), "jac": (lambda g, A0=A0: -A0)}]
    for x0 in starts:
        x0 = np.clip(x0, lo, hi)
        try:
            r = minimize(Fgrad, x0, jac=True, method="SLSQP", bounds=bnds, constraints=consl, options={"maxiter": 200, "ftol": 1e-15})
            g = np.clip(r.x, lo, hi)
            if A0 is None or (A0 @ g <= c0 + 1e-9).all(): best = min(best, F(g))
        except Exception: pass
        if A0 is None or (A0 @ x0 <= c0 + 1e-9).all(): best = min(best, F(x0))
    return (best - cNf) / cNf
def quad_min(box, cons):
    """the non-convex second-order model: min over the cell of b.g + sum a_t q_t(s_t), q_t at the range midpoint with
    m_t = min w'' on the range (q_t <= w); local SLSQP from the centre and 8 random box vertices (optimistic)"""
    I = iv(box, cons); P0 = np.zeros(NP); W0 = np.zeros(NP); D0 = np.zeros(NP); M0 = np.zeros(NP)
    for t in ACT:
        L, U = I[t]; pm = (L + U) // 2; P0[t] = pm / SC; W0[t] = float(w(pm / SC)); D0[t] = float(w1(pm / SC))
        M0[t] = w2min(L, U) - 1e-9
    def fq(g):
        s = INC @ g; ds = s - P0
        return float(b @ g + a @ (W0 + D0 * ds + 0.5 * M0 * ds * ds)), b + INC.T @ (a * (D0 + M0 * ds))
    bnds, A0, c0 = polycons(box, cons)
    lo = np.array([x[0] for x in bnds]); hi = np.array([x[1] for x in bnds])
    consl = [] if A0 is None else [{"type": "ineq", "fun": (lambda g: c0 - A0 @ g), "jac": (lambda g: -A0)}]
    starts = [0.5 * (lo + hi)] + [np.where(rng.random(Q) < 0.5, lo, hi) for _ in range(8)]
    best = math.inf
    for x0 in starts:
        try:
            r = minimize(fq, x0, jac=True, method="SLSQP", bounds=bnds, constraints=consl, options={"maxiter": 100, "ftol": 1e-14})
            g = np.clip(r.x, lo, hi)
            if A0 is None or (A0 @ g <= c0 + 1e-9).all(): best = min(best, fq(g)[0])
        except Exception: pass
        if A0 is None or (A0 @ x0 <= c0 + 1e-9).all(): best = min(best, fq(x0)[0])
    return (best - cNf) / cNf
def cert_bound(box, cons, mc):
    """float value of the leaf's own certificate (constant = exact float min on the range, tangents at the payload's grid
    positions), minimised over the cell polytope by LP; multipliers implicit, so this is >= the engine's bound"""
    I = iv(box, cons); coef = b.copy(); const = 0.0
    for t in ACT:
        kap, j1, j2, lam = mc[t]; L, U = I[t]
        c_, l1, l2 = ((0, LS, 0) if kap == 1 else (LS - lam, lam, 0) if kap == 2 else (0, LS - lam, lam) if kap == 3 else (LS, 0, 0))
        if c_: const += a[t] * c_ / LS * wmin(L, U)
        for lk, jj in ((l1, j1), (l2, j2)):
            if not lk: continue
            p = gpt(L, U, jj)
            if p is None: return float("nan")
            wp = float(w(p / SC)); dp = float(w1(p / SC))
            const += a[t] * lk / LS * (wp - dp * p / SC); coef += a[t] * lk / LS * dp * INC[t]
    bnds, A0, c0 = polycons(box, cons)
    res = linprog(coef, A_ub=A0, b_ub=c0, bounds=bnds, method="highs")
    if res.status != 0: return float("nan")
    return (res.fun + const - cNf) / cNf
def curv_class(L, U):
    m, M = w2min(L, U), w2max(L, U)
    return "convex" if m >= 0 else ("concave" if M <= 0 else "mixed")
# ---------------- basins
BJd = json.load(open(BJ)); words = []; words2 = []
if "basins_excess_le_2e-4" in BJd:
    words = [np.array(x["gaps"]) for x in BJd["basins_excess_le_2e-4"]]; words2 = list(words)
elif "root_hints_near_binding" in BJd:
    # window-scope's t-files: local minima at <= 1e-2 relative excess, sorted; the first is the unique one at <= 2e-4
    hs = [np.array(x["gaps"] if isinstance(x, dict) else x) for x in BJd["root_hints_near_binding"]]
    words = hs[:int(BJd.get("basin_counts", {}).get("2e-04", 1))]; words2 = hs
words = words + [wd[::-1] for wd in words]; words2 = words2 + [wd[::-1] for wd in words2]
WORDS = np.array(words); WORDS2 = np.array(words2)
# ---------------- tree walk
D = pickle.load(open(DUMP, "rb"))
leaves = []; parents = []
def walk(nd, depth):
    if nd[0] == "leaf":
        leaves.append((nd[1], nd[2], nd[3], nd[4], depth)); return True
    _, box, cons, ax, A_, B_ = nd[:6]
    la = walk(A_, depth + 1); lb = walk(B_, depth + 1)
    if A_[0] == "leaf" and B_[0] == "leaf": parents.append((box, cons, ax, depth))
    return False
for tr in D["trees"]: walk(tr, 0)
print(f"{DUMP}: {len(leaves)} leaves, {len(parents)} last-level parents; cN {cN}; words {len(WORDS)}", flush=True)
t0 = time.time()
# ---------------- (A) leaf anatomy: cheap stats on all leaves, slack measures on a sample
recs = []
kinds = {}
for (box, cons, kind, pay, depth) in leaves:
    widths = [(u - l) / SC for (l, u) in box]; ctr = np.array([(l + u) / 2 / SC for (l, u) in box])
    ex = F(ctr) / cTrue - 1
    dist = float(np.min(np.linalg.norm(WORDS - ctr, axis=1))) if len(WORDS) else float("nan")
    dist2 = float(np.min(np.linalg.norm(WORDS2 - ctr, axis=1))) if len(WORDS2) else float("nan")
    rec = dict(kind=kind, depth=depth, widths=widths, excess=ex, dist=dist, dist2=dist2)
    if kind == 6 and pay is not None:
        mc = pay[0]; I = iv(box, cons); ks = []; cc = []
        for t in ACT:
            ks.append(mc[t][0]); cc.append(curv_class(*I[t]))
        rec["kap"] = ks; rec["curv"] = cc
    recs.append(rec)
idx6 = [k for k, r in enumerate(recs) if r["kind"] == 6]
samp = rng.choice(idx6, size=min(NLS, len(idx6)), replace=False)
for n_, k in enumerate(samp):
    box, cons, kind, pay, depth = leaves[k]
    recs[k]["cert_slack"] = cert_bound(box, cons, pay[0])
    recs[k]["true_slack"] = true_slack(box, cons)
    if n_ % 500 == 0: print(f"  leaf sample {n_}/{len(samp)} ({time.time() - t0:.0f}s)", flush=True)
# ---------------- (B) parents
psamp = rng.choice(len(parents), size=min(NPS, len(parents)), replace=False)
prec = []
for n_, k in enumerate(psamp):
    box, cons, ax, depth = parents[k]
    widths = [(u - l) / SC for (l, u) in box]; ctr = np.array([(l + u) / 2 / SC for (l, u) in box])
    st = true_slack(box, cons)
    l0 = lp_relax(box, cons, cands_first(box, cons, const_only=True))
    l1 = lp_relax(box, cons, cands_first(box, cons))
    l2 = lp_relax(box, cons, cands_first(box, cons, so=True))
    l3 = quad_min(box, cons)
    dist = float(np.min(np.linalg.norm(WORDS - ctr, axis=1))) if len(WORDS) else float("nan")
    prec.append(dict(depth=depth, ax=int(ax), widths=widths, true_slack=st, lp0=l0, lp1=l1, lp2=l2, nso=l3, dist=dist,
                     excess=F(ctr) / cTrue - 1))
    if n_ % 250 == 0: print(f"  parent sample {n_}/{len(psamp)} ({time.time() - t0:.0f}s)", flush=True)
json.dump(dict(dump=DUMP, weights=WJ, delta=DELTA, cN=cN, nleaves=len(leaves), nparents=len(parents), leaves=recs,
               leaf_sample=[int(k) for k in samp], parents=prec), open(OUT, "w"))
print(f"wrote {OUT} ({time.time() - t0:.0f}s)", flush=True)
