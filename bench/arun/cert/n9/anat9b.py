"""bridge-port 2026-10-10: ANATOMY.md follow-up.  At sampled last-level parents, the ideal first-order LP (exact constants,
exactly valid tangents at the engine's grid positions) is solved and its relaxation error a_t (w(s_t*) - z_t*) at the LP
point is broken down by pair span j - i and by the term's minorant kind (constant only vs a tangent available).
Usage: python3 anat9b.py DUMP.pkl WEIGHTS.json DELTA BASINS.json OUT.json NPARENT_SAMPLE"""
import sys
src = open(__file__.replace("anat9b.py", "anat9.py")).read().split("# ---------------- basins")[0]
sys.argv = sys.argv[:6] + ["0", sys.argv[6]]
exec(src)
NPS = int(sys.argv[7])
D = pickle.load(open(DUMP, "rb")); parents = []
def walk(nd, depth):
    if nd[0] == "leaf": return
    _, box, cons, ax, A_, B_ = nd[:6]
    walk(A_, depth + 1); walk(B_, depth + 1)
    if A_[0] == "leaf" and B_[0] == "leaf": parents.append((box, cons, ax, depth))
for tr in D["trees"]: walk(tr, 0)
def lp_x(box, cons, cands):
    bnds, A0, c0 = polycons(box, cons); rows = []; rhs = []
    for t in ACT:
        for (v, d, p) in cands[t]:
            r = np.zeros(Q + NP); r[:Q] = d * INC[t]; r[Q + t] = -1.0; rows.append(r); rhs.append(-(v - d * p))
    if A0 is not None:
        for k in range(len(A0)):
            r = np.zeros(Q + NP); r[:Q] = A0[k]; rows.append(r); rhs.append(c0[k])
    zb = [(None, None) if aN[t] > 0 else (0, 0) for t in range(NP)]
    res = linprog(np.concatenate([b, a]), A_ub=np.array(rows), b_ub=np.array(rhs), bounds=bnds + zb, method="highs")
    return res
psamp = rng.choice(len(parents), size=min(NPS, len(parents)), replace=False)
span_err = np.zeros(n); kind_err = {"const_only": 0.0, "tangent": 0.0}; tot_loss = []; nfail = 0
per_parent = []
for k in psamp:
    box, cons, ax, depth = parents[k]
    cs = cands_first(box, cons)
    res = lp_x(box, cons, cs)
    if res.status != 0: continue
    x = res.x; g = x[:Q]; s = INC @ g
    errs = np.zeros(NP)
    for t in ACT: errs[t] = a[t] * (float(w(s[t])) - x[Q + t])
    val = (res.fun - cNf) / cNf
    if val < 0: nfail += 1
    per_parent.append(dict(lp1=val, err_total=float(errs.sum() / cNf), err_by_span=[float(sum(errs[t] for t in ACT if PAIRS[t][1] - PAIRS[t][0] == sp) / cNf) for sp in range(1, n)]))
    for t in ACT:
        sp = PAIRS[t][1] - PAIRS[t][0]; span_err[sp] += errs[t]
        kind_err["const_only" if len(cs[t]) == 1 else "tangent"] += errs[t]
T_ = span_err.sum()
print(f"{DUMP}: {len(per_parent)} parents (LP1 < 0 in {nfail}); relaxation error at the LP point, share by pair span:",
      {sp: round(float(span_err[sp] / T_), 3) for sp in range(1, n)}, flush=True)
print("   share by candidate set:", {k_: round(v_ / T_, 3) for k_, v_ in kind_err.items()}, flush=True)
fl = [p_ for p_ in per_parent if p_["lp1"] < 0]
if fl:
    S = np.array([p_["err_by_span"] for p_ in fl]); print("   failing parents (LP1 < 0): mean error by span (units of c):",
          np.round(S.mean(axis=0), 4), "; mean total", round(float(np.mean([p_["err_total"] for p_ in fl])), 4), flush=True)
json.dump(dict(span_share={sp: float(span_err[sp] / T_) for sp in range(1, n)}, kind_share={k_: v_ / T_ for k_, v_ in kind_err.items()},
               parents=per_parent), open(OUT, "w"))
