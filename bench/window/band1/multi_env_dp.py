"""Joint environment DP for a FIXED multi-pair geometry (line model, certificate v1, P_h dropped):
  LP_total >= Q_pp + T_pp + V_env,
  Q_pp  = int_{-1}^{1} qf ( |sum_p A_p e(a s_p)|^2 - 4 |sum_p e(a s_p)|^2 ),  A_p = 2 cosh(2 pi a y_p)      (exact, quadrature)
  T_pp  = sum_{p != q} 4 g(s_p - s_q)                                                                     (pair doubles, R convention)
  V_env = min over environment chains on the line of
          sum_b m_b [ Phi(x_b) + 4 sum_p g(x_b - s_p) ] + sum_consecutive 2 m m' g + half-bin cluster charges,
          Phi(x) = sum_p phi_{y_p}(x - s_p)  (all pairs' fields: the long-range coupling enters as a one-body potential).
The chain DP and cluster charge are those of crowd_dp2.py, in absolute units, on cells of width 1/RES near pairs and coarser far
away; field cell bounds from the c_j tables (min over the cell's grid points + second-derivative allowance + series remainder),
g from the certified block minima; beyond the DP range the half-bin tail bound with the summed |phi| tails.
usage: python3 multi_env_dp.py GEOMS.json [names] [RES]"""
import sys, json, time, numpy as np
GF = sys.argv[1]; NAMES = sys.argv[2].split(',') if len(sys.argv) > 2 and sys.argv[2] else None; RES = int(sys.argv[3]) if len(sys.argv) > 3 else 256
sys.argv = ['crowd_dp.py', '128', '8', '', '1e-8']
import crowd_dp as C
a_half = float(C.gmin_range(np.array([0.0]), np.array([0.5]))[0])
xg, wg = np.polynomial.legendre.leggauss(400); al0 = (xg + 1) / 2; wa0 = wg / 2
def Qpp(s, ys, npiece=None):
    span = max(1.0, float(np.max(s) - np.min(s))); npc = npiece or int(8 * span + 16); tot = 0.0
    edges = np.linspace(0, 1, npc + 1)
    for a0, a1 in zip(edges[:-1], edges[1:]):
        a = a0 + (a1 - a0) * al0; w = (a1 - a0) * wa0; q = C.qf(np.minimum(a, 1 - 1e-13))
        E = np.exp(2j * np.pi * np.outer(a, s)); A = 2 * np.cosh(2 * np.pi * np.outer(a, ys))
        tot += float(np.sum(w * q * (np.abs((E * A).sum(1)) ** 2 - 4 * np.abs(E.sum(1)) ** 2)))
    return 2 * tot
def phi_table(y):
    pw = np.array([y ** (2 * j) for j in range(1, C.J + 1)])          # phi = y^2 psi = sum_j y^{2j} c_j
    tab = pw @ C.Cg; d2 = float(pw @ C.Cj2); rem = y ** 2 * C.series_rem(y ** 2)
    return tab, d2, rem
def cell_lower_phi(lo, hi, s, y, tabinfo):
    """lower bound of phi_y(x - s) over x in [lo, hi] (arrays), via |u| intervals on the table grid"""
    tab, d2, rem = tabinfo; eta = C.ETA_C; n = len(tab)
    a = lo - s; b = hi - s
    ua = np.where((a <= 0) & (b >= 0), 0.0, np.minimum(np.abs(a), np.abs(b))); ub = np.maximum(np.abs(a), np.abs(b))
    ia = np.floor(ua / eta).astype(np.int64); ib = np.ceil(ub / eta).astype(np.int64)
    out = np.full(len(lo), np.inf); inside = ib < n
    width = int(np.max(ib[inside] - ia[inside])) if np.any(inside) else 0
    for w in range(width + 1):
        idx = np.minimum(ia + w, ib); ok = inside & (idx < n)
        out[ok] = np.minimum(out[ok], tab[idx[ok]])
    out = out - d2 * eta ** 2 / 8 - rem - 1e-12
    A2, A3 = C.Btail(y); far = ~inside
    if np.any(far):
        # beyond the table: phi(u) = 8 p'(1) cos(2 pi u)/(2 pi u)^2 + R, |R| <= A3 y^2/u^3 (three integrations by parts), 8 p'(1)/(2 pi)^2 = -(A2/1.05) y^2
        u0, u1 = ua[far], ub[far]; mc = max_cos_on(u0, u1)
        lead = -(A2 / 1.05) * y ** 2 * np.where(mc >= 0, mc / u0 ** 2, mc / u1 ** 2)
        out[far] = lead - A3 * y ** 2 / u0 ** 3
    return out
def max_cos_on(u0, u1):
    """max of cos(2 pi u) on [u0, u1] (arrays, u1 - u0 <= 1/2)"""
    has_int = np.floor(u1) >= np.ceil(u0)
    return np.where(has_int, 1.0, np.maximum(np.cos(2 * np.pi * u0), np.cos(2 * np.pi * u1)))

# ---------------- density term (P_h, dual / test-function form) ----------------
# For any test function v with v-hat supported where h-hat > 0 (here |a| >= A0, so no DC term):
#   P_h >= 2 sum_a m_a v(x_a) - int |v-hat|^2 / h-hat     (h-hat |S|^2 >= 2 Re(c-bar S) - |c|^2 / h-hat, termwise).
# With v = t (h-hat_W S_pairs)^check, S_pairs = sum_p 2 e(a s_p), h-hat_W = h-hat * W (W: 0 below A0, linear to 1 at A1):
#   P_h >= 4 t sum_env m_b sum_p h_W(x_b - s_p)  +  4 (2t - t^2) sum_{p,q} h_W(s_p - s_q),   h_W = (h-hat_W)^check (even, real).
import os
TDENS = float(os.environ.get('MEDP_T', '0')); A0, A1 = 0.5, 0.75
TLOW = float(os.environ.get('MEDP_TLOW', '0')); DPROF = float(os.environ.get('MEDP_DPROF', '0')); XR = float(os.environ.get('MEDP_XR', '40')); BETA = float(os.environ.get('MEDP_BETA', str(1 / 32)))
FAR = [float(v) for v in os.environ.get('MEDP_FAR', '').split(',') if v]   # round 3: far profile f = lam (D/(D + d_out))^kappa beyond R
assert FAR == [] or (len(FAR) == 3 and FAR[0] >= 0) and DPROF <= 0
# low band (density): v_low = t_low (w - int w / N), w = 1_R * k_beta >= 0, k_beta = beta sinc^2(beta x) (k-hat = triangle on [-beta, beta]);
#   P_h >= 2 t_low [ sum_a m_a w(x_a) - int w ] - t_low^2 Q,  Q = int_{a != 0} |w-hat|^2 / h-hat   (total mass N, mean-zero test function)
REFM = float(os.environ.get('MEDP_REF', '-1'))   # >= 0: test function built from the reference configuration (pairs + environment) within REFM of the cluster
def hhat_W(a):
    a = np.abs(np.asarray(a, float)); gh = np.interp(a, np.arange(len(C.yk) + 1) * C.Dk, np.concatenate([C.yk, [0.0]]), right=0.0)
    q = np.where(a < 1, C.qf(np.minimum(a, 1 - 1e-13)), 0.0); W = np.clip((a - A0) / (A1 - A0), 0.0, 1.0)
    return (q - gh) * W
if TDENS > 0:
    bk = np.unique(np.concatenate([np.arange(0, 97) * C.Dk, [A0, A1, 1.0]])); bk = bk[(bk >= A0) & (bk <= 3.0)]
    xq, wq = np.polynomial.legendre.leggauss(24)
    an = np.concatenate([(b0 + b1) / 2 + (b1 - b0) / 2 * xq for b0, b1 in zip(bk[:-1], bk[1:])])
    wn = np.concatenate([(b1 - b0) / 2 * wq for b0, b1 in zip(bk[:-1], bk[1:])]); hn = hhat_W(an)
    assert np.all(hn >= -1e-15), 'h-hat_W must be >= 0'
    UW = np.arange(0, C.X + 2, 1 / 1024)
    HW = np.empty(len(UW))
    for i in range(0, len(UW), 4000): HW[i:i + 4000] = 2 * (np.cos(2 * np.pi * np.outer(UW[i:i + 4000], an)) @ (hn * wn))
    M2W = 2 * float(np.sum(hn * wn * (2 * np.pi * an) ** 2))
    UW2 = np.arange(0, 300.0, 1 / 256); HW2 = np.empty(len(UW2))     # 24-node quadrature exact to 1e-10 for u <= 300 (aliases beyond ~400; checked against 400 nodes)
    for i in range(0, len(UW2), 4000): HW2[i:i + 4000] = 2 * (np.cos(2 * np.pi * np.outer(UW2[i:i + 4000], an)) @ (hn * wn))
    af_ = np.linspace(A0, 3.0, 400001); dW = np.gradient(hhat_W(af_), af_)
    CW = 1.05 * 2 * float(np.sum(np.abs(np.diff(dW))) + abs(dW[0]) + abs(dW[-1])) / (2 * np.pi) ** 2      # |h_W(u)| <= CW / u^2
    print('density term: t = %.3f, band |a| >= %.2f (taper to %.2f); h_W(0) = %.4f, |h_W\'\'| <= %.2f, tail |h_W(u)| <= %.4f/u^2'
          % (TDENS, A0, A1, HW[0], M2W, CW), flush=True)
def hW_exact(u):
    u = np.abs(np.atleast_1d(np.asarray(u, float)))
    return np.array([2 * float(np.sum(hn * wn * np.cos(2 * np.pi * an * x))) for x in u])
def cell_lower_hW(lo, hi, s):
    a = lo - s; b = hi - s
    ua = np.where((a <= 0) & (b >= 0), 0.0, np.minimum(np.abs(a), np.abs(b))); ub = np.maximum(np.abs(a), np.abs(b))
    eta = 1 / 1024; n = len(HW); ia = np.floor(ua / eta).astype(np.int64); ib = np.ceil(ub / eta).astype(np.int64)
    out = np.full(len(lo), np.inf); inside = ib < n
    width = int(np.max(ib[inside] - ia[inside])) if np.any(inside) else 0
    for w in range(width + 1):
        idx = np.minimum(ia + w, ib); ok = inside & (idx < n); out[ok] = np.minimum(out[ok], HW[idx[ok]])
    out = out - M2W * eta ** 2 / 8 - 1e-12
    far = ~inside
    if np.any(far):
        eta2 = 1 / 256; n2 = len(HW2); ia2 = np.floor(ua[far] / eta2).astype(np.int64); ib2 = np.ceil(ub[far] / eta2).astype(np.int64)
        o2 = np.full(int(far.sum()), np.inf); ins2 = ib2 < n2
        wd = int(np.max(ib2[ins2] - ia2[ins2])) if np.any(ins2) else 0
        for w in range(wd + 1):
            idx = np.minimum(ia2 + w, ib2); ok = ins2 & (idx < n2); o2[ok] = np.minimum(o2[ok], HW2[idx[ok]])
        o2 = o2 - M2W * eta2 ** 2 / 8 - 1e-9; o2[~ins2] = -CW / ua[far][~ins2] ** 2
        out[far] = o2
    return out
def run(geo):
    s = np.array(geo['pairs']); ys = np.array(geo['depths']); P = len(s); t0 = time.time()
    xmin, xmax = s.min(), s.max(); XL = float(__import__("os").environ.get("MEDP_XL", "48"))
    # cells: 1/RES within 3 of a pair, 1/64 within 16, 1/16 beyond (to XL past the outermost pair)
    edges = [np.floor((xmin - XL) * 16) / 16]
    while edges[-1] < xmax + XL:
        x = edges[-1]; dmin = float(np.min(np.abs(s - x)))
        h = 1 / RES if dmin < 3 else (1 / 64 if dmin < 16 else (1 / 16 if dmin < 512 else 1 / 4))
        nxt = np.floor(x * (1 / h) + 1e-9) / (1 / h) + h; edges.append(round(nxt, 12))
    edges = np.array(edges); lo, hi = edges[:-1], edges[1:]; K = len(lo)
    hb = np.floor(lo * 2 + 1e-9).astype(int); assert np.all(np.floor(hi * 2 - 1e-9).astype(int) == hb)
    tabs = {}
    Phi = np.zeros(K); G4 = np.zeros(K)
    for p in range(P):
        y = round(float(ys[p]), 12)
        if y not in tabs: tabs[y] = phi_table(y)
        Phi += cell_lower_phi(lo, hi, s[p], y, tabs[y])
        da = np.where((lo - s[p] <= 0) & (hi - s[p] >= 0), 0.0, np.minimum(np.abs(lo - s[p]), np.abs(hi - s[p])))
        db = np.maximum(np.abs(lo - s[p]), np.abs(hi - s[p]))
        G4 += 4 * C.gmin_range(da, np.minimum(db, C.X + 1))
        if TDENS > 0 and REFM < 0: G4 += 4 * TDENS * cell_lower_hW(lo, hi, s[p])
    if TDENS > 0 and REFM >= 0:
        env = np.array(geo['env']); envw = env[(env >= xmin - REFM) & (env <= xmax + REFM)]
        refx = np.concatenate([s, envw]); refm = np.concatenate([np.full(P, 2.0), np.ones(len(envw))])
        for xa, ma in zip(refx, refm): G4 += 2 * TDENS * ma * cell_lower_hW(lo, hi, xa)
    lowconst = 0.0
    if TLOW > 0:
        # w = sum_i (f_i / 8) k_beta(x - y_i) >= 0 with k_beta = beta sinc^2(beta x): band-limited to |a| <= beta for ANY weights f_i;
        # f = 1 on R = [xmin - XR, xmax + XR] and, if DPROF > 0, D^2/(D^2 + d^2) at distance d outside R (to the DP range); Q and int w are
        # computed for this same discrete w, so the dual bound P_h >= 2t(sum m w - int w) - t^2 Q holds exactly for it.
        Rl, Rr = xmin - XR, xmax + XR; ext = (XL if (DPROF > 0 or FAR) else 0.0)
        yq = np.arange(Rl - ext, Rr + ext, 1 / 8) + 1 / 16
        dout = np.maximum(np.maximum(Rl - yq, yq - Rr), 0.0); fq = np.ones(len(yq)) if DPROF <= 0 else DPROF ** 2 / (DPROF ** 2 + dout ** 2)
        if FAR: fq = np.where(dout > 0, FAR[0] * (FAR[1] / (FAR[1] + dout)) ** FAR[2], 1.0)
        def wfun(x):
            x = np.atleast_1d(x); out = np.empty(len(x))
            for i in range(0, len(x), 1000): out[i:i + 1000] = (BETA * np.sinc(BETA * (x[i:i + 1000, None] - yq[None, :])) ** 2) @ fq / 8
            return out
        # cell lower bound of w (f >= 0): (a) midpoint - |w'| h/2 with |w'| <= max f * TV(k_beta), TV(k_beta) = 2 beta (1 + 2 sum_n 1/(pi^2 (n+1/2)^2)) < 2.4 beta
        # (round-2 code used 2 beta, slightly too small); (b) min of the endpoint values - |w''| h^2/8 with |w''| <= sum f/8 * max|k''|,
        # max|k''| = int (2 pi a)^2 k-hat = (2 pi)^2 beta^3 / 6 (k-hat = triangle >= 0).  Take the larger of (a), (b), 0.
        we = wfun(edges); wc = wfun((lo + hi) / 2); M2w = float(np.sum(fq) / 8) * (2 * np.pi) ** 2 * BETA ** 3 / 6
        wlo = np.maximum(np.maximum(wc - 2.4 * BETA * float(fq.max()) * (hi - lo) / 2, np.minimum(we[:-1], we[1:]) - M2w * (hi - lo) ** 2 / 8), 0.0)
        G4 += 2 * TLOW * wlo
        al_ = np.linspace(-BETA, BETA, 40001)[1:-1]; al_ = al_[np.abs(al_) > 1e-12]
        hh = np.interp(np.abs(al_), np.arange(len(C.yk) + 1) * C.Dk, np.concatenate([C.yk, [0.0]]), right=0.0); hh = C.qf(np.abs(al_)) - hh
        Fq = np.zeros(len(al_), complex)
        for i in range(0, len(yq), 400): Fq += np.exp(-2j * np.pi * np.outer(al_, yq[i:i + 400])) @ (fq[i:i + 400] / 8)
        tri = 1 - np.abs(al_) / BETA
        Q = float(np.trapezoid(np.abs(Fq) ** 2 * tri ** 2 / hh, al_))
        lowconst = 4 * TLOW * float(np.sum(wfun(s))) - 2 * TLOW * float(np.sum(fq) / 8) - TLOW ** 2 * Q
    one = {m: m * (Phi + G4) for m in (1, 2)}
    selfg = C.gmin_range(np.zeros(K), hi - lo)
    # tails beyond the range: half-bins with the summed |phi| bound (needs Phi_tot <= 2 a)
    tail = 0.0
    for side in (-1, 1):
        u0 = (xmin - edges[0]) if side < 0 else (edges[-1] - xmax)
        jj = np.arange(0, 400000) / 2.0 + u0
        Pt = np.zeros(len(jj)); Pd = np.zeros(len(jj)); coh = 0j; Wsum = 0.0; A3sum = 0.0
        for p in range(P):
            A2, A3 = C.Btail(ys[p]); off = (s[p] - xmin if side < 0 else xmax - s[p]); dist = jj + off
            Pt += ys[p] ** 2 * (A2 / dist ** 2 + A3 / dist ** 3)
            if TDENS > 0 and REFM < 0: Pd += 4 * TDENS * CW / dist ** 2
            coh += ys[p] ** 2 * A2 * np.exp(2j * np.pi * s[p]); Wsum += ys[p] ** 2 * A2 * 2 * off; A3sum += ys[p] ** 2 * A3
        # coherent far-field bound: the leading IBP terms share the phase e(x - s_p), so |sum_p| <= |sum_p w_p e(s_p)|/d^2 + (2 W-spread + A3)/d^3
        Pcoh = abs(coh) / jj ** 2 + (Wsum + A3sum) / jj ** 3
        Pt = np.minimum(Pt, Pcoh) + Pd
        if TDENS > 0 and REFM >= 0:
            for xa, ma in zip(refx, refm):
                dist = jj + (xa - xmin if side < 0 else xmax - xa); Pt += 2 * TDENS * ma * CW / np.maximum(dist, 0.5) ** 2
        assert np.all(Pt <= 2 * a_half)
        tail += -2 * float(Pt.sum()) - 4 * float(Pt[-1]) * jj[-1]
    PC = 24; W = np.full((3, PC + 1, K), np.inf); NX = np.full((3, PC + 1, K, 3), -1, dtype=np.int64)
    for k in range(K - 1, -1, -1):
        kk = np.arange(k + 1, K); same = hb[kk] == hb[k]; ko, ks = kk[~same], kk[same]
        go = C.gmin_range(np.maximum(lo[ko] - hi[k], 0.0), np.minimum(hi[ko] - lo[k], C.X + 1)) if len(ko) else None
        gs = C.gmin_range(np.maximum(lo[ks] - hi[k], 0.0), hi[ks] - lo[k]) if len(ks) else None
        A = {}; AA = {}
        for m in (1, 2):
            best = 0.0; arg = (-1, -1, -1)                             # no further environment point in range (tail added separately)
            for m2 in (1, 2):
                if len(ko):
                    c = 2 * m * m2 * go + one[m2][ko] + W[m2, 0, ko]; i = int(np.argmin(c)); v = float(c[i])
                    if v < best: best = v; arg = (int(ko[i]), m2, 0)
            A[m] = best; AA[m] = arg
        for pp in range(PC, -1, -1):
            for m in (1, 2):
                pn = min(pp + m, PC); best = A[m]; arg = AA[m]
                for m2 in (1, 2):
                    if len(ks):
                        c = 2 * m * m2 * gs + one[m2][ks] + 2 * a_half * m2 * pp + W[m2, pn, ks]; i = int(np.argmin(c)); v = float(c[i])
                        if v < best: best = v; arg = (int(ks[i]), m2, pn)
                    base = 2 * m * m2 * selfg[k] + one[m2][k] + 2 * a_half * m2 * pp
                    if pn == pp:
                        assert base > 0, 'cap too small at k=%d' % k
                    else:
                        if base + W[m2, pn, k] < best: best = base + W[m2, pn, k]; arg = (k, m2, pn)
                W[m, pp, k] = best; NX[m, pp, k] = arg
    Venv = min(0.0, float(min(np.min(one[m] + W[m, 0]) for m in (1, 2))))
    global LAST_CHAIN
    st = min(((float(one[m][k] + W[m, 0, k]), k, m) for m in (1, 2) for k in range(K)))
    chain = []; v0, k, m = st; pp = 0
    if v0 < 0:
        chain.append(((lo[k] + hi[k]) / 2, m))
        while True:
            k2, m2, p2 = NX[m, pp, k]
            if k2 < 0 or len(chain) > 2000: break
            chain.append(((lo[k2] + hi[k2]) / 2, m2)); k, m, pp = k2, m2, p2
    LAST_CHAIN = chain
    q = Qpp(s, ys); tpp = 4 * float(sum(C.gfun(np.array([abs(s[i] - s[j])]))[0] for i in range(P) for j in range(P) if i != j))
    dconst = 0.0
    if TDENS > 0:
        if REFM < 0:
            D = np.abs(s[:, None] - s[None, :]).ravel(); dconst = 4 * (2 * TDENS - TDENS ** 2) * float(np.sum(hW_exact(D)))
        else:   # 2 sum_pairs 2 v(s_p) - ||v||^2,  v = t sum_{a in ref} m_a h_W(. - x_a)
            Dpr = np.abs(s[:, None] - refx[None, :]); Drr = np.abs(refx[:, None] - refx[None, :])
            dconst = 4 * TDENS * float(np.sum(hW_exact(Dpr.ravel()).reshape(Dpr.shape) * refm[None, :])) \
                     - TDENS ** 2 * float(refm @ hW_exact(Drr.ravel()).reshape(Drr.shape) @ refm)
    dconst += lowconst
    lb = q + tpp + Venv + tail + dconst; S2 = float(np.sum(ys ** 2))
    return lb, q, tpp, Venv, tail, S2, K, time.time() - t0, dconst
if __name__ == '__main__':
    geoms = json.load(open(GF))
    for geo in geoms:
        if NAMES and geo['name'] + '@%g' % geo['Y'] not in NAMES and geo['name'] not in NAMES: continue
        lb, q, tpp, venv, tail, S2, K, dt, dconst = run(geo)
        print('%-8s N=%-3d Y=%.1f P=%2d t=%.2f tlow=%.4f: joint lower bound %+.4f (/sum y^2 %+.3f) = Q_pp %.4f + T_pp %.4f + V_env %+.4f + tails %+.4f + density const %+.4f | exact periodic LP %.4f (P_h %.3f) | %d cells %.0fs'
              % (geo['name'], geo['N'], geo['Y'], len(geo['pairs']), TDENS, TLOW, lb, lb / S2, q, tpp, venv, tail, dconst, geo['LP_total'], geo['split']['P_h'], K, dt), flush=True)
