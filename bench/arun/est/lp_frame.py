"""Round 3: optimise an n-point weighted certificate (a_ij, b_r) directly for kappa_n = (H - B)/(1 - c), c = min_{g >= lo} Fw(g).
Cutting-plane LP (HiGHS) with reflection symmetry and capacity sum_{j-i=s} a_ij <= 2; Dinkelbach outer loop on kappa;
separation by a global search of Fw (word seeds {1.04,1.97,2.93}^(n-1) + working set + random; L-BFGS-B on [lo, 40]).
The kernel is the R8 window (wfun = kfun^2), tabulated on [0, 420] at step 2e-5 with linear interpolation for the search;
final c is re-evaluated with the exact kernel at the global-search minimiser.
usage: python3 lp_frame.py N LO OUT_PREFIX [MAXROUNDS]"""
import sys, json, math, time, itertools, numpy as np
from scipy.optimize import minimize, linprog
n = int(sys.argv[1]); LO = float(sys.argv[2]); OUT = sys.argv[3]; MAXR = int(sys.argv[4]) if len(sys.argv) > 4 else 80
cn = json.load(open('/Users/samuellavery/work/riemann-submission/bench/window/rwin8.json'))['cnum']
cw = np.array(cn, float) / cn[0]; om = np.concatenate([[math.sqrt(2.0)], 2 * np.pi * np.arange(1, len(cw))])
def Kraw(x):
    x = np.asarray(x, float)[..., None]
    return ((np.sinc((om - 2 * np.pi * x) / 2 / np.pi) + np.sinc((om + 2 * np.pi * x) / 2 / np.pi)) / 2 * cw).sum(-1)
K0 = float(Kraw(0.0))
def wex(x): return (Kraw(x) / K0) ** 2
HSTEP = 2e-5; XT = np.arange(0, 420 + HSTEP, HSTEP)
WT = np.empty(len(XT))
for i in range(0, len(XT), 200000): WT[i:i + 200000] = wex(XT[i:i + 200000])
DWT = np.gradient(WT, HSTEP)
def wtab(x): return np.interp(x, XT, WT)
def dwtab(x): return np.interp(x, XT, DWT)
H = 0.67216841056411887478          # exact H_W of the R8 window (hw_exact.log); MOP uses the floor 0.67216841
HLO = 0.67216841
m = n - 1
PI, PJ = np.array([(i, j) for i in range(n) for j in range(i + 1, n)]).T
NP = len(PI); SPAN = PJ - PI
# variable vector: [a_0..a_{NP-1}, b_0..b_{m-1}, c]
def mirror_pair(k):
    i, j = PI[k], PJ[k]; ii, jj = n - 1 - j, n - 1 - i
    return int(np.where((PI == ii) & (PJ == jj))[0][0])
MP = np.array([mirror_pair(k) for k in range(NP)])
def Fw_parts(g):
    p = np.concatenate([[0.0], np.cumsum(g)]); d = p[PJ] - p[PI]; return d
def Fw_val(g, a, b, exact=False):
    d = Fw_parts(g); return float(b @ g + a @ (wex(d) if exact else wtab(d)))
COV = np.array([[1.0 if (PI[k] <= r < PJ[k]) else 0.0 for k in range(NP)] for r in range(m)])   # d_k depends on g_r
def Fw_grad(g, a, b):
    d = Fw_parts(g); return float(b @ g + a @ wtab(d)), b + COV @ (a * dwtab(d))
LASTMINS = []
def global_min(a, b, seeds, rng, nrand=200):
    """global minimum by multi-start; all distinct local minima are kept in LASTMINS (sorted)"""
    global LASTMINS
    best = (np.inf, None); bounds = [(LO, 40.0)] * m; mins = {}
    starts = list(seeds) + [rng.uniform(LO, LO + 3.2, m) for _ in range(nrand)]
    for g0 in starts:
        g0 = np.clip(np.asarray(g0, float), LO, 40.0)
        r = minimize(lambda g: Fw_grad(g, a, b), g0, jac=True, method='L-BFGS-B', bounds=bounds, options={'ftol': 1e-15, 'gtol': 1e-11, 'maxiter': 2000})
        key = tuple(np.round(r.x, 3))
        if key not in mins or r.fun < mins[key][0]: mins[key] = (float(r.fun), r.x.copy())
        if r.fun < best[0]: best = (float(r.fun), r.x.copy())
    LASTMINS = sorted(mins.values(), key=lambda v: v[0])
    return best
WORDS = [np.array(w) for w in itertools.product((1.04, 1.97, 2.93), repeat=m)]
def solve_lp(G, t):
    nv = NP + m + 1
    cobj = np.zeros(nv); cobj[NP:NP + m] = 1.0; cobj[-1] = -t          # minimise B - t c
    Aub = []; bub = []
    for g in G:                                                         # c - Fw(g) <= 0
        d = Fw_parts(g); row = np.zeros(nv); row[:NP] = -wex(d); row[NP:NP + m] = -np.asarray(g); row[-1] = 1.0; Aub.append(row); bub.append(0.0)
    for s in range(1, n):                                               # capacity
        row = np.zeros(nv); row[:NP] = (SPAN == s).astype(float); Aub.append(row); bub.append(2.0)
    Aeq = []; beq = []
    for k in range(NP):
        if MP[k] > k:
            row = np.zeros(nv); row[k] = 1; row[MP[k]] = -1; Aeq.append(row); beq.append(0.0)
    for r in range(m):
        if m - 1 - r > r:
            row = np.zeros(nv); row[NP + r] = 1; row[NP + m - 1 - r] = -1; Aeq.append(row); beq.append(0.0)
    bounds = [(0, None)] * (NP + m) + [(None, None)]
    res = linprog(cobj, A_ub=np.array(Aub), b_ub=np.array(bub), A_eq=np.array(Aeq) if Aeq else None, b_eq=np.array(beq) if beq else None,
                  bounds=bounds, method='highs')
    assert res.status == 0, res.message
    x = res.x; return x[:NP], x[NP:NP + m], x[-1], res
t0 = time.time(); rng = np.random.default_rng(5)
G = [w * 1.0 for w in WORDS[::max(1, len(WORDS) // 400)]] + [np.full(m, 1.5), np.full(m, 1.04), np.full(m, 1.97)]
G = [np.maximum(g, LO) for g in G]
t = 0.6735; hist = []
for rnd in range(MAXR):
    a, b, c, res = solve_lp(G, t)
    B = float(b.sum()); kap_lp = (H - B) / (1 - c)
    seeds = [w for w in WORDS] + G[-200:]
    fmin, gmin = global_min(a, b, seeds, rng, nrand=100)
    fex = Fw_val(gmin, a, b, exact=True)
    kap_true = (H - B) / (1 - fex)
    hist.append((rnd, kap_lp, kap_true, c, fex, B, len(G)))
    print('round %2d: LP c %.9f B %.9f -> kappa_LP %.8f | true min Fw %.9f at %s -> kappa_true %.8f (H exact) | |G| %d | %.0fs'
          % (rnd, c, B, kap_lp, fex, np.round(gmin, 3), kap_true, len(G), time.time() - t0), flush=True)
    if fex < c - 1e-10:
        cuts = [g for f, g in LASTMINS if f < c - 1e-10][:60]
        for g in cuts: G.append(np.maximum(g, LO))
        t = kap_lp
    else:
        t_new = (H - B) / (1 - c)
        if abs(t_new - t) < 1e-10 and rnd > 2: break
        t = t_new
a, b, c, res = solve_lp(G, t); B = float(b.sum())
fmin, gmin = global_min(a, b, list(WORDS) + G, rng, nrand=400)
fex = Fw_val(gmin, a, b, exact=True)
kap = (H - B) / (1 - fex); kap_lo = (HLO - B) / (1 - fex)
act = [g for g in G if Fw_val(g, a, b, exact=True) - fex < 1e-7 * max(1, fex)]
print('FINAL n=%d lo=%.3f: B %.9f, true min c %.9f at %s; kappa (H exact) %.8f, kappa (H floor 0.67216841) %.8f, gain over MOP %+.3e'
      % (n, LO, B, fex, np.round(gmin, 4), kap, kap_lo, kap_lo - 0.6735478), flush=True)
print('active words (Fw within 1e-7 rel of the min): %d of %d' % (len(act), len(G)))
for g in act[:40]: print('   ', np.round(g, 3), ' gap sums', np.round(np.cumsum(g)[-1], 3))
json.dump({'n': n, 'lo': LO, 'a': a.tolist(), 'b': b.tolist(), 'pairs': [[int(i), int(j)] for i, j in zip(PI, PJ)], 'B': B, 'c_true': fex,
           'kappa_Hexact': kap, 'kappa_Hfloor': kap_lo, 'argmin': gmin.tolist(), 'active': [g.tolist() for g in act], 'hist': hist}, open(OUT + '.json', 'w'))
