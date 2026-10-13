"""Round 7: n = 9 certificates that trade kappa for basin separation.  LP in (a, b, c, t): maximise t subject to
  Fw(g) >= c            for local minima in the KEPT basin(s) (letter pattern of KEEP and its mirror),
  Fw(g) >= c + t        for local minima of every other basin,
  kT c - B >= kT - H_lo (i.e. (H_lo - B)/(1 - c) >= kT),  capacity <= 2 per rank, mirror symmetry, b_r >= 1e-6, t <= 0.05 c (cap).
Cutting planes with the word-seeded global search (lp_frame machinery); basins are identified by their letter pattern.
usage: python3 lp_sep.py KT KEEP(min|pal) OUT_PREFIX [MAXROUNDS]"""
import sys, json, time, numpy as np
from scipy.optimize import linprog
KT = float(sys.argv[1]); KEEP = sys.argv[2]; OUT_SEP = sys.argv[3]; MAXR = int(sys.argv[4]) if len(sys.argv) > 4 else 80
pre = open('lp_frame.py').read().split("t0 = time.time(); rng")[0]
pre = pre.replace("n = int(sys.argv[1]); LO = float(sys.argv[2]); OUT = sys.argv[3]", "n = 9; LO = 0.0; OUT = '/tmp/unused'")
exec(pre)
HLO = 0.67216841
LET = np.array([1.04, 1.97, 2.92, 3.9, 4.9, 5.9])
def pattern(g):
    g = np.asarray(g); idx = np.argmin(np.abs(g[:, None] - LET[None, :]), axis=1)
    idx[g < 0.7] = -1                                         # small gaps get their own letter
    return tuple(int(v) for v in idx)
def mirror_pat(p): return tuple(reversed(p))
I9 = json.load(open('cert9_inputs.json'))
if KEEP == 'min':
    kw = np.array(I9['basins_excess_le_2e-4'][0]['gaps'])
else:                                                          # the lowest palindromic near-binding word of cert9
    pal = [b for b in I9['basins_excess_le_2e-4'] if pattern(b['gaps']) == mirror_pat(pattern(b['gaps']))]
    kw = np.array(pal[0]['gaps'])
KP = {pattern(kw), mirror_pat(pattern(kw))}
print('target %.7f (LP kT = target + 3e-7), keep %s: word %s pattern(s) %s' % (KT, KEEP, np.round(kw, 3), KP), flush=True)
kT = KT + float(__import__("os").environ.get("SEP_CUSHION", "3e-7"))
KW = [None]
def solve(G, tfix=None):
    nv = NP + m + 2                      # a, b, c, t
    cobj = np.zeros(nv); cobj[-1] = -1.0
    if tfix is not None: cobj[:] = 0.0; cobj[-2] = -1.0         # second stage: maximise c at t >= tfix
    Aub, bub = [], []
    for g in G:
        d = Fw_parts(g); row = np.zeros(nv); row[:NP] = -wex(d); row[NP:NP + m] = -np.asarray(g); row[-2] = 1.0
        if pattern(g) not in KP: row[-1] = 1.0
        Aub.append(row); bub.append(0.0)
    row = np.zeros(nv); row[NP:NP + m] = 1.0; row[-2] = -kT; Aub.append(row); bub.append(HLO - kT)       # B - kT c <= H - kT
    for s in range(1, n):
        row = np.zeros(nv); row[:NP] = (SPAN == s).astype(float); Aub.append(row); bub.append(2.0)
    row = np.zeros(nv); row[-1] = 1.0; row[-2] = -0.05; Aub.append(row); bub.append(0.0)                 # t <= 0.05 c
    BMIN_FRAC = float(__import__('os').environ.get('BMIN_FRAC', str(1.05 / 32)))   # Lean root cover: b_r >= cN/32 (bridge-port), with 5% margin
    for r in range(m):
        row = np.zeros(nv); row[NP + r] = -1.0; row[NP + m] = BMIN_FRAC; Aub.append(row); bub.append(0.0)   # BMIN_FRAC*c - b_r <= 0
    Aeq, beq = [], []
    if KW[0] is not None:                                     # the kept basin's current minimiser sits exactly at level c
        d = Fw_parts(KW[0]); row = np.zeros(nv); row[:NP] = wex(d); row[NP:NP + m] = np.asarray(KW[0]); row[-2] = -1.0; Aeq.append(row); beq.append(0.0)
    for k in range(NP):
        if MP[k] > k:
            row = np.zeros(nv); row[k] = 1; row[MP[k]] = -1; Aeq.append(row); beq.append(0.0)
    for r in range(m):
        if m - 1 - r > r:
            row = np.zeros(nv); row[NP + r] = 1; row[NP + m - 1 - r] = -1; Aeq.append(row); beq.append(0.0)
    bounds = [(0, None)] * NP + [(1e-6, None)] * m + [(0, None), ((None, None) if tfix is None else (tfix, None))]
    res = linprog(cobj, A_ub=np.array(Aub), b_ub=np.array(bub), A_eq=np.array(Aeq), b_eq=np.array(beq), bounds=bounds, method='highs')
    assert res.status == 0, res.message
    x = res.x; return x[:NP], x[NP:NP + m], x[-2], x[-1]
rng = np.random.default_rng(9)
G = [np.array(b['gaps']) for b in I9['basins_excess_le_2e-4']] + [np.array(w) for w in WORDS[::16]] + [kw]
t0 = time.time()
for rnd in range(MAXR):
    a, b, c, t = solve(G)
    try:
        a, b, c, t = solve(G, tfix=t * (1 - 1e-4))                       # lexicographic: max t, then max c
    except AssertionError:
        pass
    global_min(a, b, list(WORDS) + G[-300:], rng, nrand=100)
    mins = [(Fw_val(g, a, b, exact=True), g) for f, g in LASTMINS]
    viol = []
    for f, g in mins:
        need = c if pattern(g) in KP else c + t
        if f < need - 5e-8: viol.append((need - f, g))
    viol.sort(key=lambda v: -v[0])
    kept = [(f, g) for f, g in mins if pattern(g) in KP]
    if kept: KW[0] = min(kept, key=lambda v: v[0])[1]
    kexc = (min(kept, key=lambda v: v[0])[0] - c) if kept else float('nan')
    B = float(b.sum()); kap = (HLO - B) / (1 - c)
    print('round %2d: c %.10f t %.3e (rel %.3e) B %.9f kappa %.8f | kept basin above c by %.2e | violations %d (worst %.2e) | |G| %d | %.0fs'
          % (rnd, c, t, t / c, B, kap, kexc, len(viol), viol[0][0] if viol else 0, len(G), time.time() - t0), flush=True)
    if not viol and abs(kexc) < 5e-8 and rnd > 0: break
    for v, g in viol[:60]: G.append(g)
json.dump({'n': 9, 'target': KT, 'keep': KEEP, 'keep_word': kw.tolist(), 'pairs': [[int(i), int(j)] for i, j in zip(PI, PJ)],
           'a': a.tolist(), 'b': b.tolist(), 'c_lp': c, 't_lp': t, 'kappa_lp': kap}, open(OUT_SEP + '.json', 'w'))
