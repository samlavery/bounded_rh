"""R_max curve on R8 (double precision).  An idealised chain that credits all pair energy up to rank R_max exactly,
through the full-range profile (i):
  defect >= E_band + (2 beta - beta^2) E_(8..R_max),  beta = min{1, (1 - sqrt(E_band/tau)) / sqrt(E_(8..R_max))}
(E_band <= tau; band = ranks 1..7), with PC8SF's pressure: R(R_max) = min over block configurations of
V = E_band + (2 beta - beta^2) E_out + Press, kappa = (m H - B(m - q)) / (m - R) at m = 152 (and best m).
Block quantities are phase-averaged exactly for periodic words: rank-k ordered pair energy = 2 (m - k) wbar_k,
Press = (m - 7) B gbar.  Binding configurations minimised over periodic words (q <= 8 general, structured a/b words
near and at integer periods, the dual and ergodic words).  Two-level proxy at the end."""
import sys, json, math, itertools, time
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window/capscan')
from slack import K, bN, aN, cc, H, m, q as QQ, tau
B = float(bN.sum()); KMAX = m - 1
PAIRS = [(a, b, wt) for (a, b), wt in aN.items() if wt]
PA = np.array([p[0] for p in PAIRS]); PB = np.array([p[1] for p in PAIRS]); PW = np.array([p[2] for p in PAIRS])

def wbar(g, kmax=KMAX):
    """mean over the word's positions of W at rank distance k, k = 1..kmax"""
    g = np.asarray(g, float); qq = len(g)
    reps = kmax // qq + 2
    x = np.concatenate([[0.0], np.cumsum(np.tile(g, reps))])
    i = np.arange(qq)[:, None]; k = np.arange(1, kmax + 1)[None, :]
    return (K(x[i + k] - x[i]) ** 2).mean(axis=0)

def block_V(g, Rmax, mm=m):
    w = wbar(g, mm - 1); kk = np.arange(1, mm)
    Ek = 2 * (mm - kk) * w
    Eb = Ek[:7].sum(); Eo = Ek[7:min(Rmax, mm - 1)].sum() if Rmax > 7 else 0.0
    press = (mm - 7) * B * float(np.mean(g))
    if Eb > tau: return np.inf, Eb, Eo, press, 0.0
    beta = 1.0 if Eo <= 0 else min(1.0, (1 - math.sqrt(Eb / tau)) / math.sqrt(Eo))
    return Eb + (2 * beta - beta ** 2) * Eo + press, Eb, Eo, press, beta

def kappa(R, mm=m):
    return (mm * H - B * (mm - 7)) / (mm - R)

def Fwin(w7):
    w7 = np.asarray(w7, float); x = np.concatenate([[0.0], np.cumsum(w7)])
    return float(np.dot(bN, w7) + np.sum(PW * K(x[PB] - x[PA]) ** 2))

def F_cyclic(g):
    g = np.asarray(g, float); ext = np.tile(g, 8 // len(g) + 2)
    return np.array([Fwin(ext[s:s + 7]) for s in range(len(g))])

if __name__ == '__main__':
    t0 = time.time(); rng = np.random.default_rng(13)
    RM = [7, 8, 10, 12, 15, 20, 30, 60, KMAX]
    a, b = 1.04, 1.97
    seeds = {}
    for qq in range(1, 9):
        seeds[qq] = [np.array(p) for p in itertools.product((a, b), repeat=qq)] + [rng.uniform(0.6, 2.4, qq) for _ in range(12 if qq < 6 else 6)]
    named = [[1.96183, 1.03817], [1.9745, 1.0427], [1.0451, 1.9866, 1.9866, 1.0451, 1.9758, 1.0436, 1.9759],
             [1.029992, 1.953037, 1.037678, 1.958585, 1.037678, 1.953037, 1.029992], [1.028397, 1.028397, 1.943206]]
    for s in np.linspace(2.99, 3.03, 9):          # alternating words with prescribed a + b near 3
        for af in (1.035, 1.04, 1.045): named.append([af, s - af])
    curve = {}
    for Rmax in RM:
        best = (np.inf, None)
        cands = [np.array(w) for w in named] + [s for qq in seeds for s in seeds[qq]]
        for s0 in cands:
            f = lambda g: block_V(g, Rmax)[0]
            r = minimize(f, s0, method='L-BFGS-B', bounds=[(0.3, 4.0)] * len(s0), options={'maxiter': 200})
            if r.fun < best[0]: best = (float(r.fun), r.x.copy())
        V, Eb, Eo, press, beta = block_V(best[1], Rmax)
        kbest = max((kappa(block_V(best[1], Rmax, mm)[0], mm), mm) for mm in range(120, 241, 4))
        L = sum(best[1]); per = L / round(L) if round(L) else 0
        curve[Rmax] = dict(R=V, kappa=kappa(V), kappa_bestm=kbest, word=list(map(float, best[1])), Eb=Eb, Eo=Eo, beta=beta)
        print('R_max %4s: R = %.6f  kappa(m=152) = %.7f  [best m %d: %.7f]  binding word q=%d gaps %s (period %.4f, a+b-type sums %s) Eb %.4f Eo %.4f beta %.3f (%.0fs)'
              % ('inf' if Rmax == KMAX else Rmax, V, kappa(V), kbest[1], kbest[0], len(best[1]), np.round(best[1], 4), L,
                 np.round([best[1][i] + best[1][(i + 1) % len(best[1])] for i in range(len(best[1]))][:4], 4), Eb, Eo, beta, time.time() - t0), flush=True)
    json.dump({str(k): v for k, v in curve.items()}, open('rmax_r8.json', 'w'), indent=1)
    # ---- two-level proxy: windows near binding, runs, forced long-range energy
    c = 805165 / 1e8
    for nm, gw in (('ergodic word abbabab', named[2]), ('alternating', named[1])):
        Fw = F_cyclic(gw) / c - 1
        print('\n%s: window excess over c per cyclic window (%%): %s' % (nm, np.round(100 * Fw, 3)))
        for d in (0.005, 0.01, 0.02):
            inU = Fw <= d
            print('  delta %.1f%%: %d/%d windows in U; run length %s' % (100 * d, inU.sum(), len(inU), 'infinite (all windows)' if inU.all() else 'cyclic max %d' % max(len(list(gr)) for k, gr in itertools.groupby(np.tile(inU, 3)) if k)))
    print('\nforced long-range energy per point e(l) = min over periodic words with ALL windows F <= c(1+delta) of the per-point'
          ' ordered-pair energy at ranks 8 .. l+6 (within a run of l windows):')
    for d in (0.005, 0.01, 0.02):
        for ell in (8, 16, 32):
            best = (np.inf, None)
            for qq in (2, 3, 4, 5, 6, 7, 8):
                for s0 in seeds[qq][:min(len(seeds[qq]), 20)] + [np.array(named[1] * 4)[:qq]]:
                    cons = [{'type': 'ineq', 'fun': (lambda g, s=s: c * (1 + d) - Fwin(np.tile(g, 8)[s:s + 7]))} for s in range(qq)]
                    obj = lambda g: 2 * float(wbar(g, ell + 6)[7:].sum())
                    try:
                        r = minimize(obj, s0, method='SLSQP', bounds=[(0.3, 4.0)] * qq, constraints=cons, options={'maxiter': 200})
                    except Exception:
                        continue
                    if r.success and all(cf['fun'](r.x) >= -1e-9 for cf in cons) and r.fun < best[0]: best = (float(r.fun), r.x.copy())
            if best[1] is not None:
                sums = [best[1][i] + best[1][(i + 1) % len(best[1])] for i in range(len(best[1]))]
                print('  delta %.1f%%  l = %2d: e = %.6f per point (q=%d gaps %s; consecutive sums %s)'
                      % (100 * d, ell, best[0], len(best[1]), np.round(best[1], 4), np.round(sums, 4)), flush=True)
            else:
                print('  delta %.1f%%  l = %2d: no feasible word found' % (100 * d, ell), flush=True)
