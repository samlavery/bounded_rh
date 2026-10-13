"""Exact check (periodic model, certificate v1) of the joint-DP optimal environment for block16 at Y = 0.2 / 0.4: embed the DP's
environment chain (doubles at density 2 near the block) and the block in a period N, fill the rest of the period uniformly with the
remaining mass (singles, evenly spaced), relax nothing, and compute the exact LP_total and its split.  Then relax all positions."""
import sys, json, numpy as np
from scipy.optimize import minimize
NN = int(sys.argv[1]) if len(sys.argv) > 1 else 1024
sys.argv = ['multi_env_dp.py', 'multipair_geoms.json', '', '256']
import os; os.environ['MEDP_XL'] = '128'
exec(open('multi_env_dp.py').read().split("if __name__ == '__main__':")[0])
G = {(g['name'], g['Y']): g for g in json.load(open('multipair_geoms.json'))}
exec(open('lemmaP.py').read().split("if __name__ == '__main__':")[0].replace("WIN, N = sys.argv[1], int(sys.argv[2])", "WIN, N = 'R8b', %d" % NN))
exec(open('multipair_dense2.py').read().split("def run(")[0].split("exec(open('lemmaP.py')")[1].split('\n', 1)[1])
for Y in (0.2, 0.4):
    geo = G[('block16', Y)]; out = run(geo); ch = LAST_CHAIN
    s = np.array(geo['pairs']); ys = np.array(geo['depths'])
    ex = np.array([c[0] for c in ch]); em = np.array([c[1] for c in ch])
    span_l, span_r = min(ex.min(), s.min()) - 0.5, max(ex.max(), s.max()) + 0.5
    M_in = em.sum() + 2 * len(s); rest = NN - M_in; L_out = NN - (span_r - span_l)
    sites = np.arange(np.ceil(span_r) + 0.0, np.ceil(span_r) + np.floor(L_out) - 1)          # unit lattice in the outer region
    nrm = len(sites) - int(rest); keep = np.ones(len(sites), bool)
    if nrm > 0: keep[np.round(np.linspace(0, len(sites) - 1, nrm)).astype(int)] = False         # evenly spread vacancies
    xs_fill = sites[keep]; assert len(xs_fill) == int(rest), (len(xs_fill), rest)
    xon = np.concatenate([np.repeat(ex, em.astype(int)), xs_fill])   # doubles as two coincident singles (R convention: one point of mass 2 = two coincident? use mass array instead)
    # build with masses: environment points with their masses
    x_env = np.concatenate([ex, xs_fill]); m_env = np.concatenate([em, np.ones(len(xs_fill))])
    def LP_split(x_env, m_env, s, ys):
        xD = np.concatenate([x_env, s]); mD = np.concatenate([m_env, np.full(len(s), 2.0)])
        SD = np.exp(2j * np.pi * np.outer(JA, xD) / NN) @ mD
        SB = (np.exp(2j * np.pi * np.outer(JA, s) / NN) * (2 * np.cosh(2 * np.pi * np.outer(JA, ys) / NN) - 2)).sum(1)
        nz = JA != 0
        Ph = float(np.sum(hhA[nz] * np.abs(SD[nz]) ** 2) / NN); Tg = float(np.sum(ghA * np.abs(SD) ** 2) / NN) - gN0 * float(np.sum(mD ** 2))
        BB = float(np.sum(qA * np.abs(SB) ** 2) / NN); FLD = 2 * float(np.sum(qA * np.real(np.conj(SD) * SB)) / NN)
        return Ph, Tg, FLD, BB
    sp = LP_split(x_env, m_env, s, ys)
    # T_g restricted to pairs with both points in the DP window region
    xD = np.concatenate([x_env, s]); mD = np.concatenate([m_env, np.full(len(s), 2.0)]); inw = (xD >= span_l) & (xD <= span_r)
    Dm = np.abs(xD[inw][:, None] - xD[inw][None, :]); Gm = C.gfun(Dm.ravel()).reshape(Dm.shape); np.fill_diagonal(Gm, 0.0)
    Tg_win = float(mD[inw] @ Gm @ mD[inw])
    print('   T_g among window points (line-model g, all pairs) %.3f over %d points' % (Tg_win, int(inw.sum())), flush=True)
    print('Y=%.1f N=%d: DP bound %.4f | exact LP of the DP environment embedded: %.4f (P_h %.3f T_g %.3f fields %.3f B-B %.3f); mass check %.1f'
          % (Y, NN, out[0], sum(sp), *sp, m_env.sum() + 2 * len(s)), flush=True)
    nz = JA != 0; xD = np.concatenate([x_env, s]); mD = np.concatenate([m_env, np.full(len(s), 2.0)])
    SD = np.exp(2j * np.pi * np.outer(JA, xD) / NN) @ mD; P2 = np.abs(SD) ** 2 / NN; aJ = JA / NN
    bands = [(0, 1/64), (1/64, 1/16), (1/16, 0.5), (0.5, 1.0), (1.0, 1.5), (1.5, 3.0)]
    print('   P_h by band:', ' '.join('(%.3g,%.3g] %.3f' % (lo_, hi_, float(np.sum(np.where((np.abs(aJ) > lo_) & (np.abs(aJ) <= hi_) & nz, hhA, 0) * P2))) for lo_, hi_ in bands), flush=True)
