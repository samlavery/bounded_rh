"""Round 2 diagnostic: where the DP's minimising environment chain sits and what it collects.
Runs multi_env_dp.run (patched in memory to expose its fields; the file itself is not modified) for the named geometries and bins the
chain's contributions by distance from the block (inside the span / 0-3 / 3-10 / 10-20 / 20-50 / 50-150 / 150+ from the nearer end):
mass, field m*Phi (pair fields), env-pair doubles m*4*sum_p g, density band m*4t*h_W, low band m*2t_L*w, and the remainder (bonds + cluster).
usage: python3 chain_diag.py GEOMS.json name@Y[,name@Y...] [RES]   (MEDP_* env vars as for multi_env_dp.py)"""
import sys, json, numpy as np
GF, WANT = sys.argv[1], sys.argv[2].split(","); RES = sys.argv[3] if len(sys.argv) > 3 else '256'
src = open('multi_env_dp.py').read().split("if __name__ == '__main__':")[0]
src = src.replace("    global LAST_CHAIN\n", "    global LAST_CHAIN, LAST_F\n    LAST_F = dict(lo=lo, hi=hi, Phi=Phi, G4=G4, s=s, ys=ys, wlo=(wlo if TLOW > 0 else np.zeros(K)))\n", 1)
src = src.replace("len(chain) > 2000", "len(chain) > 40000"); assert "LAST_F" in src and "40000" in src
sys.argv = ['multi_env_dp.py', GF, '', RES]
exec(src)
BANDS = [(-1e9, 0), (0, 3), (3, 10), (10, 20), (20, 50), (50, 150), (150, 1e9)]
for geo in json.load(open(GF)):
    if geo["name"] + "@%g" % geo["Y"] not in WANT: continue
    lb, q, tpp, venv, tail, S2, K, dt, dconst = run(geo)
    F = LAST_F; lo, hi, Phi, G4, s = F['lo'], F['hi'], F['Phi'], F['G4'], F['s']; xmin, xmax = s.min(), s.max()
    ch = LAST_CHAIN; xs = np.array([c[0] for c in ch]); ms = np.array([c[1] for c in ch], float)
    ks = np.searchsorted(lo, xs) - 1
    gp = np.zeros(len(ks)); bandp = np.zeros(len(ks))
    for p in range(len(s)):
        da = np.where((lo[ks] - s[p] <= 0) & (hi[ks] - s[p] >= 0), 0.0, np.minimum(np.abs(lo[ks] - s[p]), np.abs(hi[ks] - s[p])))
        db = np.maximum(np.abs(lo[ks] - s[p]), np.abs(hi[ks] - s[p]))
        gp += 4 * C.gmin_range(da, np.minimum(db, C.X + 1))
        if TDENS > 0 and REFM < 0: bandp += 4 * TDENS * cell_lower_hW(lo[ks], hi[ks], s[p])
    low = 2 * TLOW * F['wlo'][ks]
    field = ms * Phi[ks]; onebody = ms * (Phi[ks] + G4[ks])
    d = np.where(xs < xmin, xmin - xs, np.where(xs > xmax, xs - xmax, -1.0))
    print('%s@%g P=%d: LB %+.4f  V_env %+.4f  chain: %d points, mass %d, one-body %+.4f, bonds+cluster %+.4f'
          % (geo['name'], geo['Y'], len(s), lb, venv, len(xs), int(ms.sum()), onebody.sum(), venv - onebody.sum()))
    for a, b in BANDS:
        sel = (d >= a) & (d < b) if a >= 0 else (d < 0)
        if not np.any(sel): continue
        nm = 'inside span' if a < 0 else '%g-%g' % (a, b) if b < 1e8 else '%g+' % a
        print('   %-12s mass %4d (doubles %3d)  field %+.4f  env-pair g %+.4f  band %+.4f  low %+.4f  | one-body/mass %+.5f'
              % (nm, int(ms[sel].sum()), int((ms[sel] == 2).sum()), field[sel].sum(), (ms * gp)[sel].sum(), (ms * bandp)[sel].sum(),
                 (ms * low)[sel].sum(), onebody[sel].sum() / ms[sel].sum()), flush=True)
