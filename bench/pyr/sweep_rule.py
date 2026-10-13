"""Leaf counts at delta 2% for oracle extra-levels PE and bisection WFRAC (sizing only; the Lean checker bakes PE=5)."""
import sys, time
import size_pyr
cN = round(358287 * (1 - 0.02))
for PE, WF in [(5, 4), (6, 4), (5, 2), (5, 8), (4, 4)]:
    size_pyr.WFRAC = WF
    t = time.time()
    r = size_pyr.run(cN, PE=PE, PB=10, MAXA=4, verbose=False)
    if r is None: print(PE, WF, "FAIL"); continue
    P = r["P"]
    # reads per distinct query (the oracle's cost driver)
    nr = 0
    for (lo, hi) in list(P.cache)[:200000]:
        cv = P.cover(lo, hi); nr += len(cv) if cv else 0
    print(f"PE={PE} WFRAC={WF}: leaves {r['nleaves']} finest {r['stats']['finest']} entries {r['stats']['entries']} distinct q {r['nq']} reads/q {nr/max(1,min(200000,len(P.cache))):.2f} ({time.time()-t:.0f}s)", flush=True)
