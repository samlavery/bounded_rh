"""Round 11, comparator for (2): top-down collapse of bridge-port's t570 tree under the hull-LP leaf test of subcert2.SideHull on the
FULL 9-point functional (per pair the valid convex minorant of w on the pair's effective range; one LP per node; float, not a certificate).
A node counts as one leaf when the LP value is >= cN.  Also records, per sizer leaf kind, nothing else.
usage: python3 hull_collapse.py OUT.json"""
import sys, json, time, numpy as np
OUTH = sys.argv[1]
sys.argv = ['t2star.py', '0', '/dev/null']
exec(open('/Users/samuellavery/work/riemann-submission/bench/arun/est/t2star.py').read().split("if __name__")[0])
import subcert2 as S2
FULL = S2.SideHull(Side(0, n - 1), XT, KT ** 2)
def lc(cons): return {FULL.side.tix.index(t): (lb / SC, ub / SC) for t, (lb, ub) in cons.items()}
st = {'lp': 0}; t0 = time.time(); per = {}; vals = []; NODE = {}         # NODE: path -> (hull leaves in the subtree, certified here)
def go(nd, path):
    box = np.array(nd[1], float) / SC; v = FULL.test(box[:, 0], box[:, 1], lc(nd[2]))[0]; st['lp'] += 1
    if v is not None and v >= cN: vals.append(v / cN - 1); NODE[path] = (1, True); return 1
    if nd[0] == 'leaf': NODE[path] = (1, False); return 1
    c = go(nd[4], path + 'X') + go(nd[5], path + 'Y'); NODE[path] = (c, False); return c
for ri, t in enumerate(D['trees']):
    per[ri] = (sub_leaves(t), go(t, 'R%d:' % ri))
    print('root %2d: %5d -> %5d (%d LPs, %.0fs)' % (ri, per[ri][0], per[ri][1], st['lp'], time.time() - t0), flush=True)
tot = (sum(a for a, b in per.values()), sum(b for a, b in per.values()))
print('total %d -> %d (%.1f%%)' % (tot[0], tot[1], 100 * (tot[1] / tot[0] - 1)), flush=True)
json.dump({'per_root': per, 'total': tot, 'nodes': NODE, 'collapsed_lp_excess_quantiles': np.quantile(vals, [0, .01, .1, .5]).tolist() if vals else []}, open(OUTH, 'w'))
