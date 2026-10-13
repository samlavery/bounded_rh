"""Round 11 (2): calibrate the hull proxy subcert2.SideHull (valid convex minorant per pair, one LP per cell) against the sizer (tree from T2DUMP).  For sampled nodes of bridge-port's t570 tree, the proxy
counts leaves certifying the FULL 9-point functional >= cN on the node's box and constraints; compare with the node's subtree size.
usage: python3 calib_proxy.py NSAMPLE OUT.json"""
import sys, json, time, numpy as np
NS, OUTC = int(sys.argv[1]), sys.argv[2]
sys.argv = ['t2star.py', '0', '/dev/null']
exec(open('/Users/samuellavery/work/riemann-submission/bench/arun/est/t2star.py').read().split("if __name__")[0])
import subcert2 as S2
wt = lambda x: np.interp(x, XT, KT) ** 2
FULL = S2.SideHull(Side(0, n - 1), XT, KT ** 2)
def lc(sl, cons): return {sl.side.tix.index(t): (lb / SC, ub / SC) for t, (lb, ub) in cons.items() if t in sl.side.tix}
nodes = []
def collect(nd, ri, path):
    nodes.append((ri, path, nd, sub_leaves(nd)))
    if nd[0] != 'leaf': collect(nd[4], ri, path + 'X'); collect(nd[5], ri, path + 'Y')
for ri, t in enumerate(D['trees']): collect(t, ri, '')
sizes = np.array([s for *_, s in nodes]); rs = np.random.default_rng(5); pick = []
for lo_, hi_ in [(1, 1), (2, 3), (4, 7), (8, 15), (16, 31), (32, 63), (64, 127), (128, 255), (256, 600)]:
    idx = np.where((sizes >= lo_) & (sizes <= hi_))[0]
    pick += list(rs.choice(idx, min(len(idx), NS), replace=False))
out = []; t0 = time.time()
for k in pick:
    ri, path, nd, s = nodes[k]; box = np.array(nd[1], float) / SC
    c, ok = FULL.count(box[:, 0], box[:, 1], lc(FULL, nd[2]), cN, cap=20000)
    out.append({'root': ri, 'path': path, 'sizer': int(s), 'proxy': int(c), 'ok': bool(ok)})
    print('root %2d %-30s sizer %5d proxy %6d%s  (%.0fs)' % (ri, path[:30], s, c, '' if ok else ' CAP', time.time() - t0), flush=True)
json.dump(out, open(OUTC, 'w'))
