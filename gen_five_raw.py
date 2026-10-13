import sys, os, pickle, time
sys.path.insert(0, os.path.expanduser("~/work/zeta-lab/hunts/ainta_seven_point"))
import five_point_gen as F5, four_point_gen as G4, three_point_gen as G
G4.extend_anchors(16)
t = time.time()
res = F5.certificate(3000, 2500)
assert res is not None
ivals = F5.collect_intervals(res)
nl = sum(F5.nleaves(n) for _, n in res['boxes'])
print(f"done in {time.time()-t:.0f}s: cells={len(ivals)} bad={len(res['bad'])} boxes={len(res['boxes'])} leaves={nl} clear={len(res['clear'])}")
pickle.dump(dict(res=res, ivals=ivals), open("five_raw.pkl", "wb"))
