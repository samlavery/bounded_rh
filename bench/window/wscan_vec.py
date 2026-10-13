"""LP ceiling at given n, B for an explicit window theta = [w0, c1..cK] (json on argv)."""
import sys, json, time
sys.path.insert(0, '/Users/samuellavery/work/riemann-submission/bench/window')
from wopt import evaluate
import numpy as np
n, B = int(sys.argv[1]), float(sys.argv[2]); th = np.array(json.loads(sys.argv[3]))
t0 = time.time(); r = evaluate(n, B, th[0], th[1:])
print('VEC n=%d B=%.5f: H=%.10f eps=%.9f (upper %.9f) Phi=%.7f m=%d (%.0fs)' % (n, B, r['H'], r['eps'], r['upper'], r['phi'], r['m'], time.time()-t0), flush=True)
