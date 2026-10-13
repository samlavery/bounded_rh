"""Leaf counts at delta 2% for axis-choice scores (sizing only)."""
import size_pyr, time
src = open("size_pyr.py").read()
cN = round(358287 * (1 - 0.02))
variants = {
  "passfirst_sum": "score = ((la >= CSU) + (lb2 >= CSU), la + lb2)",
  "passfirst_min": "score = ((la >= CSU) + (lb2 >= CSU), min(la, lb2))",
  "sum_only": "score = (0, la + lb2)",
  "passfirst_max": "score = ((la >= CSU) + (lb2 >= CSU), max(la, lb2))",
}
for name, line in variants.items():
    s = src.replace("score = ((la >= CSU) + (lb2 >= CSU), la + lb2)", line)
    ns = {"__name__": "x", "__file__": __file__}
    exec(compile(s, "size_pyr_v", "exec"), ns)
    t = time.time()
    r = ns["run"](cN, PE=5, PB=10, MAXA=4, verbose=False)
    print(f"{name}: leaves {r['nleaves'] if r else 'FAIL'} ({time.time()-t:.0f}s)", flush=True)
