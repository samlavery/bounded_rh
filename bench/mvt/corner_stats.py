import sys, collections
sys.path.insert(0, ".")
from size_m import run, Q, PAIRS, AN, BN
import gen_inst
TS = gen_inst.TS; U1 = 10**9; KU1 = 2 * U1
AR = [sum(AN[t] for t in TS[q]) for q in range(Q)]
r = run(354704, JC=4, corner=True, verbose=False)
PP, PM = r["PP"], r["PM"]
kinds = collections.Counter(); need = collections.Counter()
for b, kind in r["leaves"]:
    if kind != 2: continue
    tm = [(sum(b[q][0] for q in range(i, j)), sum(b[q][1] for q in range(i, j))) for (i, j) in PAIRS]
    p = [PP.lb(lo, hi) for lo, hi in tm]; qq = [PM.lb(lo, hi) for lo, hi in tm]
    st = []
    for q in range(Q):
        Pos = max(0, U1 * BN[q] + KU1 * AR[q] - sum(AN[t] * qq[t] for t in TS[q]))
        Neg = max(0, KU1 * AR[q] - (U1 * BN[q] + sum(AN[t] * p[t] for t in TS[q])))
        st.append('U' if Pos == 0 else ('L' if Neg == 0 else 'C'))
    kinds["".join(st)] += 1
    n = 0
    for t, (i, j) in enumerate(PAIRS):
        s = set(st[i:j])
        n += (0 if s == {'U'} else 1) + (0 if s == {'L'} else 1)
    need[n] += 1
tot = sum(kinds.values())
print("M leaves", tot)
print("patterns (top 15):", kinds.most_common(15))
print("lookups needed distribution:", sorted(need.items()), "mean", sum(k * v for k, v in need.items()) / tot)
