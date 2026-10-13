"""Round 13b: sizing of loop-free codes (at most 2 flag reads per field, no table loop) on a decoded PC9Q-family walk.
Modal tables are taken from the BUILD data (first argument) and applied to every DATA file listed (out of sample when different).
usage: python3 loopfree.py BUILD_DATA.json DATA.json [DATA2.json ...]"""
import sys, json, collections
BUILD, FILES = sys.argv[1], sys.argv[2:]
def parse(path):
    sys.argv = ['walkcode.py', path, '/dev/null', '/dev/null']
    src = open('/Users/samuellavery/work/riemann-submission/bench/arun/est/walkcode.py').read().split("if SPEC_IN:")[0]
    g = {'__name__': 'wc'}; exec(src, g); return g['EV'], g['NL'], g['NA'], g['JB'], g['LB']
EVb, NLb, NA, JB, LB = parse(BUILD)
def Ms(EV):
    for ev in EV:
        last = None
        for e in ev:
            if e[0] == 'M': yield e, last; last = e
        # previous-leaf state resets per root (one walk per root)
cK = collections.defaultdict(collections.Counter); cP = collections.defaultdict(collections.Counter); cJ = collections.defaultdict(collections.Counter); cL = collections.defaultdict(collections.Counter)
for e, _ in Ms(EVb):
    T = e[1]
    for t, (k, j1, j2, lam) in enumerate(T):
        cK[t][k] += 1
        if k >= 1: cJ[(t, 1)][j1] += 1
        if k == 3: cJ[(t, 2)][j2] += 1
        if k >= 2: cL[k][lam] += 1
    for q in range(NA // 2): cP[q][(T[2 * q][0], T[2 * q + 1][0])] += 1
rankK = {t: [s for s, _ in cK[t].most_common()] + [s for s in range(4) if s not in cK[t]] for t in range(NA)}
modeP = {q: cP[q].most_common(1)[0][0] for q in range(NA // 2)}
modeJ = {k: (cJ[k].most_common(1)[0][0] if cJ[k] else -1) for k in [(t, s) for t in range(NA) for s in (1, 2)]}
modeL = {k: cL[k].most_common(1)[0][0] for k in (2, 3)}
for path in FILES:
    EV, NL, _, _, _ = parse(path)
    bits = collections.Counter(); base = collections.Counter(); n = collections.Counter()
    for e, prev in Ms(EV):
        T = e[1]; P = prev[1] if prev else None
        for t, (k, j1, j2, lam) in enumerate(T):
            base['K'] += 2; n['K'] += 1
            bits['K1'] += 1 if k == rankK[t][0] else 3
            r = rankK[t].index(k); bits['K2'] += [1, 2, 3, 3][r]
            bits['K3'] += (1 if k == P[t][0] else 3) if P else 2
            for slot, jj in ((1, j1), (2, j2)):
                if jj is None: continue
                base['J'] += 7; n['J'] += 1
                bits['J1'] += 1 if jj == modeJ[(t, slot)] else 8
                pj = P[t][slot] if P else None
                bits['J2'] += (1 if jj == pj else 8) if pj is not None else 7
            if lam is not None:
                base['L'] += 10; n['L'] += 1; bits['L1'] += 1 if lam == modeL[k] else 11
        for q in range(NA // 2):
            pr = (T[2 * q][0], T[2 * q + 1][0])
            bits['K4'] += 1 if pr == modeP[q] else 5
            bits['K5'] += 1 if pr == modeP[q] else 1 + (1 if pr[0] == rankK[2 * q][0] else 3) + (1 if pr[1] == rankK[2 * q + 1][0] else 3)
    print('%s (%d leaves; modal tables from %s):' % (path.split('/')[-1], NL, BUILD.split('/')[-1]))
    for name, fam, what, state in [('K1', 'K', 'modal-kind flag per position, else 1+2 raw', 'none'), ('K2', 'K', 'ranked flags per position: lengths 1/2/3/3', 'none'),
                                   ('K3', 'K', 'same kind as previous leaf flag, else 1+2', '34 kinds (68 bits)'), ('K4', 'K', 'modal pair flag per position pair, else 1+4 raw', 'none'),
                                   ('K5', 'K', 'modal pair flag, else 1 + K1 per term', 'none'), ('J1', 'J', 'modal jj flag per (term, slot), else 1+7', 'none'),
                                   ('J2', 'J', 'same jj as previous leaf flag, else 1+7', '68 jj (476 bits)'), ('L1', 'L', 'modal lambda flag per kappa, else 1+10', 'none')]:
        sv = base[fam] - bits[name]
        print('  %-3s %-48s %8.2f bits/leaf saved = %6.1f KB hex; walk state: %s' % (name, what, sv / NL, sv / 4000, state))
