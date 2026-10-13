"""Round 13c: fixed-width point index with escape.  Index w bits into a table of the 2^w - 1 most frequent jj values (per (term, slot) or
global); value 2^w - 1 = escape, then 7 raw bits.  Tables built on BUILD and applied to every DATA (out of sample when different).
usage: python3 top63.py BUILD_DATA.json DATA.json [DATA2.json ...]"""
import sys, json, collections
BUILD, FILES = sys.argv[1], sys.argv[2:]
def parse(path):
    sys.argv = ['walkcode.py', path, '/dev/null', '/dev/null']
    src = open('/Users/samuellavery/work/riemann-submission/bench/arun/est/walkcode.py').read().split("if SPEC_IN:")[0]
    g = {'__name__': 'wc'}; exec(src, g); return g['EV'], g['NL']
def codes(EV):
    for ev in EV:
        for e in ev:
            if e[0] != 'M': continue
            for t, (k, j1, j2, lam) in enumerate(e[1]):
                if k >= 1: yield (t, 1), j1
                if k == 3: yield (t, 2), j2
EVb, _ = parse(BUILD)
per = collections.defaultdict(collections.Counter); glob = collections.Counter()
for key, jj in codes(EVb): per[key][jj] += 1; glob[jj] += 1
print('distinct jj values in %s: %d (per-slot max %d)' % (BUILD.split('/')[-1], len(glob), max(len(c) for c in per.values())))
VAR = []
for w in (6, 5, 4):
    m = (1 << w) - 1
    VAR.append(('per-slot top-%d, %d bits' % (m, w), w, {k: set(s for s, _ in c.most_common(m)) for k, c in per.items()}, len(per) * m * 7))
    VAR.append(('global top-%d, %d bits' % (m, w), w, set(s for s, _ in glob.most_common(m)), m * 7))
for path in FILES:
    EV, NL = parse(path)
    allc = list(codes(EV)); n = len(allc)
    print('%s: %d leaves, %d point indices (%.2f per leaf); today %d bits = %.1f bits/leaf' % (path.split('/')[-1], NL, n, n / NL, 7 * n, 7 * n / NL))
    for name, w, T, tbits in VAR:
        isper = isinstance(T, dict)
        hit = collections.Counter(); tot = collections.Counter()
        for key, jj in allc:
            tot[key] += 1; hit[key] += (jj in (T.get(key, set()) if isper else T))
        H = sum(hit.values()); bits = n * w + (n - H) * 7
        worst = min(((hit[k] / tot[k], k, tot[k]) for k in tot if tot[k] >= 20), default=None)
        sav = 7 * n - bits; tab_hex = tbits / 4
        print('  %-26s coverage %.4f%%; worst slot (>= 20 uses) %s %.2f%% of %d; %.2f bits/index; %.1f bits/leaf (saves %.1f) = %.1f KB hex saved, table %.1f KB hex -> net %.1f KB' % (
            name, 100 * H / n, worst[1] if worst else '-', 100 * worst[0] if worst else 0, worst[2] if worst else 0, bits / n, bits / NL, sav / NL, sav / 4000, tab_hex / 1000, (sav / 4 - tab_hex) / 1000))
