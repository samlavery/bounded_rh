#!/usr/bin/env python3
"""rt_split.py RT.tsv [TOPN]: split a ReplayTimes.lean dump (name, µs, unit size) by part of the assembled file and by
category inside the certificate; auxiliary constants (`_proof_k`, `match_k`, `_auxLemma`, `_eq_k`, ...) are charged to
their parent declaration.  Prints the per-part totals and the top TOPN certificate declarations."""
import re, sys
from collections import defaultdict

rows = []
for ln in open(sys.argv[1], encoding='utf-8'):
    n, us, k = ln.rstrip('\n').split('\t')
    rows.append((n, int(us)))
TOPN = int(sys.argv[2]) if len(sys.argv) > 2 else 20

def parent(n):
    parts = n.split('.')
    while len(parts) > 1 and re.match(r'^(_|match_\d|proof_\d|eq_\d|_proof|_auxLemma|_unary|_sunfold|_cstage)', parts[-1]):
        parts.pop()
    return '.'.join(parts)

def part(n):
    if '.PC8Data.' in n or n.startswith('AMW.Cert.PC8Data') or re.search(r'\.PC8_(G_rev|half|cert_full)', n):
        return 'cert data (PC8Data)'
    if '.PC8.' in n or n.startswith('AMW.Cert.PC8.'):
        return 'cert instance (PC8Inst)'
    if re.search(r'\.AT7(Data|Inst)?\.|AT7_', n) or 'AT7Data' in n:
        return 'cert data (AT7Data)' if 'Data' in n or 'AT7_' in n else 'cert instance (AT7Inst)'
    if '.PCell' in n:
        return 'pair-cell generics (PCell*)'
    if re.search(r'AMW\.Cert\.(Pyr|PyrD|Min|CM|Eng|C[A-Z])', n) or '.CEngine' in n or 'AMW.Cert.' in n:
        return 'engine (CEngine/CMin/...)'
    if re.search(r'AMW\.(G[A-Z.]|Cell)', n):
        return 'evaluator (G*)'
    if 'BridgeW' in n and re.search(r'band|_τ|sRank|bp[A-Z_]|bp_', n):
        return 'τ chain + band profile'
    return 'AM layer + bridge + tail'

def cat(n):
    last = n.split('.')[-1]
    if re.match(r'^(wk|rc|run)\d*$', last) or last == 'run': return 'walk root / root cover'
    if re.match(r'^((PTL|PTs)\d*_\d+_ok|pblk_\d+|pblk_all|ptS)$', last): return 'point table check'
    if re.match(r'^(d?blk_\d+|d?blk_all|top_ok|topD_ok|hR)$', last): return 'table check'
    if re.match(r'^(BK|BKD|BKs|BKDs|PTL|PTs|TOP|TOPD|PT|REG|COV|WB|SMAX)', last): return 'data def'
    return 'glue'

tot = defaultdict(int); cnt = defaultdict(int)
agg = defaultdict(int)
for n, us in rows:
    p = parent(n)
    tot[part(p)] += us; cnt[part(p)] += 1
    agg[p] += us
T = sum(tot.values())
print(f'total {T/1e6:.1f} s over {len(rows)} replay units')
for k, v in sorted(tot.items(), key=lambda kv: -kv[1]):
    print(f'  {k:32s} {v/1e6:8.1f} s  {100*v/T:5.1f} %  ({cnt[k]} units)')
cert = {p: us for p, us in agg.items() if part(p).startswith('cert')}
if cert:
    cc = defaultdict(int); cn = defaultdict(int)
    for p, us in cert.items():
        cc[cat(p)] += us; cn[cat(p)] += 1
    C = sum(cc.values())
    print(f'certificate by category ({C/1e6:.1f} s):')
    for k, v in sorted(cc.items(), key=lambda kv: -kv[1]):
        print(f'  {k:28s} {v/1e6:8.1f} s  {100*v/C:5.1f} %  ({cn[k]} decls)')
    print(f'top {TOPN} certificate declarations:')
    for p, us in sorted(cert.items(), key=lambda kv: -kv[1])[:TOPN]:
        print(f'  {us/1e6:8.2f} s  {cat(p):24s} {p}')
