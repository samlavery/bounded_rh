#!/usr/bin/env python3
"""instr_predict.py OUT REF REF_BOARD_S [OUT_MOD_SUFFIX]: load-free board-time prediction for the run_n8 outputs ${OUT}
from a reference run ${REF} whose board time is known.  Per stage (stripped build, export, nanoda, closure replay) the
reference's local time is scaled by the ratio of retired instructions; the conservative model
P = 157 + 2·build + 2.46·(export + nanoda + closure) is evaluated on both, and the prediction is REF_BOARD_S · P(scaled) /
P(ref).  OUT_MOD_SUFFIX selects a re-measure (e.g. 'q' for Cand${OUT}TSq in specroot_${out}tsq)."""
import os, re, sys

B = os.path.expanduser('~/work/riemann-submission/bench')

def stats(path):
    t = i = None
    for ln in open(path, encoding='utf-8', errors='replace'):
        m = re.match(r'\s*([\d.]+) real', ln)
        if m: t = float(m.group(1))
        m = re.match(r'\s*(\d+)\s+instructions retired', ln)
        if m: i = int(m.group(1))
    return t, i

def stages(out, suf=''):
    lc = out.lower(); mod = f'Cand{out}TS{suf}'; root = f'specroot_{lc}ts{suf}'
    return {'build': stats(f'{B}/{root}/build_{mod}.log'), 'replay': stats(f'{B}/{root}/replay_{mod}.log'),
            'export': stats(f'{B}/nanoda/export_{mod}.err'), 'nanoda': stats(f'{B}/nanoda/nanoda_{mod}.err'),
            'closure': stats(f'{B}/nanoda/replayx_{mod}.err')}

def P(s):
    return 157 + 2 * s['build'] + 2.46 * (s['export'] + s['nanoda'] + s['closure'])

out, ref, refboard = sys.argv[1], sys.argv[2], float(sys.argv[3])
suf = sys.argv[4] if len(sys.argv) > 4 else ''
o, r = stages(out, suf), stages(ref)
scaled = {}
print(f'{"stage":8s} {"ref s":>8s} {"ref instr":>11s} {out+" s":>10s} {out+" instr":>13s} {"ratio":>6s}')
for k in ('build', 'replay', 'export', 'nanoda', 'closure'):
    (rt, ri), (ot, oi) = r[k], o[k]
    ratio = oi / ri
    scaled[k] = rt * ratio
    print(f'{k:8s} {rt:8.1f} {ri:11.3e} {ot:10.1f} {oi:13.3e} {ratio:6.3f}')
pr, ps = P({k: r[k][0] for k in r}), P(scaled)
po = P({k: o[k][0] for k in o})
print(f'conservative: ref {pr:.1f} s, {out} measured {po:.1f} s, {out} at ref load (instruction-scaled) {ps:.1f} s')
print(f'predicted board: {refboard:.0f} × {ps:.1f} / {pr:.1f} = {refboard * ps / pr:.0f} s')
