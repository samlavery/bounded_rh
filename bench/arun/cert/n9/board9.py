#!/usr/bin/env python3
"""board9.py MOD ROOT [MOD ROOT ...]: am-cert's retake8.sh board prediction (157 + 2·build + 2.46·(export + nanoda + closure),
each stage's time scaled by its instruction ratio to PC8C5BF's staged run, normalised to PC8C5BF's actual 2,319 s), verbatim,
for any staged module; also prints peaks (max RSS and peak footprint).  Run from bench/."""
import re, sys
def stats(p):
    t = i = rss = pk = None
    for ln in open(p, errors='replace'):
        m = re.match(r'\s*([\d.]+) real', ln); t = float(m.group(1)) if m else t
        m = re.match(r'\s*(\d+)\s+instructions retired', ln); i = int(m.group(1)) if m else i
        m = re.match(r'\s*(\d+)\s+maximum resident set size', ln); rss = int(m.group(1)) if m else rss
        m = re.match(r'\s*(\d+)\s+peak memory footprint', ln); pk = int(m.group(1)) if m else pk
    return t, i, rss, pk
def st(mod, root):
    return {'build': stats(f'{root}/build_{mod}.log'), 'replay': stats(f'{root}/replay_{mod}.log'),
            'export': stats(f'nanoda/export_{mod}.err'), 'nanoda': stats(f'nanoda/nanoda_{mod}.err'),
            'closure': stats(f'nanoda/replayx_{mod}.err')}
def P(s): return 157 + 2 * s['build'] + 2.46 * (s['export'] + s['nanoda'] + s['closure'])
Rf = st('CandPC8C5BFTS', 'specroot_pc8c5bfts')
args = sys.argv[1:]
for mod, root in zip(args[::2], args[1::2]):
    O = st(mod, root)
    print(f"== {mod}")
    for k in O: print(f"{k:8s} {O[k][0]:7.1f} s  {O[k][1] / 1e12:6.3f}e12 instr  max RSS {O[k][2] / 1e9:5.2f} GB  peak footprint {O[k][3] / 1e9:5.2f} GB")
    sc = {k: Rf[k][0] * O[k][1] / Rf[k][1] for k in Rf}
    print(f"PREDICTED board ≈ {2319 * P(sc) / P({k: Rf[k][0] for k in Rf}):.0f} s (instruction-ratio vs PC8C5BF actual 2,319 s)")
