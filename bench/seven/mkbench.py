import re, json, sys
NAME = sys.argv[1]; NCH = int(sys.argv[2]) if len(sys.argv) > 2 else 4
d = open(f'../../data_{NAME}.lean').read()
c = open(f'../../checker_{NAME}.lean').read()
i = c.index("/-! ###### the 7-point weighted certificate")
open('SevC.lean', 'w').write("import ConvCore\n\nset_option maxRecDepth 100000\n" + c[i:])
w = json.load(open(f'walkstat_{NAME}.json'))
items = sorted(w.items(), key=lambda kv: -(kv[1]['S'] + kv[1]['SF']))
keep = {n for n, _ in items[:NCH]}
print([(n, w[n]) for n in sorted(keep, key=lambda x: int(x[2:]))])
blocks = re.split(r'\n(?=(?:def|theorem) )', d)
res = []
for b in blocks:
    m = re.match(r'(def|theorem) (\S+)', b)
    if not m: res.append(b); continue
    kind, name = m.groups()
    if kind == 'def': res.append(b); continue
    if name in ('lbS', 'lbD', 'ptS', 'hbas', 'hR'):
        res.append(b.split(':=')[0].replace('theorem', 'axiom', 1)); continue
    if name in keep: res.append(b)
txt = '\n'.join(res)
txt = "import SevC\n\nset_option Elab.async false\nset_option profiler true\nset_option profiler.threshold 10\n" + txt
if f'end Zeta23Ext.Bridge.ThreePoint.{NAME}Data' not in txt: txt += f'\nend Zeta23Ext.Bridge.ThreePoint.{NAME}Data\n\nend\n'
open('SevB.lean', 'w').write(txt)
