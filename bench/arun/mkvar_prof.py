#!/usr/bin/env python3
"""mkvar_prof.py: bench-only variants of PFNPInst (am-cert, 2026-10-10; definitions only, certify nothing).
  PFNOInst: every term side condition `(mokTZC …)` in mcheckP replaced by `true`;
  PFNMInst: mcheckP's main inequality `(Nat.ble …)` replaced by `true` (side conditions kept).
On PC8C5BF's walks every leaf passes both parts, so each variant walks the same nodes and ends at the same position."""
import os, re
W = os.path.expanduser("~/work/riemann-submission/bench/window/rootR8f/AMW")
src = open(f"{W}/PFNPInst.lean", encoding="utf-8").read()
def balanced_end(t, i):
    d = 0
    for k in range(i, len(t)):
        if t[k] == "(": d += 1
        elif t[k] == ")":
            d -= 1
            if d == 0: return k + 1
    raise ValueError
a = src.index("def mcheckP"); b = src.index("\ntheorem", a) if "\ntheorem" in src[a:] else src.index("\ndef mleafP", a)
body = src[a:b]
def sub_calls(body, head):
    out = []; i = 0; n = 0
    while True:
        j = body.find(head, i)
        if j < 0: out.append(body[i:]); break
        e = balanced_end(body, j); out.append(body[i:j] + "true"); i = e; n += 1
    return "".join(out), n
noOK, n1 = sub_calls(body, "(mokTZC ")
k = body.index("(Nat.ble"); e = balanced_end(body, k)
noMAIN = body[:k] + "true" + body[e:]
for name, nb in [("PFNO", noOK), ("PFNM", noMAIN)]:
    p = f"{W}/{name}Inst.lean"
    if os.path.exists(p): raise SystemExit(f"{p} exists")
    t = (src[:a] + nb + src[b:]).replace("namespace AMW.Cert.PFNP", f"namespace AMW.Cert.{name}").replace("end AMW.Cert.PFNP", f"end AMW.Cert.{name}")
    t = t.replace('macro "pc_spl_PFNPInst ', f'macro "pc_spl_{name}Inst ')
    open(p, "w", encoding="utf-8").write(t)
    print(p, len(t))
print("mokTZC calls replaced:", n1)
