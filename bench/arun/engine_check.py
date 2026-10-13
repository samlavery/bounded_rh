#!/usr/bin/env python3
"""engine_check.py IN.lean ROOT NAME OUT.lean: make sure the certificate NAME's engine is present in a swapped file
(am-cert, 2026-10-10).

The swap markers cover only the certificate (instance, data, glue, RiemannFail); the generic engine (Pyr, PyrD, PCell*,
PCD*, CEngine, AMW.G…) is the base file's.  This walks the import closure of ROOT/AMW/{NAME}Data.lean and, for every module
in it, compares each declaration's first line with the lines of IN:
  * a module none of whose declarations appear (e.g. AMW.PCBias for a HELP instance) is inserted if the certificate
    references one of its declarations, imports removed and
    its scopes closed, just before `-- SWAP BEGIN certificate`;
  * a module with SOME declarations missing is a hard stop only if the certificate's own modules reference one of the
    missing names (otherwise those declarations were stripped as dead and are not needed);
  * a declaration present under the same name with a different first line is reported (engine drift) — hard stop if the
    certificate references it.
Writes OUT (IN plus the inserted modules) and prints what it did."""
import os, re, sys
IN, ROOT, NAME, OUT = sys.argv[1:5]
base = open(IN, encoding="utf-8").read()
lines = set(l.strip() for l in base.split("\n"))
R = os.path.join(ROOT, "AMW")
mods = {fn[:-5]: open(os.path.join(R, fn), encoding="utf-8").read() for fn in os.listdir(R) if fn.endswith(".lean")}
deps = lambda t: re.findall(r"^import AMW\.(\w+)\s*$", t, re.M)
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps(mods[m]): visit(d)
    order.append(m)
visit(NAME + "Data")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)( [^\s:({\[]+)?[^\n]*", re.M)
cert_text = mods[NAME + "Inst"] + mods[NAME + "Data"]
cert_text = re.sub(r"/-.*?-/", " ", cert_text, flags=re.S)          # names in comments and docstrings do not count
cert_text = re.sub(r"--[^\n]*", " ", cert_text)
used = set(x.split(".")[-1] for x in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", cert_text))
insert, stop = [], []
for m in order:
    if m in (NAME + "Inst", NAME + "Data"): continue
    ds = [(mt.group(0).strip(), (mt.group(1) or "").strip()) for mt in DECL.finditer(mods[m])]
    miss = [(l, n) for l, n in ds if l not in lines]
    if not miss: continue
    if len(miss) == len(ds):
        if any(n and n.split(".")[-1] in used for _, n in ds): insert.append(m)
        else: print(f"skipped module {m}: absent from {IN} and not referenced by {NAME}")
        continue
    for l, n in miss:
        if n and n.split(".")[-1] in used:
            drift = re.search(r"(theorem|lemma|def|abbrev) " + re.escape(n) + r"\b", base)
            stop.append((m, n, "drift (different text)" if drift else "missing"))
for m, n, why in stop:
    print(f"STOP: {m}.{n} is used by {NAME} and is {why} in {IN}")
if stop: sys.exit(1)
k = base.index("-- SWAP BEGIN certificate")
add = ""
for m in insert:
    body = re.sub(r"^import .*\n", "", mods[m], flags=re.M)
    opened = len(re.findall(r"^(noncomputable section|section)\b", body, re.M)) - len(re.findall(r"^end\s*$", body, re.M))
    add += "\nsection\n" + body + "\nend\n" * max(opened, 0) + "end\n"
    print(f"inserted module {m} ({len(body.encode())} B; {max(opened, 0)} open scope(s) closed)")
out = base[:k] + add + base[k:]
open(OUT, "w", encoding="utf-8").write(out)
print(f"{OUT}: {len(out.encode())} B; engine modules in {NAME}'s closure: {len(order) - 2}, inserted {len(insert)}, stops 0")
