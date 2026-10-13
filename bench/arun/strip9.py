#!/usr/bin/env python3
"""strip9.py SRC.lean UNREACH.tsv OUT.lean [KEEP.txt]: the precise strip (am-cert, 2026-10-11).

UNREACH.tsv comes from strip/Reach.lean on SRC's compiled olean: every module declaration NOT reachable (types, values and
proofs) from the three candidate theorems, with its declaration range `name  start  end  kind` (1-based lines; the range
covers the docstring and attributes), and the ranges of the reachable ones (kind REACH): a span shared with a reachable
declaration is kept.  A declaration is removed (its whole range) unless:
  * it carries an attribute (`@[`) or is an `instance` (trap 4: simp/rfl lemmas and instances leave no trace in terms);
  * its name is in KEEP.txt (names the compiler asked for on an earlier round: `simp [foo]` arguments, notation, etc.).
Block comments `/- … -/` (the notices) and everything outside the removed ranges are kept byte-for-byte; runs of more
than two blank lines left behind are collapsed to two.  Prints the bytes removed."""
import sys

src_p, un_p, out_p = sys.argv[1:4]
keep = set(open(sys.argv[4]).read().split()) if len(sys.argv) > 4 else set()
lines = open(src_p, encoding="utf-8").read().split("\n")
# names listed in `export X (a b)` / `open X (a b)` / `open X renaming …` must exist even when unreachable
import re as _re
for _l in lines:
    _m = _re.match(r"^\s*(?:export|open)\s+\S+\s*\(([^)]*)\)", _l)
    if _m: keep.update(_m.group(1).split())
drop = set(); nrem = 0; nkeep_attr = 0; nkeep_name = 0; nkeep_reach = 0
rows = [r.split("\t") for r in open(un_p).read().split("\n") if r.strip()]
# a span shared with a reachable declaration (a structure's auxiliaries `rec`/`casesOn`, equation lemmas…) is never cut
reach_spans = {(int(r[1]), int(r[2])) for r in rows if r[3] == "REACH"}
done = set()
for name, a, b, kind in rows:
    a, b = int(a), int(b)
    if kind in ("norange", "REACH") or a == 0: continue
    if (a, b) in reach_spans: nkeep_reach += 1; continue
    # a span nested inside a reachable declaration (a structure field's projection theorem) is part of it
    if any(ra <= a and b <= rb for (ra, rb) in reach_spans if ra <= a): nkeep_reach += 1; continue
    if (a, b) in done: continue
    done.add((a, b))
    if name in keep or name.split(".")[-1] in keep or any(name.endswith("." + k) for k in keep if "." in k): nkeep_name += 1; continue
    span = lines[a - 1:b]
    head = "\n".join(span[:6])
    if "@[" in head or any(l.lstrip().startswith(("instance", "@[")) for l in span[:3]): nkeep_attr += 1; continue
    # never cut into a notice block: the range must not contain a block-comment opener that is not a docstring
    if any(l.lstrip().startswith("/-") and not l.lstrip().startswith("/--") for l in span): nkeep_attr += 1; continue
    drop.update(range(a - 1, b)); nrem += 1
    # a command prefix `open … in` / `set_option … in` / `omit … in` (column 0) above belongs to the removed declaration
    j = a - 2
    while j >= 0 and lines[j].rstrip().endswith(" in") and lines[j][:1] not in (" ", "\t") and lines[j].strip():
        drop.add(j); j -= 1
out = []; blank = 0
for i, l in enumerate(lines):
    if i in drop: continue
    if l.strip() == "":
        blank += 1
        if blank > 2: continue
    else:
        blank = 0
    out.append(l)
txt = "\n".join(out)
open(out_p, "w", encoding="utf-8").write(txt)
before = len("\n".join(lines).encode()); after = len(txt.encode())
print(f"removed {nrem} declarations ({len(drop)} lines); kept attributed/instance {nkeep_attr}, by name {nkeep_name}, shared-with-reachable {nkeep_reach}; "
      f"bytes {before} -> {after} ({before - after} removed)")
