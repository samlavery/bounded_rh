#!/usr/bin/env python3
"""Assemble the single-file riemannzeta.fun submission from the lab's module sources.

Strips the Lean module-system header (`module`, `public import`, `@[expose] public section`),
collects external imports to the top, closes each file's `noncomputable section`, drops
`#print axioms` lines, and splits the 453-leaf `pair_0_1` bisection into chunk lemmas so that
the leaves elaborate in parallel.  Output: Solution.lean next to this script.
"""
import re, sys, os
from cells_transform import transform_cells, SHIFTS
from fractions import Fraction as Fr

LAB = os.path.expanduser("~/work/zeta-lab/lean/bridge")
ORDER = [
  "Zeta23Ext/StableRankTrace.lean",
  "Zeta23Ext/Bridge/Defs.lean", "Zeta23Ext/Bridge/Helpers_finite.lean",
  "Zeta23Ext/Bridge/Helpers_pinching.lean", "Zeta23Ext/Bridge/Helpers_S8.lean",
  "Zeta23Ext/Bridge/Helpers_S9.lean", "Zeta23Ext/Bridge/S6.lean", "Zeta23Ext/Bridge/S7.lean",
  "Zeta23Ext/Bridge/S8.lean", "Zeta23Ext/Bridge/S9.lean", "Zeta23Ext/Bridge/S11.lean",
  "Zeta23Ext/Bridge/S12.lean", "Zeta23Ext/Bridge/S13.lean", "Zeta23Ext/Bridge/S14.lean",
  "Zeta23Ext/Bridge/S15.lean", "Zeta23Ext/Bridge/S16.lean", "Zeta23Ext/Bridge/Main.lean",
  "Zeta23Ext/BridgeW/DefsW.lean", "Zeta23Ext/BridgeW/S11W.lean", "Zeta23Ext/BridgeW/S13W.lean",
  "Zeta23Ext/BridgeW/S15W.lean", "Zeta23Ext/BridgeW/MainW.lean", "Zeta23Ext/BridgeW/Fixed.lean",
  "ThreePoint/Base.lean",
] + [f"ThreePoint/Cells{i}.lean" for i in range(7)] + ["ThreePoint/Main.lean"]

CHUNK_LEAVES = int(sys.argv[1]) if len(sys.argv) > 1 else 24

imports = []
def strip_comments(s):
    out = []; i = 0; depth = 0
    while i < len(s):
        if s.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("-/", i):
            depth -= 1; i += 2; continue
        if not depth: out.append(s[i])
        i += 1
    t = "".join(out)
    ls = []
    for l in t.split("\n"):
        if "--" in l and '"' not in l: l = l[:l.index("--")].rstrip()
        ls.append(l)
    # collapse runs of blank lines
    res = []
    for l in ls:
        if l.strip() == "" and res and res[-1].strip() == "": continue
        res.append(l)
    return "\n".join(res)

def strip_module(text, path):
    text = strip_comments(text)
    out = []
    for line in text.split("\n"):
        s = line.strip()
        if s == "module": continue
        m = re.match(r"^public import (\S+)", s)
        if m:
            mod = m.group(1)
            if not (mod.startswith("Zeta23Ext") or mod.startswith("ThreePoint")):
                if mod not in imports: imports.append(mod)
            continue
        if s in ("@[expose] public section", "public section"): continue
        if s.startswith("#print axioms"): continue
        out.append(line)
    body = "\n".join(out).rstrip() + "\n\nend\n"   # close the file's `noncomputable section`
    # --- port fixes for the pinned Mathlib (51e6992) and the ChallengeDeps root namespace ---
    # (1) Mathlib 51e6992 resolves `Y * diagonal d * Yᴴ` through a CStarMatrix instance unless
    #     the diagonal factor is ascribed as a Matrix.
    if path.endswith("Helpers_pinching.lean"):
        body = re.sub(r"(?<!\()diagonal \(RCLike\.ofReal ∘ (d|hM\.eigenvalues)\)",
                      r"(diagonal (RCLike.ofReal ∘ \1) : Matrix ι ι 𝕜)", body)
    # (2) `Helpers_S9` re-proves `cos_sqrt_two_mul_nonneg` of `Helpers_finite` under the same name.
    if path.endswith("Helpers_S9.lean"):
        ls = body.split("\n")
        i = next(k for k, l in enumerate(ls) if l.startswith("lemma cos_sqrt_two_mul_nonneg"))
        j = i + 1
        while j < len(ls) and (ls[j].startswith("  ") or ls[j].strip() == ""): j += 1
        body = "\n".join(ls[:i] + ls[j:])
    # (3) `ChallengeDeps` puts `Ncount`, `N0simple`, `N0star` in the root namespace, so the bare
    #     names are ambiguous under `open Zeta23`; qualify them.
    body = re.sub(r"(?<![.\w])(Ncount|N0simple|N0star)\b", r"Zeta23.\1", body)
    return f"\n/-! ###### source module: {path} ###### -/\n" + body

# ---------- chunking of pair_0_1 ----------
RAT = r"\(([-0-9/]+):ℝ\)"
def parse_rat(s): return Fr(s)
def fmt_rat(q): return f"({q.numerator}/{q.denominator}:ℝ)" if q.denominator != 1 else f"({q.numerator}:ℝ)"

class Node:
    def __init__(self, var=None, val=None, lines=None):
        self.var, self.val, self.lines, self.kids = var, val, lines, []
    def leaves(self):
        return 1 if not self.kids else sum(k.leaves() for k in self.kids)

def parse_block(lines, indent):
    """lines: the block's lines, first line at column `indent` (after any bullet)."""
    first = lines[0][indent:]
    m = re.match(r"rcases le_total ([xy]) " + RAT + r" with hc \| hc$", first)
    if not m:
        return Node(lines=lines)
    node = Node(var=m.group(1), val=parse_rat(m.group(2)))
    # remaining lines: two bullets at column `indent`
    rest = lines[1:]
    bullets = []
    cur = None
    for ln in rest:
        if ln[indent:indent+2] == "· " and ln[:indent].strip() == "":
            cur = [ln[:indent] + "  " + ln[indent+2:]]   # replace bullet with two spaces
            bullets.append(cur)
        else:
            assert cur is not None, ("orphan line", ln)
            cur.append(ln)
    assert len(bullets) == 2, (len(bullets), first)
    for b in bullets:
        node.kids.append(parse_block(b, indent + 2))
    return node

NAMES0 = ("hx1", "hx2", "hy1", "hy2")

def render(node, indent, box, chunks, prefix, names, depth):
    """Return lines (at column `indent`) proving the goal on `box`; emit chunk lemmas."""
    if node.kids and node.leaves() <= CHUNK_LEAVES:
        name = f"{prefix}_c{len(chunks)}"
        body = render_full_at(node, 2, box, None, None, NAMES0, 0)
        chunks.append((name, box, body))
        xlo, xhi, ylo, yhi = names
        return [" " * indent + f"exact {name} x y (by linarith only [{xlo}]) (by linarith only [{xhi}]) "
                f"(by linarith only [{ylo}]) (by linarith only [{yhi}])"]
    return render_full_at(node, indent, box, chunks, prefix, names, depth)

def reindent(lines, old, new):
    out = []
    for ln in lines:
        assert ln[:old].strip() == "" or ln.strip() == "", ln
        out.append(" " * new + ln[old:] if ln.strip() else "")
    return out

def leaf_lines(lines, indent, names):
    xlo, xhi, ylo, yhi = names
    col = len(lines[0]) - len(lines[0].lstrip())
    ls = reindent(lines, col, indent)
    lists = {"x": (f"[{xlo}]", f"[{xhi}]"), "y": (f"[{ylo}]", f"[{yhi}]"),
             "(x+y)": (f"[{xlo}, {ylo}]", f"[{xhi}, {yhi}]")}
    out = []
    block_var, block_indent = None, None
    for l in ls:
        ind = len(l) - len(l.lstrip(" "))
        if block_var is not None and l.strip() and ind < block_indent:
            block_var, block_indent = None, None
        m = re.match(r"\s*rcases le_total (x|y|\(x\+y\)) " + RAT + r" with hq0 \| hq0$", l)
        if m:
            block_var, block_indent = m.group(1), ind
        def repl(mm):
            v = mm.group(2)
            lo, hi = lists[v]
            if block_var is not None and v == block_var:
                lo, hi = lo[:-1] + ", hq0]", hi[:-1] + ", hq0]"
            return f"{mm.group(1)} {v} (by linarith only {lo}) (by linarith only {hi})"
        l = re.sub(r"(wc_\d+) (x|y|\(x\+y\)) \(by linarith\) \(by linarith\)", repl, l)
        out.append(l)
    text = "\n".join(out)
    text = re.sub(r"have (hw\d) : [^\n]*? := (wc_\d+ (?:x|y|\(x\+y\)) \(by linarith only \[[^\]]*\]\) \(by linarith only \[[^\]]*\]\))",
                  r"have \1 := \2", text)
    haves = re.findall(r"^\s*have (h[wp]\d) ", text, flags=re.M)
    ls = text.split("\n")
    assert ls[-1].strip() == "linarith", ls[-1]
    ls[-1] = " " * indent + "linarith only [" + ", ".join(haves + [xlo, ylo]) + "]"
    assert "(by linarith)" not in "\n".join(ls), text
    return ls

def render_full_at(node, indent, box, chunks, prefix, names, depth):
    xlo, xhi, ylo, yhi = box
    if not node.kids:
        return leaf_lines(node.lines, indent, names)
    hname = f"q{node.var}{depth}"
    out = [" " * indent + f"rcases le_total {node.var} {fmt_rat(node.val)} with {hname} | {hname}"]
    nxlo, nxhi, nylo, nyhi = names
    for i, kid in enumerate(node.kids):
        if node.var == "x":
            kb = (xlo, node.val, ylo, yhi) if i == 0 else (node.val, xhi, ylo, yhi)
            kn = (nxlo, hname, nylo, nyhi) if i == 0 else (hname, nxhi, nylo, nyhi)
        else:
            kb = (xlo, xhi, ylo, node.val) if i == 0 else (xlo, xhi, node.val, yhi)
            kn = (nxlo, nxhi, nylo, hname) if i == 0 else (nxlo, nxhi, hname, nyhi)
        if chunks is not None:
            sub = render(kid, indent + 2, kb, chunks, prefix, kn, depth + 1)
        else:
            sub = render_full_at(kid, indent + 2, kb, None, None, kn, depth + 1)
        sub[0] = " " * indent + "· " + sub[0][indent + 2:]
        out.extend(sub)
    return out

GOAL = "(1345/1000000:ℝ) ≤ (1/(3000:ℝ)) * (x + y) + wfun x + wfun y + 2 * wfun (x + y)"

def chunk_lemma(text, name):
    """Split `lemma name ...` in text into chunk lemmas + a short main lemma."""
    lines = text.split("\n")
    # locate header
    start = next(i for i, l in enumerate(lines) if l.startswith(f"lemma {name} "))
    hdr_end = next(i for i in range(start, len(lines)) if lines[i].rstrip().endswith(":= by"))
    header = lines[start:hdr_end + 1]
    # box from header
    hs = " ".join(header)
    bx = re.findall(r"\(hx1 : " + RAT + r" ≤ x\) \(hx2 : x ≤ " + RAT + r"\)", hs)[0]
    by = re.findall(r"\(hy1 : " + RAT + r" ≤ y\) \(hy2 : y ≤ " + RAT + r"\)", hs)[0]
    box = (parse_rat(bx[0]), parse_rat(bx[1]), parse_rat(by[0]), parse_rat(by[1]))
    # body: until the next blank line followed by non-indented text
    end = hdr_end + 1
    while end < len(lines) and (lines[end].startswith("  ") or lines[end].strip() == ""):
        end += 1
    body = [l for l in lines[hdr_end + 1:end] if l.strip()]
    tree = parse_block(body, 2)
    n_leaves = tree.leaves()
    chunks = []
    main = render(tree, 2, box, chunks, name, NAMES0, 0)
    # the root itself may have been turned into a single chunk; that is fine
    out = []
    for cname, (a, b, c, d), cbody in chunks:
        out.append("set_option maxHeartbeats 10000000 in")
        out.append(f"lemma {cname} (x y : ℝ) (hx1 : {fmt_rat(a)} ≤ x) (hx2 : x ≤ {fmt_rat(b)})")
        out.append(f"    (hy1 : {fmt_rat(c)} ≤ y) (hy2 : y ≤ {fmt_rat(d)}) :")
        out.append(f"    {GOAL} := by")
        out.extend(cbody)
        out.append("")
    # main lemma keeps the original header (with its set_option line just above, if any)
    pre = start
    while lines[pre - 1].startswith("set_option maxHeartbeats") or lines[pre - 1].startswith("/-- "):
        pre -= 1
    # drop a docstring right above? keep it: it is above set_option; fine either way
    new = lines[:pre] + out + lines[pre:hdr_end + 1] + main + lines[end:]
    print(f"[chunk] {name}: {n_leaves} leaves -> {len(chunks)} chunks", file=sys.stderr)
    return "\n".join(new)

from cells_transform import finalize_shifts
if not os.environ.get("NO_CELL_TRANSFORM"):
    for rel in ORDER:
        if rel.startswith("ThreePoint/Cells"):
            transform_cells(open(os.path.join(LAB, rel), encoding="utf-8").read())
    finalize_shifts()
parts = []   # list of (rel, text)
for rel in ORDER:
    text = open(os.path.join(LAB, rel), encoding="utf-8").read()
    if rel.startswith("ThreePoint/Cells") and not os.environ.get("NO_CELL_TRANSFORM"):
        text = transform_cells(text)
    if rel == "ThreePoint/Main.lean":
        # drop the ratio theorem (needs eventually_Ncount_pos only for the ratio form; not needed)
        for nm in ("pair_0_1", "pair_1_1", "pair_0_0", "pair_0_2"):
            text = chunk_lemma(text, nm)
    parts.append((rel, strip_module(text, rel)))
    if rel == "ThreePoint/Base.lean":
        parts.append(("aux", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "aux.lean"), encoding="utf-8").read()))
        parts.append(("shifts", SHIFTS[0]))
        if os.environ.get("CHECKER"):
            parts.append(("checker", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "checker.lean"), encoding="utf-8").read()))
            if os.environ.get("MODE") == "four" and os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data4.lean")):
                parts.append(("data4", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data4.lean"), encoding="utf-8").read()))
            if os.environ.get("MODE") == "five":
                parts.append(("checker5", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "checker5.lean"), encoding="utf-8").read()))
                if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data5.lean")):
                    parts.append(("data5", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data5.lean"), encoding="utf-8").read()))
            if os.environ.get("MODE") == "fourb":
                parts.append(("checker5", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "checker5.lean"), encoding="utf-8").read()))
                parts.append(("checker4b", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "checker4b.lean"), encoding="utf-8").read()))
                if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data4b.lean")):
                    parts.append(("data4b", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data4b.lean"), encoding="utf-8").read()))
            if os.environ.get("MODE") == "w":
                nm = os.environ["WNAME"]; dn = os.environ.get("WDATA", f"data_{nm}.lean")
                for f in (f"checker_{nm}.lean", dn, "tail_common.lean"):
                    parts.append((f, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f), encoding="utf-8").read()))
            if os.environ.get("EXTRA"):
                for f in os.environ["EXTRA"].split(","):
                    parts.append((f, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f), encoding="utf-8").read()))
            if os.environ.get("CHK5ONLY"):
                parts.append(("checker5", open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "checker5.lean"), encoding="utf-8").read()))

_hd = os.path.join(os.path.dirname(os.path.abspath(__file__)), f"head_{os.environ['WNAME']}.lean") if os.environ.get("MODE") == "w" and os.environ.get("WNAME") and os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), f"head_{os.environ['WNAME']}.lean")) else os.path.join(os.path.dirname(os.path.abspath(__file__)), "head.lean")
head = open(_hd, encoding="utf-8").read()
tail = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), ({"four": "tail4.lean", "five": "tail5.lean", "fourb": "tail4b.lean"}.get(os.environ.get("MODE"), "tail.lean") if os.environ.get("MODE") != "w" else f"tail_{os.environ['WNAME']}.lean")), encoding="utf-8").read()
imp = "\n".join(f"import {m}" for m in imports)
head = head.replace("{{IMPORTS}}", imp)
if os.environ.get("LINTER_OFF"):
    head += "\nset_option linter.all false\n"
if os.environ.get("NOASYNC"):
    head += "\nset_option Elab.async false\n"
if os.environ.get("PROFILE"):
    head += "\nset_option profiler true\nset_option profiler.threshold 200\n"
if os.environ.get("MODE") in ("four", "five", "fourb", "w"):
    parts = [(rel, p) for rel, p in parts if not (rel.startswith("ThreePoint/Cells") or rel == "ThreePoint/Main.lean" or rel == "shifts")]
if os.environ.get("KEEP"):
    pats = os.environ["KEEP"].split(",")
    parts = [(rel, p) for rel, p in parts if any(k in rel for k in pats)]
    tail = ""
if os.environ.get("MINI"):
    keep = {"Zeta23Ext/StableRankTrace.lean", "Zeta23Ext/Bridge/Defs.lean", "ThreePoint/Base.lean", "aux", "shifts", "ThreePoint/Cells0.lean"}
    parts = [(rel, p) for rel, p in parts if rel in keep]
    tail = ""
out = head + "".join(p for _, p in parts) + tail
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), os.environ.get("OUT", "Solution.lean")), "w", encoding="utf-8") as f:
    f.write(out)
print(f"wrote Solution.lean: {len(out.encode('utf-8'))} bytes; imports: {imports}", file=sys.stderr)
