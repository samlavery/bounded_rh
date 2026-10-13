#!/usr/bin/env python3
"""Safe byte cuts for an assembled candidate .lean (stage G / n = 8 byte budget).

Usage: safecut.py SRC.lean DEPS.tsv OUT.lean [--no-indent] [--keep-indent LINES]
  DEPS.tsv: `live  startLine  endLine  name` per declaration of the candidate's module, from the COMPILED olean
  (bbaudit/Dep.lean: dependency closure of the three scored theorems).  Never computed from regexes.

Cuts, in order:
  1. dead declarations: every line covered by the range of a dead declaration and by no live one is dropped, but
     only for ranges that open a `theorem`/`lemma`/`def`/`abbrev`/`structure`/`instance`/`inductive` command
     (after its docstring and attributes); `set_option`/`open`/`omit`/`include`/`variable … in` lines directly above go with it;
  2. comments: block comments `/- … -/` (docstrings, banners) and full-line `--` comments, except the header block
     (the first block comment of the file, kept verbatim); blank lines;
  3. every indented line moves one column left (uniform, so layout is preserved; halving breaks bullet blocks);
     `--keep-indent` lists 1-based SOURCE line numbers to leave untouched.
Prints the bytes removed by each cut."""
import re, sys

KEYS = ("theorem", "lemma", "def", "abbrev", "structure", "instance", "inductive", "class")


def main():
    args = sys.argv[1:]
    src, deps, out = args[0], args[1], args[2]
    no_indent = "--no-indent" in args
    keep = set()
    if "--keep-indent" in args:
        keep = {int(x) for x in args[args.index("--keep-indent") + 1].split(",") if x}
    lines = open(src, encoding="utf-8").read().split("\n")
    L = len(lines)
    nb = lambda idxs: sum(len(lines[i].encode()) + 1 for i in idxs)

    # ---- header block: the first block comment (kept verbatim) ----
    h0 = next(i for i, l in enumerate(lines) if l.strip())
    assert lines[h0].lstrip().startswith("/-"), "no header block"
    depth = 0; h1 = h0
    for i in range(h0, L):
        depth += lines[i].count("/-") - lines[i].count("-/")
        if depth <= 0: h1 = i; break
    header = set(range(h0, h1 + 1))

    # ---- 1. dead declarations ----
    live, dead = [False] * L, [False] * L
    cands = []                                   # (name, first line, last line) of removable dead declarations
    for row in open(deps, encoding="utf-8"):
        lv, a, b, name = row.rstrip("\n").split("\t")
        a, b = int(a) - 1, min(int(b) - 1, L - 1)
        if lv == "1":
            for j in range(a, b + 1): live[j] = True
            continue
        # the command keyword after the docstring / attributes
        j = a; d = 0
        while j <= b:
            s = lines[j].strip()
            if d > 0 or s.startswith("/-"):
                d += s.count("/-") - s.count("-/"); j += 1; continue
            s = re.sub(r"^(@\[[^\]]*\]\s*)+", "", s)
            s = re.sub(r"^((private|protected|noncomputable|nonrec|partial|unsafe)\s+)+", "", s)
            break
        if j > b or not s.split() or s.split()[0] not in KEYS: continue
        p = a - 1
        while p >= 0 and re.match(r"\s*(set_option|open|omit|include|variable|unseal|seal|attribute)\b.*\sin\s*$", lines[p]):
            p -= 1
        cands.append((name, p + 1, b))
    # a dead declaration whose name is still written in the kept text (e.g. an unused `simp [foo]` / `norm_num [foo]`
    # argument, which the compiled term does not mention) is kept: iterate to a fixpoint
    while True:
        rm = [False] * L
        for _, a, b in cands:
            for k in range(a, b + 1): rm[k] = True
        kept = "\n".join(lines[i] for i in range(L) if not (rm[i] and not live[i]))
        still = [(n, a, b) for (n, a, b) in cands
                 if re.search(r"(?<![\w.'])" + re.escape(n.split(".")[-1]) + r"(?![\w'])", kept)]
        if not still: break
        cands = [c for c in cands if c not in still]
    for _, a, b in cands:
        for k in range(a, b + 1): dead[k] = True
    drop = [dead[i] and not live[i] and i not in header for i in range(L)]
    cut_dead = nb(i for i in range(L) if drop[i])

    # ---- 2. comments and blank lines ----
    keep_line = [not d for d in drop]
    cut_com = 0; depth = 0
    new_text = list(lines)
    for i in range(L):
        if not keep_line[i] or i in header: continue
        l = lines[i]; s = l.strip()
        if depth > 0 or s.startswith("/-"):
            depth += l.count("/-") - l.count("-/")
            rest = l[l.rfind("-/") + 2:] if depth <= 0 and "-/" in l else ""
            if rest.strip():                      # code after a closing `-/` on the same line
                new_text[i] = rest; cut_com += len(l.encode()) - len(rest.encode())
            else:
                keep_line[i] = False; cut_com += len(l.encode()) + 1
            depth = max(depth, 0)
        elif s.startswith("--") or not s:
            keep_line[i] = False; cut_com += len(l.encode()) + 1

    # ---- 3. indentation: every indented line moves one column left (all indented lines start at column >= 2,
    # so every difference between indented lines, hence every layout relation among them, is preserved, and each
    # stays right of column 0); halving is NOT safe (bullet blocks `· tac` fix the next line's column mid-line) ----
    cut_ind = 0
    if not no_indent:
        idx = [i for i in range(L) if keep_line[i] and i not in header]
        assert all(new_text[i][:1] != " " or new_text[i][:2] == "  " for i in idx), "a line indented by one column"
        for i in idx:
            if new_text[i][:2] == "  " and i + 1 not in keep:
                new_text[i] = new_text[i][1:]; cut_ind += 1

    res = "\n".join(new_text[i] for i in range(L) if keep_line[i] or i in header)
    open(out, "w", encoding="utf-8").write(res)
    tot = len("\n".join(lines).encode())
    print(f"{src}: {tot} B -> {out}: {len(res.encode())} B  (dead declarations -{cut_dead}, comments/blank -{cut_com}, "
          f"indentation -{cut_ind}; total -{tot - len(res.encode())})")


if __name__ == "__main__":
    main()
