#!/usr/bin/env python3
"""mk_skel.py SRC.lean DEPS.tsv OUT.lean: the MOPX upload skeleton from Arun's MOP_Solution.lean.

  1. dead declarations: removed exactly as bbaudit/safecut.py does (dead set from the compiled olean, DEPS.tsv; the
     fixpoint that keeps any dead declaration still named in the kept text; `… in` prefixes go with their declaration).
     DEPS.tsv must already mark attributed dead declarations live (deps_mop_k.tsv: an `@[simp]` rfl lemma leaves no
     trace in the compiled terms).
  2. comments: block comments and full-line `--` comments are removed, EXCEPT every block comment that carries a
     copyright, license or attribution notice (kept verbatim); blank lines removed.
  3. our header (Sam's copyright/NOTICE block and the Apache-2.0 §4(b) change notice) is inserted after Arun's two
     header blocks, before the imports; one-line `-- SWAP` markers are inserted at the certificate and constant swap
     points.
No indentation pass (third-party files have one-column indents)."""
import re, sys

KEYS = ("theorem", "lemma", "def", "abbrev", "structure", "instance", "inductive", "class")
NOTICE = re.compile(r"Copyright|SPDX|Apache|NOTICE|[Aa]ttribution|Licensed|License|Adapted from|retain")

OUR_HEADER = """/-
Copyright (c) 2026 Samuel Lavery (github: samlavery). Licensed under Apache-2.0. Built on the author's
riemannzeta.fun submissions attempt-012/013/014/015/016 and on R. Arun Chandru's "master-of-puppets".
NOTICE: reuse or adaptation of this file must retain this copyright and attribution notice
(Apache-2.0 §4(c)) and must state any changes made (§4(b)).
The internal modules are by Samuel Lavery's agent team (bridge-port, am-cert, mvt-engine, window-scope).
-/
/-
Changes (Apache-2.0 §4(b)), by Samuel Lavery's agent team, 2026-10-10. This file is derived from
R. Arun Chandru's riemannzeta.fun submission "master-of-puppets" (2026-10-09, κ = 66812491/99194876,
Apache-2.0; Solution.lean sha256 f7ef331e72e8c34804e196a4cc0c6fdd69bb1c6947a51dfbf60b88a6343aad9d).
* Dead declarations removed: every declaration outside the dependency closure of the three scored
  theorems, computed from the compiled olean (attributed lemmas kept). Non-notice comments removed.
  Every copyright, license and attribution notice is retained verbatim.
* Certificate replaced by a re-optimised eight-point certificate (weights @@W@@, B = @@B@@, c = @@C@@).
* Counting constants unchanged: H_W ≥ 67216841/10⁸ and the matching/pinching chain, so
  κ = (H_W⁻ − B)/(1 − c) = @@KAPPA@@.
-/"""


def main():
    src, deps, out = sys.argv[1:4]
    lines = open(src, encoding="utf-8").read().split("\n")
    L = len(lines)

    # ---- 1. dead declarations (safecut.py's rule) ----
    live, dead = [False] * L, [False] * L
    cands = []
    for row in open(deps, encoding="utf-8"):
        lv, a, b, name = row.rstrip("\n").split("\t")
        a, b = int(a) - 1, min(int(b) - 1, L - 1)
        if lv == "1":
            for j in range(a, b + 1): live[j] = True
            continue
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
    keep = [not (dead[i] and not live[i]) for i in range(L)]

    # ---- 2. comments: keep notice-bearing block comments verbatim, and the file's first block (Arun's author block) ----
    i = 0; first = True
    while i < L:
        if not keep[i]: i += 1; continue
        s = lines[i].strip()
        if s.startswith("/-"):
            depth = 0; j = i
            while j < L:
                depth += lines[j].count("/-") - lines[j].count("-/")
                if depth <= 0: break
                j += 1
            block = "\n".join(lines[i:j + 1])
            tail = lines[j][lines[j].rfind("-/") + 2:]
            if first:
                first = False
            elif not NOTICE.search(block):
                for k in range(i, j + 1): keep[k] = False
                if tail.strip():
                    lines[j] = tail; keep[j] = True
            i = j + 1; continue
        if s.startswith("--") or not s:
            keep[i] = False
        i += 1
    text = [lines[i] for i in range(L) if keep[i]]

    # ---- 3. our header after Arun's two header blocks; swap markers ----
    imp = next(k for k, l in enumerate(text) if l.startswith("import "))
    text = text[:imp] + OUR_HEADER.split("\n") + text[imp:]
    marks = [
        (r"^namespace AMW\.Cert\.PC8C5BF$", "-- SWAP BEGIN certificate: instance + data + full cert + RiemannFail (W8, W8_adm, W8_B, cert_AM)", -3),
        (r"^end RiemannFail$", "-- SWAP END certificate", 2),
        (r"^def cFloor : ℝ", "-- SWAP constants: cFloor = c, pressureSum = B, proposedQ = κ", 0),
        (r"^namespace Opeth\.AMFinal$", "-- SWAP κ literals in actual_dyadic / actual_cumulative", 0),
        (r"^private theorem am_export_candidate_exact", "-- SWAP κ literal in am_export_candidate_exact", 0),
    ]
    for pat, msg, off in marks:
        k = next(k for k, l in enumerate(text) if re.match(pat, l))
        if off < 0:   # place above the `set_option … / noncomputable section` lines that open the instance
            while k > 0 and re.match(r"^(set_option|noncomputable section)", text[k - 1]): k -= 1
        elif off > 0:  # after `end RiemannFail` and its closing `end`
            k += 1
            while k < len(text) and text[k] == "end": k += 1
        text.insert(k, msg)
    res = "\n".join(text)
    open(out, "w", encoding="utf-8").write(res)
    print(f"{src}: {len('\n'.join(open(src, encoding='utf-8').read().split(chr(10))).encode())} B -> {out}: "
          f"{len(res.encode())} B; notice blocks kept: {res.count('Copyright')} 'Copyright' occurrences")


if __name__ == "__main__":
    main()
