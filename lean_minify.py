#!/usr/bin/env python3
"""lean_minify.py -- shrink a single-file Lean 4 board submission without changing what it proves.

usage:
  lean_minify.py IN.lean OUT.lean [--passes P,P,...] [--map MAP.txt] [--report]
  lean_minify.py IN.lean --measure            # bytes after each pass alone, and all combined

Passes (always applied in this order, whatever order they are listed in):
  comments  drop `--`, `/- -/`, `/-- -/`, `/-! -/` (nested); the leading header comment block is kept verbatim
  tree      binary-tree literals `(N l ⟨a,b⟩ r)` written with a `local notation "N"` -> prefix notations
            `L a b` (leaf) / `M l a b r` (node) / `P a b r` / `Q l a b`, which expand to the same syntax
  hex       decimal natural-number literals -> `0x…` where that is strictly shorter (same `OfNat` literal)
  ns        namespace atoms declared in the file and absent from every imported source -> short fresh atoms
  ids       declaration-name atoms declared in the file and absent from every imported source -> short fresh
            atoms (the scored theorems and the board constants are never renamed; neither are type names,
            structure fields, instance-header atoms, nor any atom that may also be a binder name, so the
            elaborated terms keep their binder names)
  walk      top-level commands that differ only in numerals / identifiers (the certificate's walk, box, root,
            `_ok` lines) -> one `local macro` per shape, `set_option hygiene false`, so every call expands to
            exactly the command text it replaced
  ws        delete blank lines and trailing spaces; collapse interior runs of spaces when no later line of
            the same command could be column-compared with a shifted token; leading indentation untouched

Every rename is atom-level and bijective onto atoms that occur nowhere in the file or in the imported
sources (Lean core, Mathlib and the other packages, Zeta23, ChallengeDeps); `--map` writes the atom map
(`old new` per line) for an olean-level comparison of the two builds.

Self-checks run on every invocation: the lexer round-trips the input; the header block is byte-identical;
the statements of the protected theorems are byte-identical; no `sorry` / `native_decide` / `axiom` is
introduced; the output is at most 2,000,000 bytes.

Validation of an output (bench/, holds bench/.leanlock; see bench/build_min.sh and bench/OleanDiff.lean):
  bench/build_min.sh OUT.lean ModName        # build with the zeta23 LEAN_PATH, then ReplayHarness on the olean
  lean --run bench/OleanDiff.lean bench/<Orig>.olean bench/ModName.olean MAP   # MAP = --map file plus a line
                                             # `<Orig> ModName`; every constant must be identical modulo the
                                             # renaming (up to hygienic binder-name suffixes)
  bench/ChkSig_<Mod>.lean                    # `#check` (also pp.all) and `#print axioms` of the scored theorems
"""
import argparse
import hashlib
import os
import pickle
import re
import sys
from collections import Counter, defaultdict

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)   # certificate literals have ~10^5 digits

PASS_ORDER = ['comments', 'tree', 'ns', 'ids', 'walk', 'hex', 'ws']
PROTECTED = {'candidate_strict_improvement', 'candidate_critical_line_bound',
             'candidate_critical_line_bound_cumulative', 'currentRecordKappa', 'candidateKappa'}
SCORED = ['candidate_strict_improvement', 'candidate_critical_line_bound',
          'candidate_critical_line_bound_cumulative']

HOME = os.path.expanduser('~')
DEFAULT_ZETA23 = os.path.join(HOME, 'work', 'riemann-submission', 'zeta23')

# words that must never become slots of a macro or fresh names (dependency scan covers the rest)
RESERVED = set('''theorem lemma def noncomputable abbrev instance example structure inductive class where by
fun have show from at with match if then else do let in calc exact rw simp decide intro intros apply refine
obtain rcases cases induction unfold omega norm_num linarith nlinarith ring ring_nf field_simp push_cast
exact_mod_cast constructor use left right trivial rfl sorry native_decide private protected open namespace
section end variable universe set_option local scoped attribute deriving mutual termination_by decreasing_by
partial unsafe nonrec macro syntax notation infix infixl infixr prefix postfix true false Type Sort Prop
forall exists this axiom opaque export import macro_rules elab first try repeat all_goals any_goals
fun_prop positivity gcongr congr ext funext simp_all aesop and or not mod div'''.split())

# ------------------------------------------------------------------------------------------------ lexer

def _letter_like(o):
    return ((0x3b1 <= o <= 0x3c9 and o != 0x3bb) or (0x391 <= o <= 0x3a9 and o not in (0x3a0, 0x3a3))
            or 0x3ca <= o <= 0x3fb or 0x1f00 <= o <= 0x1ffe or 0x2100 <= o <= 0x214f
            or 0x1d49c <= o <= 0x1d59f)


def _sub_alnum(o):
    return 0x2080 <= o <= 0x2089 or 0x2090 <= o <= 0x209c or 0x1d62 <= o <= 0x1d6a or o == 0x2c7c


def id_first(c):
    return ('a' <= c <= 'z') or ('A' <= c <= 'Z') or c == '_' or _letter_like(ord(c))


def id_rest(c):
    return (('a' <= c <= 'z') or ('A' <= c <= 'Z') or ('0' <= c <= '9') or c in "_'!?"
            or _letter_like(ord(c)) or _sub_alnum(ord(c)))


DIG = '0123456789'
HEXD = '0123456789abcdefABCDEF'
CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|u\{[0-9a-fA-F]+\}|[\\'\"ntr])|[^\\'\n])'")


class LexError(Exception):
    pass


def lex(s):
    """Tokens (kind, text). Kinds: nl ws lc bc str chr num numx id sym.
    `num` is a plain decimal literal that may be rewritten; `numx` is any other numeric token
    (0x/0b/0o, scientific, field index)."""
    toks = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c == '\n':
            toks.append(('nl', c)); i += 1; continue
        if c in ' \t\r':
            j = i
            while j < n and s[j] in ' \t\r':
                j += 1
            toks.append(('ws', s[i:j])); i = j; continue
        if c == '-' and s.startswith('--', i):
            j = s.find('\n', i)
            j = n if j < 0 else j
            toks.append(('lc', s[i:j])); i = j; continue
        if c == '/' and s.startswith('/-', i):
            depth, j = 1, i + 2
            while depth:
                if j >= n:
                    raise LexError('unterminated block comment at %d' % i)
                if s.startswith('-/', j):
                    depth -= 1; j += 2
                elif s.startswith('/-', j):
                    depth += 1; j += 2
                else:
                    j += 1
            toks.append(('bc', s[i:j])); i = j; continue
        if c == '"':
            j = i + 1
            while True:
                if j >= n:
                    raise LexError('unterminated string at %d' % i)
                if s[j] == '\\':
                    j += 2; continue
                if s[j] == '"':
                    j += 1; break
                j += 1
            toks.append(('str', s[i:j])); i = j; continue
        if c == "'":
            m = CHAR_RE.match(s, i)
            if m:
                toks.append(('chr', m.group())); i = m.end(); continue
            toks.append(('sym', c)); i += 1; continue
        if c in DIG:
            after_dot = bool(toks) and toks[-1] == ('sym', '.')
            j = i
            if after_dot:
                while j < n and s[j] in DIG:
                    j += 1
                toks.append(('numx', s[i:j])); i = j; continue
            if c == '0' and i + 1 < n and s[i + 1] in 'xXbBoO':
                j = i + 2
                while j < n and (s[j] in HEXD or s[j] == '_'):
                    j += 1
                toks.append(('numx', s[i:j])); i = j; continue
            while j < n and s[j] in DIG:
                j += 1
            if j < n and s[j] in '.eE':
                # scientific literal (Lean consumes a trailing '.' even without digits)
                if s[j] == '.':
                    j += 1
                    while j < n and s[j] in DIG:
                        j += 1
                if j < n and s[j] in 'eE':
                    k = j + 1
                    if k < n and s[k] in '+-':
                        k += 1
                    if k < n and s[k] in DIG:
                        j = k
                        while j < n and s[j] in DIG:
                            j += 1
                toks.append(('numx', s[i:j])); i = j; continue
            toks.append(('num', s[i:j])); i = j; continue
        if c == 'r' and i + 1 < n and s[i + 1] in '"#':
            m = re.compile(r'r(#*)"').match(s, i)
            if m:
                close = '"' + m.group(1)
                j = s.find(close, m.end())
                if j < 0:
                    raise LexError('unterminated raw string at %d' % i)
                j += len(close)
                toks.append(('str', s[i:j])); i = j; continue
        if id_first(c) or c == '«':
            j = i
            while True:
                if s[j] == '«':
                    k = s.find('»', j + 1)
                    if k < 0:
                        raise LexError('unterminated «» at %d' % j)
                    j = k + 1
                else:
                    j += 1
                    while j < n and id_rest(s[j]):
                        j += 1
                if j + 1 < n and s[j] == '.' and (id_first(s[j + 1]) or s[j + 1] == '«'):
                    j += 1
                    continue
                break
            toks.append(('id', s[i:j])); i = j; continue
        toks.append(('sym', c)); i += 1
    return toks


def detok(toks):
    return ''.join(t for _, t in toks)


def split_components(ident):
    """Components of a (possibly dotted, possibly «»-escaped) identifier; escaped parts keep their «»."""
    out, cur, i = [], [], 0
    while i < len(ident):
        c = ident[i]
        if c == '«':
            k = ident.index('»', i)
            cur.append(ident[i:k + 1]); i = k + 1; continue
        if c == '.':
            out.append(''.join(cur)); cur = []; i += 1; continue
        cur.append(c); i += 1
    out.append(''.join(cur))
    return out


def header_split(s):
    """(header, body): the header is the leading run of whitespace and comments, ending with the last
    comment of that run.  It is never modified by any pass."""
    toks = lex(s)
    k = 0
    while k < len(toks) and toks[k][0] in ('ws', 'nl', 'lc', 'bc'):
        k += 1
    last = -1
    for i in range(k):
        if toks[i][0] in ('lc', 'bc'):
            last = i
    head = detok(toks[:last + 1])
    return head, s[len(head):]


def with_body(fn):
    """Apply a body transformer to everything after the header."""
    def run(s, ctx):
        head, body = header_split(s)
        new = fn(body, ctx)
        if head and body.startswith('\n'):
            new = '\n' + new.lstrip('\n')
        return head + new
    run.__name__ = fn.__name__
    return run

# ------------------------------------------------------------------------------------------ line model


def token_lines(toks):
    """Split a token list into logical lines (lists of tokens) at 'nl' tokens."""
    lines, cur = [], []
    for t in toks:
        if t[0] == 'nl':
            lines.append(cur); cur = []
        else:
            cur.append(t)
    lines.append(cur)
    return lines


def line_info(line):
    """(indent, token start columns of non-ws tokens, total length, complex?)"""
    col, cols, cx = 0, [], False
    for k, t in line:
        if '\n' in t:
            cx = True
        if k != 'ws':
            cols.append(col)
        col += len(t)
    indent = len(line[0][1]) if line and line[0][0] == 'ws' else 0
    if line and all(k == 'ws' for k, _ in line):
        indent = None  # blank
    return indent, cols, col, cx


def shift_safe(infos, i, c0):
    """Moving the tokens of line i that start at columns > c0 to the left (new columns > c0) cannot change
    any layout check if no later line of the same top-level command has a token starting at a column in
    [c0 + 1, old line length]."""
    hi = infos[i][2]
    for j in range(i + 1, len(infos)):
        ind, cols, _, cx = infos[j]
        if ind is None:
            continue
        if ind == 0:
            break
        if cx:
            return False
        if any(c0 + 1 <= c <= hi for c in cols):
            return False
    return True

# ------------------------------------------------------------------------------------------- comments


@with_body
def pass_comments(body, ctx):
    toks = lex(body)
    lines = token_lines(toks)
    out = []
    for line in lines:
        if not any(k in ('lc', 'bc') for k, _ in line):
            out.append(detok(line)); continue
        phys = []          # finished physical lines produced from this logical line
        cur = []           # pieces of the current physical line
        for idx, (k, t) in enumerate(line):
            if k == 'lc':
                continue
            if k == 'bc':
                rest = line[idx + 1:]
                if '\n' in t:
                    phys.append(''.join(cur).rstrip())
                    end_col = len(t) - t.rfind('\n') - 1
                    cur = [' ' * end_col]
                elif rest and any(kk != 'ws' for kk, _ in rest):
                    # inline comment followed by code: keep the columns (the ws pass may collapse later)
                    cur.append(' ' * len(t))
                continue
            cur.append(t)
        phys.append(''.join(cur).rstrip())
        for p in phys:
            if p.strip():
                out.append(p)
    return '\n'.join(out)

# ------------------------------------------------------------------------------------------------- ws


@with_body
def pass_ws(body, ctx):
    toks = lex(body)
    lines = token_lines(toks)
    infos = [line_info(l) for l in lines]
    out = []
    for i, line in enumerate(lines):
        ind, cols, length, cx = infos[i]
        if ind is None or not line:
            continue
        while line and line[-1][0] == 'ws':
            line = line[:-1]
        if not cx:
            runs = [(j, sum(len(t) for _, t in line[:j])) for j in range(1, len(line))
                    if line[j][0] == 'ws' and len(line[j][1]) > 1]
            if runs and shift_safe(infos, i, runs[0][1]):
                line = [(k, ' ') if (j > 0 and k == 'ws') else (k, t) for j, (k, t) in enumerate(line)]
        out.append(detok(line))
    return '\n'.join(out) + ('\n' if body.endswith('\n') else '')

# ------------------------------------------------------------------------------------------------ hex


@with_body
def pass_hex(body, ctx):
    toks = lex(body)
    out = []
    sig = []  # last two significant tokens
    for k, t in toks:
        if k == 'num':
            v = int(t)
            h = '0x%x' % v
            guarded = len(sig) >= 2 and sig[-2] == ('id', 'set_option')
            if len(h) < len(t) and not guarded:
                ctx['stats']['hex_literals'] += 1
                ctx['stats']['hex_saved'] += len(t) - len(h)
                t = h
        out.append((k, t))
        if k not in ('ws', 'nl', 'lc', 'bc'):
            sig.append((k, t))
            sig = sig[-2:]
    return detok(out)

# ------------------------------------------------------------------------------- dependency word scan


def toolchain_dir(zeta23):
    try:
        tc = open(os.path.join(zeta23, 'lean-toolchain')).read().strip()
    except OSError:
        return None
    name = tc.replace('/', '--').replace(':', '---')
    d = os.path.join(HOME, '.elan', 'toolchains', name)
    return d if os.path.isdir(d) else None


def dep_source_roots(zeta23):
    roots = [os.path.join(zeta23, 'Zeta23'), os.path.join(zeta23, 'Zeta23.lean'),
             os.path.join(zeta23, 'comparator', 'ChallengeDeps'),
             os.path.join(zeta23, 'comparator', 'ChallengeDeps.lean'),
             os.path.join(zeta23, '.lake', 'packages')]
    tc = toolchain_dir(zeta23)
    if tc:
        roots.append(os.path.join(tc, 'src', 'lean'))
    return [r for r in roots if os.path.exists(r)]


def iter_lean_files(roots):
    for r in roots:
        if os.path.isfile(r):
            yield r; continue
        for dp, dns, fns in os.walk(r):
            dns[:] = [d for d in dns if d not in ('build', '.git')]
            for fn in fns:
                if fn.endswith('.lean'):
                    yield os.path.join(dp, fn)


def dep_words(zeta23, cache_dir='/tmp'):
    """Every maximal [A-Za-z0-9_] run in every imported source file.  An atom absent from this set
    occurs in no imported identifier (the scan over-approximates, so the test is conservative)."""
    roots = dep_source_roots(zeta23)
    key = hashlib.sha256(repr([(r, os.path.getmtime(r)) for r in roots]).encode()).hexdigest()[:16]
    cache = os.path.join(cache_dir, 'lean_minify_depwords_%s.pkl' % key)
    if os.path.exists(cache):
        with open(cache, 'rb') as f:
            return pickle.load(f)
    words = set()
    rx = re.compile(rb'[A-Za-z0-9_]+')
    nfiles = 0
    for p in iter_lean_files(roots):
        with open(p, 'rb') as f:
            words.update(rx.findall(f.read()))
        nfiles += 1
    words = {w.decode() for w in words}
    if nfiles < 1000:
        raise RuntimeError('dependency scan found only %d source files under %s' % (nfiles, roots))
    with open(cache, 'wb') as f:
        pickle.dump(words, f)
    return words

# ----------------------------------------------------------------------------------------- fresh atoms


def file_atoms(s):
    """Every identifier component and every word inside string literals / notation tokens of s."""
    atoms = set()
    for k, t in lex(s):
        if k == 'id':
            atoms.update(split_components(t))
        elif k in ('str', 'lc', 'bc'):
            atoms.update(re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*", t))
    return atoms


def fresh_atoms(taken, dep):
    import string
    first = string.ascii_uppercase + string.ascii_lowercase
    rest = first + string.digits
    def gen():
        for a in first:
            yield a
        for a in first:
            for b in rest:
                yield a + b
        for a in first:
            for b in rest:
                for c in rest:
                    yield a + b + c
    for cand in gen():
        if cand in taken or cand in dep or cand in RESERVED:
            continue
        yield cand


def rename_atoms(s, amap):
    toks = lex(s)
    out = []
    for k, t in toks:
        if k == 'id':
            comps = split_components(t)
            if any(c in amap for c in comps):
                t = '.'.join(amap.get(c, c) for c in comps)
        out.append((k, t))
    return detok(out)


def atom_counts(s):
    cnt = Counter()
    for k, t in lex(s):
        if k == 'id':
            cnt.update(split_components(t))
    return cnt


SIMPLE_ATOM = re.compile(r'^[A-Za-z_][A-Za-z0-9_]*$')


def allocate(cands, cnt, s, ctx):
    """Give the most frequent candidate atoms the shortest fresh atoms; keep only strict gains."""
    dep = ctx['dep']()
    taken = file_atoms(s) | set(ctx['taken'])
    gen = fresh_atoms(taken, dep)
    amap = {}
    for a in sorted(cands, key=lambda a: (-cnt[a] * len(a), a)):
        new = next(gen)
        if len(new) < len(a):
            amap[a] = new
            ctx['taken'].add(new)
    return amap


def declared_namespaces(s):
    toks = [t for t in lex(s) if t[0] not in ('ws', 'nl', 'lc', 'bc')]
    out = set()
    for i in range(len(toks) - 1):
        if toks[i] == ('id', 'namespace') and toks[i + 1][0] == 'id':
            out.update(split_components(toks[i + 1][1]))
    return out


DECL_KW = {'def', 'theorem', 'lemma', 'abbrev', 'opaque', 'axiom', 'instance'}
TYPE_KW = {'structure', 'inductive', 'class'}


def declared_atoms(s):
    """(decl atoms, type atoms, atoms that must not be renamed: instance headers, structure / inductive
    bodies, `deriving` lines, and every atom that may be a binder name)."""
    toks = [t for t in lex(s) if t[0] not in ('ws', 'lc', 'bc')]
    decl, types, avoid = set(), set(), set()
    i = 0
    while i < len(toks):
        k, t = toks[i]
        if k == 'id' and (t in DECL_KW or t in TYPE_KW):
            j = i + 1
            while j < len(toks) and toks[j][0] == 'nl':
                j += 1
            if j < len(toks) and toks[j][0] == 'id' and toks[j][1] not in RESERVED:
                comps = split_components(toks[j][1])
                if t in TYPE_KW:
                    types.add(comps[-1])
                else:
                    decl.add(comps[-1])
            if t == 'instance':
                j = i + 1
                while j < len(toks) and toks[j] not in (('sym', ':'), ('id', 'where')) and j < i + 200:
                    if toks[j][0] == 'id':
                        avoid.update(split_components(toks[j][1]))
                    j += 1
        i += 1
    # structure bodies: everything from `structure X` to the next column-0 line
    lines = s.split('\n')
    i = 0
    while i < len(lines):
        if re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(structure|inductive|class)\b', lines[i]):
            j = i
            while True:
                for k, t in lex(lines[j]):
                    if k == 'id':
                        avoid.update(split_components(t))
                j += 1
                if j >= len(lines) or (lines[j][:1] not in (' ', '\t', '|') and lines[j].strip()):
                    break
                if not lines[j].strip():
                    break
            i = j
        else:
            i += 1
    for line in lines:
        if 'deriving' in line:
            for k, t in lex(line):
                if k == 'id':
                    avoid.update(split_components(t))
    avoid |= binder_atoms(toks)
    return decl, types, avoid


BINDER_KW = {'fun', 'λ', '∀', '∃', '∃!', 'intro', 'intros', 'rintro', 'obtain', 'rcases', 'cases', 'induction',
             'with', 'have', 'let', 'set', 'generalize', 'case', 'next', 'rename_i', 'by_cases', 'by_contra',
             'choose', 'ext', 'funext', 'filter_upwards', 'peel', 'lift', 'suffices'}
BINDER_SYM = {'|', '∑', '∏', '⨆', '⨅', '⋃', '⋂'}
BINDER_STOP = {('sym', ','), ('id', 'at'), ('id', 'using'), ('id', 'from'), ('id', 'in'), ('id', 'then')}


def binder_atoms(toks):
    """Over-approximation of the identifiers used as binder names (a renamed binder name would change the
    binder names stored in the elaborated terms, so such atoms are never renamed):
      * every identifier in a bracket group `( x y : …`, `{ x : …`, `⦃ x : …`, `[ x : …` before the `:`;
      * every undotted identifier after a binding keyword / symbol up to `=>`, `:=`, `:` or a stop token."""
    sig = [t for t in toks if t[0] not in ('ws', 'lc', 'bc')]
    out = set()
    n = len(sig)
    for i, (k, t) in enumerate(sig):
        if k == 'sym' and t in '({⦃[':
            j, names = i + 1, []
            while j < n and sig[j][0] == 'id':
                names.append(sig[j][1]); j += 1
            if names and j < n and sig[j] == ('sym', ':') and not (j + 1 < n and sig[j + 1] == ('sym', '=')):
                out.update(nm for nm in names if '.' not in nm)   # binder names are never dotted
        if (k == 'id' and t in BINDER_KW) or (k == 'sym' and t in BINDER_SYM):
            j, depth = i + 1, 0
            while j < n and j < i + 400:
                kk, tt = sig[j]
                if kk == 'nl' and depth == 0:
                    break
                if kk == 'sym' and tt in '([{⟨⦃':
                    depth += 1
                elif kk == 'sym' and tt in ')]}⟩⦄':
                    if depth == 0:
                        break
                    depth -= 1
                elif kk == 'sym' and tt == '=' and j + 1 < n and sig[j + 1] == ('sym', '>'):
                    break
                elif kk == 'sym' and tt == ':' and depth == 0:
                    break
                elif (kk, tt) in BINDER_STOP and depth == 0:
                    break
                elif kk == 'id' and '.' not in tt:
                    out.add(tt)
                j += 1
    return out


@with_body
def pass_ns(body, ctx):
    dep = ctx['dep']()
    ns = declared_namespaces(body)
    _, types, avoid = declared_atoms(body)
    cands = {a for a in ns if SIMPLE_ATOM.match(a) and a not in dep and a not in PROTECTED
             and a not in types and a not in avoid and a not in RESERVED}
    skipped = sorted(a for a in ns if a not in cands)
    cnt = atom_counts(body)
    amap = allocate(cands, cnt, body, ctx)
    ctx['amap'].update(amap)
    ctx['notes'].append('ns: renamed %s; kept %s' % (
        ', '.join('%s->%s' % kv for kv in sorted(amap.items())), ', '.join(skipped)))
    return rename_atoms(body, amap)


@with_body
def pass_ids(body, ctx):
    dep = ctx['dep']()
    decl, types, avoid = declared_atoms(body)
    ns = declared_namespaces(body)
    cands = {a for a in decl if SIMPLE_ATOM.match(a) and a not in dep and a not in PROTECTED
             and a not in types and a not in avoid and a not in ns and a not in RESERVED and len(a) > 2}
    cnt = atom_counts(body)
    amap = allocate(cands, cnt, body, ctx)
    ctx['amap'].update(amap)
    ctx['notes'].append('ids: %d of %d declared atoms renamed' % (len(amap), len(decl)))
    return rename_atoms(body, amap)

# ------------------------------------------------------------------------------------------- scopes


def scope_ids(lines):
    """Scope instance id for every line (namespace / section / mutual nesting, column-0 commands)."""
    stack, ids, counter, cur = [], [], 0, 0
    for line in lines:
        m = re.match(r'^(noncomputable\s+)?(namespace|section|end|mutual)\b\s*([^\s]*)', line)
        if m:
            kw = m.group(2)
            if kw in ('namespace', 'section', 'mutual'):
                counter += 1
                stack.append((kw, counter))
                cur = counter
                ids.append(('open', cur))
                continue
            if kw == 'end':
                if stack:
                    stack.pop()
                counter += 1
                cur = counter
                ids.append(('close', cur))
                continue
        ids.append((('mutual' if any(k == 'mutual' for k, _ in stack) else 'scope'), cur))
    return ids

# --------------------------------------------------------------------------------------------- walk


CHUNK_START = re.compile(r'^(theorem|lemma|def|noncomputable def|abbrev)\s')
MAX_MACRO_PARAMS = 24      # wider shapes (e.g. whole tree literals) are left to the tree pass
MIN_MACRO_SAVING = 200     # bytes; below this a macro is clutter


def chunks_of(lines):
    """Top-level command chunks: a column-0 line + following indented non-blank lines."""
    out, i = [], 0
    while i < len(lines):
        if lines[i] and not lines[i][0].isspace():
            j = i + 1
            while j < len(lines) and lines[j][:1] in (' ', '\t') and lines[j].strip():
                j += 1
            out.append((i, j))
            i = j
        else:
            i += 1
    return out


def chunk_shape(text):
    """(shape key, slot values, slot kinds) or None if the chunk is not templatable."""
    toks = lex(text)
    if any(k in ('lc', 'bc', 'str', 'chr') for k, _ in toks):
        return None
    key, vals, kinds = [], [], []
    for idx, (k, t) in enumerate(toks):
        prev = toks[idx - 1] if idx else None
        nxt = toks[idx + 1] if idx + 1 < len(toks) else None
        adj_bad = (prev is not None and prev[0] == 'sym' and prev[1] in '.$') or \
                  (nxt is not None and nxt[0] == 'sym' and nxt[1] in '.:')
        if k == 'num' and not adj_bad:
            key.append(('#',)); vals.append(t); kinds.append('num')
        elif k == 'id' and not adj_bad and t not in RESERVED and '«' not in t \
                and SIMPLE_ID.match(t):
            key.append(('@',)); vals.append(t); kinds.append('ident')
        else:
            key.append((k, t))
    return tuple(key), vals, kinds


SIMPLE_ID = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")


def pick_tokens(n, taken):
    """n new keyword tokens, none of them an atom of the region where they are active."""
    out = []
    if n == 0:
        return out
    for c in 'ABCDFGHIJKLMOPQRSTUVWXYZ' + 'abcdefghijklmnopqrstuvwxyz':
        if c not in taken and c not in RESERVED:
            out.append(c)
            if len(out) == n:
                return out
    for a in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
        for b in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789':
            if a + b not in taken:
                out.append(a + b)
                if len(out) == n:
                    return out
    raise RuntimeError('no free macro tokens')


def scope_end(lines, i):
    """Index of the line holding the `end` that closes the scope containing line i (len(lines) if the
    line is at the top level).  `local` notations and macros, and their tokens, die there."""
    depth = 0
    for j in range(i, len(lines)):
        m = re.match(r'^(noncomputable\s+)?(namespace|section|end|mutual)\b', lines[j])
        if not m:
            continue
        if m.group(2) == 'end':
            if depth == 0:
                return j
            depth -= 1
        else:
            depth += 1
    return len(lines)


def region_atoms(lines, i, ctx):
    """Atoms that a token introduced at line i must avoid: every atom from line i to the end of the
    enclosing scope, plus every token and fresh atom allocated so far."""
    return file_atoms('\n'.join(lines[i:scope_end(lines, i) + 1])) | set(ctx['taken'])


@with_body
def pass_walk(body, ctx):
    lines = body.split('\n')
    sids = scope_ids(lines)
    groups = defaultdict(list)
    for (i, j) in chunks_of(lines):
        if not CHUNK_START.match(lines[i]):
            continue
        prev = lines[i - 1].rstrip() if i else ''
        if prev and (prev.lstrip().startswith('@[') or prev.endswith(' in') or prev.endswith('-/')):
            continue   # attribute, `… in` or docstring attached to this command: leave it alone
        kind, sid = sids[i]
        if kind != 'scope':
            continue
        text = '\n'.join(lines[i:j])
        sh = chunk_shape(text)
        if sh is None:
            continue
        key, vals, kinds = sh
        groups[(sid, key)].append((i, j, vals, kinds, text))
    plans = []
    for (sid, key), insts in groups.items():
        if len(insts) < 3:
            continue
        nslot = len(insts[0][2])
        kinds = insts[0][3]
        cols = [[inst[2][p] for inst in insts] for p in range(nslot)]
        const = [len(set(c)) == 1 for c in cols]
        # merge slots that agree on every instance
        param_of, params = {}, []
        for p in range(nslot):
            if const[p]:
                continue
            for q in params:
                if cols[q] == cols[p] and kinds[q] == kinds[p]:
                    param_of[p] = q; break
            else:
                param_of[p] = p
                params.append(p)
        if len(params) > MAX_MACRO_PARAMS:
            continue
        plans.append((min(i for i, *_ in insts), sid, key, insts, const, param_of, params, kinds))
    plans.sort()
    replace = {}      # line index of chunk start -> (end, new text)
    inserts = {}      # line index -> macro definition text (inserted before)
    for (first, sid, key, insts, const, param_of, params, kinds) in plans:
        tok = pick_tokens(1, region_atoms(lines, first, ctx))[0]
        pname = {p: 'x%d' % n for n, p in enumerate(params)}
        # macro body: the chunk text with slots replaced
        body_parts = []
        slot = 0
        for item in key:
            if item in (('#',), ('@',)):
                p = slot
                slot += 1
                if const[p]:
                    body_parts.append(insts[0][2][p])
                else:
                    body_parts.append('$' + pname[param_of[p]])
            else:
                body_parts.append(item[1])
        mbody = ''.join(body_parts)
        sig = ' '.join('%s:%s' % (pname[p], kinds[p]) for p in params)
        mdef = ('set_option hygiene false in\nlocal macro "%s " %s : command => `(command|\n%s)'
                % (tok, sig, mbody))
        saved = 0
        calls = []
        for (i, j, vals, _, text) in insts:
            call = tok + ''.join(' ' + vals[p] for p in params)
            # the call must expand to exactly this chunk's text
            exp_parts, slot = [], 0
            for item in key:
                if item in (('#',), ('@',)):
                    exp_parts.append(vals[slot]); slot += 1
                else:
                    exp_parts.append(item[1])
            if ''.join(exp_parts) != text:
                raise AssertionError('template reconstruction failed for chunk at line %d' % (i + 1))
            calls.append((i, j, call))
            saved += len(text.encode()) - len(call.encode())
        if saved - len(mdef.encode()) - 2 < MIN_MACRO_SAVING:
            continue
        inserts[first] = mdef
        for (i, j, call) in calls:
            replace[i] = (j, call)
        ctx['stats']['walk_macros'] += 1
        ctx['stats']['walk_calls'] += len(calls)
        ctx['notes'].append('walk: macro %r, %d params, %d calls, saves %d bytes' % (
            tok, len(params), len(calls), saved - len(mdef.encode())))
        ctx['taken'].add(tok)
    out, i = [], 0
    while i < len(lines):
        if i in inserts:
            out.append(inserts[i])
        if i in replace:
            j, call = replace[i]
            out.append(call)
            i = j
            continue
        out.append(lines[i])
        i += 1
    return '\n'.join(out)

# --------------------------------------------------------------------------------------------- tree


NOTATION_RE = re.compile(r'^local notation "([^"\s]+)" => ([A-Za-z_][\w.]*)\s*$')


class TreeParseError(Exception):
    pass


def parse_tree(toks, pos, node_tok, leaf_toks):
    """T := LEAF | IDENT | '(' NODE T '⟨' num (',' num)* '⟩' T ')' over significant tokens."""
    k, t = toks[pos]
    if k == 'id' and t in leaf_toks:
        return ('nil', t), pos + 1
    if k == 'id' and t != node_tok:
        return ('id', t), pos + 1
    if (k, t) != ('sym', '('):
        raise TreeParseError(pos)
    if toks[pos + 1] != ('id', node_tok):
        raise TreeParseError(pos)
    left, pos = parse_tree(toks, pos + 2, node_tok, leaf_toks)
    if toks[pos] != ('sym', '⟨'):
        raise TreeParseError(pos)
    pos += 1
    nums = []
    while True:
        k, t = toks[pos]
        if k != 'num':
            raise TreeParseError(pos)
        nums.append(t)
        pos += 1
        if toks[pos] == ('sym', ','):
            pos += 1; continue
        if toks[pos] == ('sym', '⟩'):
            pos += 1; break
        raise TreeParseError(pos)
    right, pos = parse_tree(toks, pos, node_tok, leaf_toks)
    if toks[pos] != ('sym', ')'):
        raise TreeParseError(pos)
    return ('node', left, nums, right), pos + 1


def tree_shapes(t, cnt):
    if t[0] != 'node':
        return
    _, l, nums, r = t
    ln, rn = l[0] == 'nil', r[0] == 'nil'
    cnt['L' if ln and rn else 'P' if ln else 'Q' if rn else 'M'] += 1
    tree_shapes(l, cnt)
    tree_shapes(r, cnt)


def emit_polish(t, use, out):
    """Iterative-free recursive emitter (trees are shallow: depth ~ log of the cell count)."""
    if t[0] in ('nil', 'id'):
        out.append(t[1]); return
    _, l, nums, r = t
    ln, rn = l[0] == 'nil', r[0] == 'nil'
    if ln and rn and 'L' in use:
        out.append(use['L']); out.extend(nums); return
    if ln and not rn and 'P' in use:
        out.append(use['P']); out.extend(nums); emit_polish(r, use, out); return
    if rn and not ln and 'Q' in use:
        out.append(use['Q']); emit_polish(l, use, out); out.extend(nums); return
    out.append(use['M']); emit_polish(l, use, out); out.extend(nums); emit_polish(r, use, out)


@with_body
def pass_tree(body, ctx):
    lines = body.split('\n')
    sids = scope_ids(lines)
    # notations per scope
    nots = defaultdict(dict)
    last_not_line = {}
    for i, line in enumerate(lines):
        m = NOTATION_RE.match(line)
        if m:
            nots[sids[i][1]][m.group(1)] = (m.group(2), i)
            last_not_line[sids[i][1]] = i
    if not nots:
        return body
    edits = {}
    defs_added = {}
    for sid, nmap in nots.items():
        # candidate (node, leaf) roles: try each notation as the node constructor
        trees = []
        for (i, j) in chunks_of(lines):
            if sids[i][1] != sid or not re.match(r'^(noncomputable\s+)?def\s', lines[i]):
                continue
            text = '\n'.join(lines[i:j])
            m = re.match(r'^(.*?:=)(\s*)', text, re.S)
            if not m:
                continue
            head, rhs = m.group(1), text[m.end():]
            toks = [t for t in lex(rhs) if t[0] not in ('ws', 'nl')]
            if len(toks) < 2 or toks[0] != ('sym', '(') or toks[1][0] != 'id' or toks[1][1] not in nmap:
                continue
            node_tok = toks[1][1]
            leaf_toks = {k for k in nmap if k != node_tok}
            try:
                tree, end = parse_tree(toks, 0, node_tok, leaf_toks)
            except (TreeParseError, IndexError):
                continue
            if end != len(toks):
                continue
            trees.append((i, j, head, m.group(2), node_tok, tree))
        if not trees:
            continue
        node_toks = {t[4] for t in trees}
        if len(node_toks) != 1:
            continue
        node_tok = node_toks.pop()
        node_rhs = nmap[node_tok][0]
        nil_rhs = {k: v[0] for k, v in nmap.items() if k != node_tok}
        arity = set()
        def arities(t):
            if t[0] == 'node':
                arity.add(len(t[2])); arities(t[1]); arities(t[3])
        cnt = Counter()
        for tr in trees:
            arities(tr[5])
            tree_shapes(tr[5], cnt)
        if len(arity) != 1:
            continue
        ar = arity.pop()
        leaves_used = set()
        def leafset(t):
            if t[0] == 'nil':
                leaves_used.add(t[1])
            elif t[0] == 'node':
                leafset(t[1]); leafset(t[3])
        for tr in trees:
            leafset(tr[5])
        if len(leaves_used) != 1:
            continue
        nil_tok = leaves_used.pop()
        nil_id = nil_rhs[nil_tok]
        toks4 = pick_tokens(4, region_atoms(lines, last_not_line[sid], ctx) | set(nmap))
        roles = dict(zip(['M', 'L', 'P', 'Q'], toks4))
        a = ' '.join('a%d:max' % k for k in range(ar))
        cell = '⟨%s⟩' % ', '.join('a%d' % k for k in range(ar))
        defs = {
            'M': 'local notation:max "%s" l:max %s r:max => %s l %s r' % (roles['M'], a, node_rhs, cell),
            'L': 'local notation:max "%s" %s => %s %s %s %s' % (roles['L'], a, node_rhs, nil_id, cell, nil_id),
            'P': 'local notation:max "%s" %s r:max => %s %s %s r' % (roles['P'], a, node_rhs, nil_id, cell),
            'Q': 'local notation:max "%s" l:max %s => %s l %s %s' % (roles['Q'], a, node_rhs, cell, nil_id),
        }
        use = {'M': roles['M']}
        for r in ('L', 'P', 'Q'):
            # each specialised notation saves 2 bytes (`E ` or ` E`; 4 for L) per use
            gain = cnt[r] * (4 if r == 'L' else 2)
            if gain > len(defs[r]) + 30:
                use[r] = roles[r]
        deftext = '\n'.join('set_option hygiene false in\n' + defs[r] for r in ['M', 'L', 'P', 'Q'] if r in use)
        defs_added[last_not_line[sid]] = deftext
        for (i, j, head, sep, _, tree) in trees:
            out = []
            emit_polish(tree, use, out)
            edits[i] = (j, head + sep + ' '.join(out))
        ctx['taken'].update(use.values())
        ctx['stats']['tree_defs'] += len(trees)
        ctx['notes'].append('tree: %d literals, node shapes %s, notations %s' % (
            len(trees), dict(cnt), {r: use[r] for r in use}))
    out, i = [], 0
    while i < len(lines):
        if i in edits:
            j, text = edits[i]
            out.append(text)
            i = j
            continue
        out.append(lines[i])
        if i in defs_added:
            out.append(defs_added[i])
        i += 1
    return '\n'.join(out)

# ------------------------------------------------------------------------------------------- driver


PASSES = {'comments': pass_comments, 'walk': pass_walk, 'tree': pass_tree, 'hex': pass_hex,
          'ns': pass_ns, 'ids': pass_ids, 'ws': pass_ws}


def statement(s, name):
    """The text of `theorem NAME ... :=` (up to the first `:=` token at the top level)."""
    toks = lex(s)
    for i, (k, t) in enumerate(toks):
        if k == 'id' and t == name and i >= 2 and toks[i - 2] == ('id', 'theorem'):
            j = i
            depth = 0
            while j < len(toks):
                if toks[j] == ('sym', ':') and toks[j + 1] == ('sym', '=') and depth == 0:
                    return detok(toks[i - 2:j])
                if toks[j][0] == 'sym' and toks[j][1] in '([{⟨':
                    depth += 1
                if toks[j][0] == 'sym' and toks[j][1] in ')]}⟩':
                    depth -= 1
                j += 1
    return None


def make_ctx(args):
    cache = {}
    def dep():
        if 'w' not in cache:
            cache['w'] = dep_words(args.zeta23)
        return cache['w']
    return {'dep': dep, 'amap': {}, 'taken': set(), 'notes': [], 'stats': Counter()}


def run_passes(src, passes, ctx):
    s = src
    sizes = []
    for p in PASS_ORDER:
        if p in passes:
            s = PASSES[p](s, ctx)
            sizes.append((p, len(s.encode())))
    return s, sizes


def checks(src, out, passes):
    errs = []
    if detok(lex(src)) != src:
        errs.append('lexer does not round-trip the input')
    if header_split(src)[0] != header_split(out)[0] or not out.startswith(header_split(src)[0]):
        errs.append('header block changed')
    for name in SCORED:
        a, b = statement(src, name), statement(out, name)
        if a is None:
            errs.append('scored theorem %s not found in input' % name)
        elif a != b:
            errs.append('statement of %s changed:\n%r\n%r' % (name, a, b))
    for bad in ('sorry', 'native_decide', 'admit'):
        if atom_counts(out)[bad] > atom_counts(src)[bad]:
            errs.append('%s introduced' % bad)
    for kw in ('axiom', 'opaque', 'implemented_by', 'extern'):
        if atom_counts(out)[kw] > atom_counts(src)[kw]:
            errs.append('%s introduced' % kw)
    if len(out.encode()) > 2_000_000:
        errs.append('output is %d bytes > 2,000,000' % len(out.encode()))
    return errs


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('inp')
    ap.add_argument('out', nargs='?')
    ap.add_argument('--passes', default=','.join(PASS_ORDER),
                    help='comma-separated subset of %s (default: all)' % ','.join(PASS_ORDER))
    ap.add_argument('--measure', action='store_true', help='report bytes after each pass alone and combined')
    ap.add_argument('--map', help='write the atom rename map (old new per line)')
    ap.add_argument('--zeta23', default=DEFAULT_ZETA23, help='zeta23 checkout (imported sources)')
    ap.add_argument('--report', action='store_true')
    args = ap.parse_args()
    src = open(args.inp, encoding='utf-8').read()
    passes = [p for p in args.passes.split(',') if p]
    for p in passes:
        if p not in PASSES:
            ap.error('unknown pass %s' % p)
    n0 = len(src.encode())
    if args.measure:
        print('%-28s %10d' % ('original', n0))
        for p in PASS_ORDER:
            ctx = make_ctx(args)
            s, _ = run_passes(src, [p], ctx)
            errs = checks(src, s, [p])
            print('%-28s %10d  (-%d)%s' % (p + ' alone', len(s.encode()), n0 - len(s.encode()),
                                           '  CHECK FAILED: ' + '; '.join(errs) if errs else ''))
        ctx = make_ctx(args)
        s, sizes = run_passes(src, passes, ctx)
        for p, n in sizes:
            print('%-28s %10d' % ('  cumulative after ' + p, n))
        print('%-28s %10d  (%.1f%%)' % ('combined', len(s.encode()), 100.0 * len(s.encode()) / n0))
        for note in ctx['notes']:
            print('  ' + note)
        return 0
    if not args.out:
        ap.error('OUT.lean required')
    ctx = make_ctx(args)
    out, sizes = run_passes(src, passes, ctx)
    errs = checks(src, out, passes)
    if errs:
        for e in errs:
            print('ERROR: ' + e, file=sys.stderr)
        return 1
    with open(args.out, 'w', encoding='utf-8') as f:
        f.write(out)
    if args.map:
        with open(args.map, 'w') as f:
            for a, b in sorted(ctx['amap'].items()):
                f.write('%s %s\n' % (a, b))
    print('%s: %d -> %d bytes (%.1f%%), sha256 %s' % (
        args.out, n0, len(out.encode()), 100.0 * len(out.encode()) / n0,
        hashlib.sha256(out.encode()).hexdigest()))
    if args.report:
        for p, n in sizes:
            print('  after %-9s %10d' % (p, n))
        for note in ctx['notes']:
            print('  ' + note)
        for k, v in sorted(ctx['stats'].items()):
            print('  %s = %d' % (k, v))
    return 0


if __name__ == '__main__':
    sys.exit(main())
