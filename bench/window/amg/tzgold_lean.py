#!/usr/bin/env python3
"""(bridge-port) Lean golden tests for T1 and Z (mvt-engine's bench/eight/am8/tz_golden.json) against the genpcell4 instance
MOD (Q = 7): each golden node's state before T1, run through the kernel's `T1` into a packing continuation, must give the
packed state after T1 (gaps, then the 21 pair bounds = the pair intervals, 24 bits each); each golden Z check, through a
copy of the kernel's piece logic (`zpe`, `zpt`) with the logged pyramid reads in place of `lb`, must give its verdict.
Usage: tzgold_lean.py ROOT MOD GOLDEN.json  (writes ROOT/AMW/PCellTZG.lean)"""
import sys, os, json
ROOT, MOD, GJ = sys.argv[1:4]
G = json.load(open(GJ)); Q = 7
PAIRS = [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]
SUMS = [t for t in PAIRS if t[1] - t[0] >= 2]
BIG = 1 << 40
def fields(l, u, A, B): return [x for r in range(Q) for x in (l[r], u[r])] + [x for k in range(len(SUMS)) for x in (A[k], B[k])]
def pack(fs): return sum(x << (24 * i) for i, x in enumerate(fs))
NF = 2 * Q + 2 * len(SUMS)
names = [f"x{i}" for i in range(NF)]
out = [f"""import AMW.{MOD}

/-! ###### golden tests of T1 and Z (bridge-port; mvt-engine's tz_golden.json, TZ.md)

* T1: each golden node's incoming state (`t1_*`, and `rc_*` where step 5's re-clip binds) through the kernel's `T1`
  (pair intervals, the 56 triples, the re-clip, the emptiness test) into a
  continuation that packs the state (24 bits per field: gaps, then the 21 pair bounds) equals the packed state after T1
  (gaps and pair intervals as logged by the sizer).
* Z: each golden check through the kernel's piece logic (`zpe` ends, `zpt` at both ends of every nondegenerate piece, in
  order, stopping at the first failure), with the logged pyramid reads in place of `lb`, gives its verdict (three that pass,
  one with `v` raised past its slack and one with `M = 0` that fail). ###### -/

set_option maxRecDepth 100000

namespace AMW.Cert.PCellTZG

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.{MOD}

/-- the packing continuation -/
def FP : ST := fun {" ".join(names)} _ => {" + ".join(f"Nat.shiftLeft {n} {24 * i}" for i, n in enumerate(names))}

/-- a Z side through the kernel's pieces, with the reads `lbs` (piece order) in place of the pyramid -/
def zsideL (v c p a b n : ℕ) (right : Bool) (lbs : List ℕ) : Bool :=
  iall (fun k => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (zpt v c (Nat.sub p (zpe a b n k)) (lbs.getD k 0) && zpt v c (Nat.sub p (zpe a b n (Nat.add k 1))) (lbs.getD k 0))
      (zpt v c (Nat.sub (zpe a b n k) p) (lbs.getD k 0) && zpt v c (Nat.sub (zpe a b n (Nat.add k 1)) p) (lbs.getD k 0)) right)
    true (Nat.ble (zpe a b n (Nat.add k 1)) (zpe a b n k))) n
"""]
for i, nd in enumerate(G['t1_nodes']):
    bf = nd['before']; af = nd['after']
    cons = bf['cons']
    A = [cons[f"{i_},{j_}"][0] if f"{i_},{j_}" in cons and cons[f"{i_},{j_}"][0] is not None else 0 for (i_, j_) in SUMS]
    B = [cons[f"{i_},{j_}"][1] if f"{i_},{j_}" in cons and cons[f"{i_},{j_}"][1] is not None else BIG for (i_, j_) in SUMS]
    I = af['intervals']
    A2 = [I[f"{i_},{j_}"][0] for (i_, j_) in SUMS]; B2 = [I[f"{i_},{j_}"][1] for (i_, j_) in SUMS]
    l2 = [I[f"{r},{r + 1}"][0] for r in range(Q)]; u2 = [I[f"{r},{r + 1}"][1] for r in range(Q)]
    assert l2 == af['l'] and u2 == af['u']
    st = ", ".join(map(str, fields(bf['l'], bf['u'], A, B) + [0]))
    out.append(f"""/-- node `{nd['path'] or 'root'}` ({nd['node']}) -/
theorem t1_{i} : U (T1 0 FP) ⟨{st}⟩ = {pack(fields(l2, u2, A2, B2))} := by decide +kernel""")
for i, nd in enumerate(G.get('reclip_nodes', [])):
    bf = nd['before']; af = nd['after']; cons = bf['cons']
    A = [cons[f"{i_},{j_}"][0] if f"{i_},{j_}" in cons and cons[f"{i_},{j_}"][0] is not None else 0 for (i_, j_) in SUMS]
    B = [cons[f"{i_},{j_}"][1] if f"{i_},{j_}" in cons and cons[f"{i_},{j_}"][1] is not None else BIG for (i_, j_) in SUMS]
    I = af['intervals']
    A2 = [I[f"{i_},{j_}"][0] for (i_, j_) in SUMS]; B2 = [I[f"{i_},{j_}"][1] for (i_, j_) in SUMS]
    l2 = [I[f"{r},{r + 1}"][0] for r in range(Q)]; u2 = [I[f"{r},{r + 1}"][1] for r in range(Q)]
    assert l2 == af['l'] and u2 == af['u']
    st = ", ".join(map(str, fields(bf['l'], bf['u'], A, B) + [0]))
    out.append(f"""/-- re-clip node `{nd['path']}`: step 5 binds on {", ".join(nd['reclipped'])} -/
theorem rc_{i} : U (T1 0 FP) ⟨{st}⟩ = {pack(fields(l2, u2, A2, B2))} := by decide +kernel""")
for i, z in enumerate(G['z_checks']):
    lbs = [0] * z['n']
    for pc in z['pieces']: lbs[pc['piece']] = pc['lb']
    c = z['M'] if z['right'] else z['P']
    out.append(f"""/-- Z check {i}: {z.get('note', '')}; verdict {z['ok']} -/
theorem z_{i} : zsideL {z['v']} {c} {z['p']} {z['a']} {z['b']} {z['n']} {'true' if z['right'] else 'false'} [{", ".join(map(str, lbs))}] = {'true' if z['ok'] else 'false'} := by
  decide +kernel""")
out.append("end AMW.Cert.PCellTZG\n")
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ROOT, "AMW", "PCellTZG.lean"), "w").write("\n\n".join(out))
print(len(G['t1_nodes']), "T1 nodes,", len(G['z_checks']), "Z checks")
