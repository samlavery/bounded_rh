"""Micro-benchmarks of kernel costs (core Lean, decide +kernel, profiler 'type checking took').
mb_fld.lean: N reads `fld C i` from packed constants of 1, 10, 100 KB; dispatch trees of depth 4 and 8 to 1 KB leaves.
mb_term.lean: the forced termWN (BenchCDefs) on N distinct real queries from the bench sample."""
import random, os, sys, re
random.seed(1); sys.set_int_max_str_digits(0)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
EB = 40; M = (1 << EB) - 1
def lit(nbytes): return random.getrandbits(nbytes * 8) | (1 << (nbytes * 8 - 1))
def sumexpr(terms):
    # balanced Nat.add tree
    if len(terms) == 1: return terms[0]
    h = len(terms) // 2
    return f"(Nat.add {sumexpr(terms[:h])} {sumexpr(terms[h:])})"
L = ["set_option maxRecDepth 100000", "set_option profiler true", "set_option profiler.threshold 1", "",
     f"def fld (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul {EB} i)) {M}", ""]
for kb in (1, 10, 100):
    L.append(f"def C{kb} : Nat := {lit(kb * 1024)}")
# dispatch trees: 2^d leaves of 1 KB
for d in (4, 8):
    for i in range(1 << d): L.append(f"def D{d}_{i} : Nat := {lit(1024)}")
    def tree(lo, hi):
        if hi - lo == 1: return None
        m = (lo + hi) // 2
        nm = f"D{d}s{lo}_{hi}"
        a = f"D{d}_{lo}" if m - lo == 1 else f"D{d}s{lo}_{m}"
        b = f"D{d}_{m}" if hi - m == 1 else f"D{d}s{m}_{hi}"
        tree(lo, m); tree(m, hi)
        L.append(f"def {nm} (j : Nat) : Nat := bif Nat.blt j {m} then {a if m - lo > 1 else a} {'j' if m - lo > 1 else ''} else {b} {'j' if hi - m > 1 else ''}".replace("  ", " "))
    tree(0, 1 << d)
L.append("")
nf = 1024 * 8 // EB - 2
for kb in (1, 10, 100):
    nf = kb * 1024 * 8 // EB - 2
    idx = random.sample(range(nf), min(N, nf)) if nf >= N else [random.randrange(nf) for _ in range(N)]
    # distinct reads: (i) pairs must be distinct; for 1 KB only ~200 fields, so vary an added offset to keep terms distinct
    terms = [f"(fld C{kb} {i})" for i in idx] if kb > 1 else [f"(Nat.add (fld C1 {random.randrange(200)}) {t})" for t in range(N)]
    L.append(f"theorem t_C{kb} : Nat.ble 0 {sumexpr(terms)} = true := by decide +kernel")
for d in (4, 8):
    terms = [f"(Nat.add (fld (D{d}s0_{1<<d} {random.randrange(1 << d)}) {random.randrange(200)}) {t})" for t in range(N)]
    L.append(f"theorem t_D{d} : Nat.ble 0 {sumexpr(terms)} = true := by decide +kernel")
terms = [f"(Nat.add {random.randrange(1<<30)} {t})" for t in range(N)]
L.append(f"theorem t_base : Nat.ble 0 {sumexpr(terms)} = true := by decide +kernel")
open("mb_fld.lean", "w").write("\n".join(L) + "\n")

# ---- termWN on distinct real queries ----
HERE = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE, "..", "count_ops.py")).read().split("# SPANS order check")[0].replace('os.path.dirname(os.path.abspath(__file__))', repr(os.path.join(HERE, ".."))))
QS = set()
_t = termWN
def termWN2(lo, hi): QS.add((lo, hi)); return _t(lo, hi)
termWN = termWN2
for n in "wk0 wk5 wk13 wk14 wk15 wk18 wk21 wk22 wk27 wk46".split():
    m = re.search(rf"theorem {n} : SixW7.walk table bits (\d+) (\d+) (bx\d+) = some (\d+)", sol)
    walk(int(m.group(1)), int(m.group(2)), bx[m.group(3)])
qs = sorted(QS); random.shuffle(qs); qs = qs[:N]
open("queries_sample.txt", "w").write("\n".join(f"{a} {b}" for a, b in qs) + "\n")
T = ["import BenchData", "import BenchCDefs", "set_option maxRecDepth 100000", "set_option profiler true", "set_option profiler.threshold 1",
     "namespace Zeta23Ext.Bridge.ThreePoint.SixW7Data", "open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW7", ""]
T.append(f"theorem t_term : Nat.ble 0 {sumexpr([f'(termWN table {a} {b})' for a, b in qs])} = true := by decide +kernel")
T.append(f"theorem t_term_again : Nat.ble 0 {sumexpr([f'(Nat.add (termWN table {a} {b}) 1)' for a, b in qs])} = true := by decide +kernel")
T.append("end Zeta23Ext.Bridge.ThreePoint.SixW7Data")
open("mb_term.lean", "w").write("\n".join(T) + "\n")
print("wrote mb_fld.lean, mb_term.lean;", len(qs), "queries")
