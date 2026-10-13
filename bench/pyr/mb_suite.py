"""Kernel micro-benchmark suite: one theorem per file (no order effects), N distinct instances each.
Writes mb/T*.lean; run with mb_run.sh."""
import random, sys
random.seed(7); sys.set_int_max_str_digits(0)
N = 2000
def sumexpr(terms):
    if len(terms) == 1: return terms[0]
    h = len(terms) // 2
    return f"(Nat.add {sumexpr(terms[:h])} {sumexpr(terms[h:])})"
HDR = "universe uF\nset_option maxRecDepth 100000\nset_option profiler.threshold 0\n"
COMMON = """
def forceN {α : Sort uF} (a : Nat) (k : Nat → α) : α := Nat.casesOn (motive := fun _ => α) a (k 0) (fun n => k (Nat.succ n))
def fld (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 32 i)) 4294967295
"""
tests = {}
def T(name, defs, term):
    terms = [term(i) for i in range(N)]
    tests[name] = HDR + COMMON + defs + f"\nset_option profiler true in\ntheorem t : Nat.ble 0 {sumexpr(terms)} = true := by decide +kernel\n"
T("T0_base", "", lambda i: f"(Nat.add {random.getrandbits(30)} {i})")
# dispatch trees over 256 constants (each 64 bytes)
consts = "\n".join(f"def K_{j} : Nat := {random.getrandbits(512)}" for j in range(256))
def tree(kind):
    L = []
    def nm(a, b): return f"K_{a}" if b - a == 1 else f"S{a}_{b}"
    def call(a, b): return f"K_{a}" if b - a == 1 else f"(S{a}_{b} j)"
    def mk(a, b):
        if b - a == 1: return
        m = (a + b) // 2; mk(a, m); mk(m, b)
        if kind == "bif": L.append(f"def S{a}_{b} (j : Nat) : Nat := bif Nat.blt j {m} then {call(a, m)} else {call(m, b)}")
        if kind == "bifle": L.append(f"def S{a}_{b} (j : Nat) : Nat := bif Nat.ble {m} j then {call(m, b)} else {call(a, m)}")
        if kind == "rec": L.append(f"def S{a}_{b} (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) {call(a, m)} {call(m, b)} (Nat.ble {m} j)")
        if kind == "casesOn": L.append(f"def S{a}_{b} (j : Nat) : Nat := Bool.casesOn (motive := fun _ => Nat) (Nat.ble {m} j) {call(a, m)} {call(m, b)}")
    mk(0, 256)
    return consts + "\n" + "\n".join(L)
for kind in ("bif", "bifle", "rec", "casesOn"):
    T(f"T1_disp_{kind}", tree(kind), lambda i: f"(Nat.add (Nat.land (S0_256 {random.randrange(256)}) {random.getrandbits(20)}) {i})")
T("T1_nodisp", consts, lambda i: f"(Nat.add (Nat.land K_{random.randrange(256)} {random.getrandbits(20)}) {i})")
# def-unfold chain (no conditionals), depth 8
chain = "\n".join([f"def F8 (x : Nat) : Nat := Nat.add x 1"] + [f"def F{k} (x : Nat) : Nat := F{k+1} x" for k in range(7, -1, -1)])
T("T2_chain8", chain, lambda i: f"(Nat.add (F0 {random.getrandbits(30)}) {i})")
T("T2_chain0", chain, lambda i: f"(Nat.add (F8 {random.getrandbits(30)}) {i})")
# forceN chain of 8
T("T3_force8", "def G (x : Nat) : Nat := forceN (Nat.add x 1) fun a => forceN (Nat.add a 1) fun b => forceN (Nat.add b 1) fun c => forceN (Nat.add c 1) fun d => forceN (Nat.add d 1) fun e => forceN (Nat.add e 1) fun f => forceN (Nat.add f 1) fun g => forceN (Nat.add g 1) fun h => h",
  lambda i: f"(Nat.add (G {random.getrandbits(30)}) {i})")
T("T3_noforce8", "def G (x : Nat) : Nat := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add x 1) 1) 1) 1) 1) 1) 1) 1",
  lambda i: f"(Nat.add (G {random.getrandbits(30)}) {i})")
T("T3_letfun8", "def G (x : Nat) : Nat := (fun a => (fun b => (fun c => (fun d => (fun e => (fun f => (fun g => (fun h => h) (Nat.add g 1)) (Nat.add f 1)) (Nat.add e 1)) (Nat.add d 1)) (Nat.add c 1)) (Nat.add b 1)) (Nat.add a 1)) (Nat.add x 1)",
  lambda i: f"(Nat.add (G {random.getrandbits(30)}) {i})")
# field reads
for kb in (1, 8, 64):
    T(f"T4_fld{kb}k", f"def C : Nat := {random.getrandbits(kb * 8192)}", lambda i: f"(Nat.add (fld C {random.randrange(kb * 256 - 1)}) {i})")
# structure projections
T("T5_proj", "structure B where (a b c d e f g h i j : Nat)\ndef mkB (x : Nat) : B := B.mk x 1 2 3 4 5 6 7 8 9",
  lambda i: f"(Nat.add (B.f (mkB {random.getrandbits(30)})) (B.a (mkB {random.getrandbits(30)})))")
# notation vs explicit
T("T6_notation", "def H (x y : Nat) : Nat := x * 3 + y * 5 + x * y", lambda i: f"(Nat.add (H {random.getrandbits(30)} {random.getrandbits(30)}) {i})")
T("T6_explicit", "def H (x y : Nat) : Nat := Nat.add (Nat.add (Nat.mul x 3) (Nat.mul y 5)) (Nat.mul x y)", lambda i: f"(Nat.add (H {random.getrandbits(30)} {random.getrandbits(30)}) {i})")
for name, src in tests.items():
    open(f"mb/{name}.lean", "w").write(src)
print(" ".join(tests))
