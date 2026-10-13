-- scratch test for lean_minify.py mechanics: macro / notation expansions must elaborate to the same terms
import Lean
open Lean Elab Command

set_option Elab.async false

namespace Foo.Bar
structure Box where
  (a : Nat) (b : Nat)
  deriving DecidableEq
def Box.setHi (x : Box) (k : Nat) (v : Nat) : Box := ⟨x.a + k, v⟩
def Box.mid (x : Box) (k : Nat) : Nat := x.b + k
def axOf (bits k : Nat) : Nat := bits + k
def walk (t bits f k : Nat) (b : Box) : Option Nat := some (t + bits + f + k + b.a)
theorem walkF_eq (t bits f k : Nat) (b : Box) : walk t bits f k b = walk t bits f k b := rfl
end Foo.Bar

namespace Foo.Bar.Data
open Foo.Bar
inductive CTN | nil | node (l : CTN) (c : Box) (r : CTN)
local notation "N" => CTN.node
local notation "E" => CTN.nil
set_option hygiene false in
local notation:max "L" a:max b:max => CTN.node CTN.nil ⟨a, b⟩ CTN.nil
set_option hygiene false in
local notation:max "M" l:max a:max b:max r:max => CTN.node l ⟨a, b⟩ r

def t1 : CTN := (N (N E ⟨1,2⟩ E) ⟨3,4⟩ (N E ⟨5,6⟩ (N E ⟨7,8⟩ E)))
def t2 : CTN := M L 1 2 3 4 M E 5 6 L 7 8

def table : Nat := 16
def bits : Nat := 0x10
def bitsD : Nat := 16
def big1 : Nat := 123456789012345678901234567890
def big2 : Nat := 0x18ee90ff6c373e0ee4e3f0ad2

def bx0 : Box := ⟨1, 2⟩
theorem wk0 : Bar.walk table bits 3 4 bx0 = some 40 :=
  (Bar.walkF_eq table bits 3 4 bx0).symm.trans (by decide +kernel)
noncomputable def bx1 : Box := (bx0).setHi (Bar.axOf bits 2) (Bar.Box.mid bx0 (Bar.axOf bits 2))
theorem rt0 : Bar.walk table bits 3 4 (Box.mk 1 2) = some 40 := by
  rw [show Box.mk 1 2 = bx0 from by decide +kernel]; exact wk0

set_option hygiene false in
local macro "F " x0:ident x1:num x2:num x3:ident x4:num : command => `(command|
theorem $x0 : Bar.walk table bits $x1 $x2 $x3 = some $x4 :=
  (Bar.walkF_eq table bits $x1 $x2 $x3).symm.trans (by decide +kernel))
set_option hygiene false in
local macro "H " x0:ident x1:ident x2:num : command => `(command|
noncomputable def $x0 : Box := ($x1).setHi (Bar.axOf bits $x2) (Bar.Box.mid $x1 (Bar.axOf bits $x2)))
set_option hygiene false in
local macro "R " x0:ident x1:num x2:num x3:ident : command => `(command|
theorem $x0 : Bar.walk table bits 3 4 (Box.mk $x1 $x2) = some 40 := by
  rw [show Box.mk $x1 $x2 = bx0 from by decide +kernel]; exact $x3)

F wk0' 3 4 bx0 40
H bx1' bx0 2
R rt0' 1 2 wk0

def same (a b : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ca := env.find? a | throwError "missing {a}"
  let some cb := env.find? b | throwError "missing {b}"
  let tv := ca.type == cb.type && ca.type.equal cb.type
  let vv := match ca.value?, cb.value? with
    | some x, some y => x == y && x.equal y
    | none, none => true
    | _, _ => false
  logInfo m!"{a} vs {b}: type {tv} value {vv}"

run_cmd same ``t1 ``t2
run_cmd same ``bits ``bitsD
run_cmd same ``big1 ``big2
run_cmd same ``wk0 ``wk0'
run_cmd same ``bx1 ``bx1'
run_cmd same ``rt0 ``rt0'
#print axioms wk0'
#print axioms rt0'
end Foo.Bar.Data
