-- scratch test for lean_minify.py: tokens of `local notation` / `local macro` are scoped to the namespace
namespace Foo
set_option hygiene false in
local notation:max "Q" a:max => (a + 1 : Nat)
set_option hygiene false in
local macro "W " x:ident : command => `(command| def $x : Nat := Q 1)
W foo
example : foo = 2 := rfl
end Foo
def g (Q : Nat) (W : Nat) : Nat := Q + W
example : g 1 2 = 3 := rfl
theorem Wt (W : Nat) : W = W := rfl
