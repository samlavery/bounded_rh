/-
Per-declaration kernel cost of a compiled module: read its olean, import its imports, and send each constant of the
module through `Lean.Environment.replay` on its own (dependencies first, an inductive together with its constructors
and recursors), timing every call.  Writes `name <TAB> microseconds` per constant.  Same kernel and API as
ReplayHarness; the sum is the module replay cost up to per-call overhead.

usage: lean --run ReplayTimes.lean <olean-path> <out.tsv>
-/
import Lean
open Lean

/-- the replay unit a constant belongs to: an inductive's constructors and recursors replay with it -/
def unitOf (c : ConstantInfo) : Name :=
  match c with
  | .inductInfo v => v.all.headD c.name
  | .ctorInfo v => v.induct
  | .recInfo v => v.all.headD c.name
  | _ => c.name

/-- `done` tracks the replayed units: the environment `replay` returns (`ofKernelEnv`) does not answer `contains`
for them -/
partial def visit (mp : Std.HashMap Name ConstantInfo) (grp : Std.HashMap Name (Array ConstantInfo))
    (h : IO.FS.Handle) (done : IO.Ref NameSet) (env : Environment) (n : Name) : IO Environment := do
  let some c := mp[n]? | return env
  let u := unitOf c
  if u != n then return ← visit mp grp h done env u
  if (← done.get).contains n then return env
  let members := (grp[u]?).getD #[c]
  let names : NameSet := members.foldl (fun s m => s.insert m.name) {}
  let mut env := env
  for m in members do
    for d in m.getUsedConstantsAsSet do
      if !names.contains d && mp.contains d then
        env ← visit mp grp h done env d
  if (← done.get).contains n then return env
  let mut one : Std.HashMap Name ConstantInfo := {}
  for m in members do
    one := one.insert m.name m
  let t0 ← IO.monoNanosNow
  let env' ← env.replay one
  let t1 ← IO.monoNanosNow
  done.modify (·.insert n)
  h.putStrLn s!"{n}\t{(t1 - t0) / 1000}\t{members.size}"
  return env'

def main (args : List String) : IO Unit := do
  let some (oleanArg : String) := args[0]? | throw <| IO.userError "usage: ReplayTimes <olean-path> <out.tsv>"
  let out := args[1]?.getD "replay_times.tsv"
  initSearchPath (← findSysroot)
  let (mod, _region) ← readModuleData ⟨oleanArg⟩
  IO.println s!"module constants: {mod.constants.size}; imports: {mod.imports.size}"
  let mut env ← importModules mod.imports {} 0
  let mut mp : Std.HashMap Name ConstantInfo := {}
  let mut grp : Std.HashMap Name (Array ConstantInfo) := {}
  for c in mod.constants do
    mp := mp.insert c.name c
    let u := unitOf c
    grp := grp.insert u (((grp[u]?).getD #[]).push c)
  let h ← IO.FS.Handle.mk out .write
  let done ← IO.mkRef ({} : NameSet)
  let t0 ← IO.monoMsNow
  for c in mod.constants do
    env ← visit mp grp h done env c.name
  let t1 ← IO.monoMsNow
  h.flush
  IO.println s!"per-declaration replay of {mod.constants.size} constants: {t1 - t0} ms"
