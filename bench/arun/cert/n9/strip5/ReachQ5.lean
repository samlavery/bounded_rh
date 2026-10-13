import CandINT9Q5
open Lean

/-- every constant reachable from `roots` through types and values (theorem proofs included) -/
partial def reach (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      let mut es : List Expr := [ci.type]
      match ci with
      | .defnInfo v => es := v.value :: es
      | .thmInfo v => es := v.value :: es
      | .opaqueInfo v => es := v.value :: es
      | .inductInfo v => todo := v.ctors ++ todo
      | .ctorInfo v => todo := v.induct :: todo
      | .recInfo v => todo := v.all ++ todo
      | _ => pure ()
      for e in es do todo := e.getUsedConstants.toList ++ todo
    | none => pure ()
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `CandINT9Q5 | throwError "no module"
  let roots := [`candidate_strict_improvement, `candidate_critical_line_bound, `candidate_critical_line_bound_cumulative]
  let r := reach env roots
  let h ← IO.FS.Handle.mk "/Users/samuellavery/work/riemann-submission/bench/arun/cert/n9/strip5/unreachQ5.tsv" .write
  let mut nU := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && r.contains n then
      match (← findDeclarationRanges? n) with
      | some d => h.putStrLn s!"{n}\t{d.range.pos.line}\t{d.range.endPos.line}\tREACH"
      | none => pure ()
    if env.getModuleIdxFor? n == some idx && !r.contains n && (!n.isInternal || isPrivateName n) then
      let rng ← findDeclarationRanges? n
      match rng with
      | some d => h.putStrLn s!"{n}\t{d.range.pos.line}\t{d.range.endPos.line}\t{if ci.isThm then "thm" else "def"}"
      | none => h.putStrLn s!"{n}\t0\t0\tnorange"
      nU := nU + 1
  IO.println s!"reachable {r.size}; unreachable module decls {nU}"
