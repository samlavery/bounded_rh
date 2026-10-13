import CandPC8CLcT
open Lean Meta Elab Command

/-- dependency closure (types and values) from the roots, restricted to constants of module `mod` -/
def closureIn (env : Environment) (modIdx : Nat) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots.toList
  let mut fuel := 10000000
  while fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for c in ci.getUsedConstantsAsSet.toList do
          if !seen.contains c then
            if env.getModuleIdxFor? c == some modIdx then stack := c :: stack
        -- inductive types: keep their constructors and recursors with them
        if let .inductInfo iv := ci then
          for c in iv.ctors do stack := c :: stack
  return seen

elab "#depaudit" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `CandPC8CLcT | throwError "no module"
  let roots := #[`candidate_strict_improvement, `candidate_critical_line_bound, `candidate_critical_line_bound_cumulative]
  let live := closureIn env modIdx.toNat roots
  let mut out : String := ""
  let mut nAll : Nat := 0; let mut nLive : Nat := 0
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some modIdx then
      nAll := nAll + 1
      let isLive := live.contains n
      if isLive then nLive := nLive + 1
      let r ← liftTermElabM (findDeclarationRanges? n)
      match r with
      | some rr => out := out ++ s!"{if isLive then 1 else 0}\t{rr.range.pos.line}\t{rr.range.endPos.line}\t{n}\n"
      | none => pure ()
  IO.FS.writeFile "deps_PC8CLc.tsv" out
  logInfo m!"constants in module: {nAll}, live: {nLive}"

#depaudit
