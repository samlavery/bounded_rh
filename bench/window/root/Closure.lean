import AMW.BrC
open Lean Meta Elab Command

def brMods : List Name := [`AMW.BrA, `AMW.BrB, `AMW.BrC]

elab "#bridge_closure" : command => do
  let env ← getEnv
  let inBr (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some idx => brMods.contains (env.header.moduleNames[idx.toNat]!)
    | none => false
  let roots : List Name := [`Zeta23Ext.BridgeW.n_point_bound_w', `Zeta23Ext.BridgeW.Fw,
    `Zeta23Ext.BridgeW.Phi_w', `Zeta23Ext.BridgeW.WCert.Adm, `Zeta23Ext.Bridge.ptsN,
    `Zeta23Ext.Bridge.wfun, `Zeta23Ext.BridgeW.WCert.B, `Zeta23Ext.BridgeW.WCert.spanMass,
    `Zeta23Ext.BridgeW.WCert, `Zeta23Ext.BridgeW.WCert.mk, `Zeta23Ext.BridgeW.WCert.a,
    `Zeta23Ext.BridgeW.WCert.b, `Zeta23Ext.BridgeW.WCert.Adm.mk]
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let used := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants | none => #[])
      -- structures / inductives: constructors and projections
      let extra : Array Name := match ci with
        | .inductInfo ii => ii.ctors.toArray
        | _ => #[]
      for u in used ++ extra do
        if inBr u && !seen.contains u then stack := u :: stack
  -- report unreachable declarations with ranges
  let mut out : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if inBr n && !seen.contains n && !n.isInternal then
      let mod := env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!
      match ← findDeclarationRanges? n with
      | some r => out := out.push s!"{mod} {r.range.pos.line} {r.range.endPos.line} {n}"
      | none => out := out.push s!"{mod} ? ? {n}"
  -- also count reachable
  logInfo m!"reachable {seen.size}; unreachable {out.size}\n{String.intercalate "\n" out.toList}"

#bridge_closure
