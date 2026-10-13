/-
Constant-by-constant comparison of two compiled modules, modulo an atom rename map.

usage: lean --run bench/OleanDiff.lean ORIG.olean NEW.olean MAP
MAP: one `old new` atom pair per line (lean_minify.py --map, plus the module-name pair, which renames the
`_private.<module>` prefix).

For every constant of ORIG, the constant named by the mapped name must exist in NEW with the same kind,
universe parameters, header fields, type and value, where every constant name inside ORIG's expressions is
mapped first.  "identical" means `Expr.equal` (binder names included); "alpha-only" means equal up to binder
names and binder info (`Expr.eqv`).  Constants only in NEW are listed (expected: the parser / macro /
unexpander definitions that `local notation` and `local macro` create).  Exit code 0 iff no constant is
missing or different.
-/
import Lean
open Lean

def loadMap (path : System.FilePath) : IO (Std.HashMap String String) := do
  let mut m : Std.HashMap String String := {}
  for line in (← IO.FS.lines path) do
    match (line.splitOn " ").filter (· ≠ "") with
    | [a, b] => m := m.insert a b
    | _ => pure ()
  return m

def rnName (m : Std.HashMap String String) : Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (rnName m p) (m.getD s s)
  | .num p k => .num (rnName m p) k

partial def rnExpr (f : Name → Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => some (.const (f n) us)
    | .proj s i b => some (.proj (f s) i (rnExpr f b))
    | _ => none

/-- binder names with their macro scopes erased (hygienic names carry the module name and a counter) -/
partial def normBinders (e : Expr) : Expr :=
  e.replace fun
    | .lam n t b bi => some (.lam n.eraseMacroScopes (normBinders t) (normBinders b) bi)
    | .forallE n t b bi => some (.forallE n.eraseMacroScopes (normBinders t) (normBinders b) bi)
    | .letE n t v b nd => some (.letE n.eraseMacroScopes (normBinders t) (normBinders v) (normBinders b) nd)
    | _ => none

/-- the first pair of binder names at which two alpha-equivalent expressions differ -/
partial def firstBinderDiff : Expr → Expr → Option (Name × Name)
  | .lam n t b _, .lam m s c _ | .forallE n t b _, .forallE m s c _ =>
    if n != m then some (n, m) else (firstBinderDiff t s).orElse fun _ => firstBinderDiff b c
  | .letE n t v b _, .letE m s w c _ =>
    if n != m then some (n, m) else
      ((firstBinderDiff t s).orElse fun _ => firstBinderDiff v w).orElse fun _ => firstBinderDiff b c
  | .app f a, .app g b => (firstBinderDiff f g).orElse fun _ => firstBinderDiff a b
  | .mdata _ a, .mdata _ b => firstBinderDiff a b
  | .proj _ _ a, .proj _ _ b => firstBinderDiff a b
  | _, _ => none

/-- `same`: `Expr.equal` after renaming; `hyg`: equal once binder names lose their macro scopes;
`alpha`: equal only up to binder names / binder info (`Expr.eqv`); `diff`: not even that. -/
inductive Verdict where
  | same
  | hyg
  | alpha (why : String)
  | diff (why : String)

def cmpE (f : Name → Name) (what : String) (a b : Expr) : Verdict :=
  let a' := rnExpr f a
  if a'.equal b then .same
  else if (normBinders a').equal (normBinders b) then .hyg
  else if a' == b then
    .alpha s!"{what}: binder {(firstBinderDiff a' b).map fun (x, y) => s!"{x} vs {y}"}"
  else .diff what

def rank : Verdict → Nat
  | .same => 0 | .hyg => 1 | .alpha _ => 2 | .diff _ => 3

def combine (vs : List Verdict) : Verdict :=
  vs.foldl (fun acc v => if rank v > rank acc then v else acc) .same

def flag (b : Bool) (w : String) : Verdict := if b then .same else .diff w

def hintsEq : ReducibilityHints → ReducibilityHints → Bool
  | .opaque, .opaque => true
  | .abbrev, .abbrev => true
  | .regular a, .regular b => a == b
  | _, _ => false

def safetyEq : DefinitionSafety → DefinitionSafety → Bool
  | .unsafe, .unsafe => true
  | .safe, .safe => true
  | .partial, .partial => true
  | _, _ => false

def cmpConst (f : Name → Name) (a b : ConstantInfo) : Verdict :=
  let base := [flag (a.levelParams == b.levelParams) "levelParams", cmpE f "type" a.type b.type]
  let rest : List Verdict := match a, b with
    | .defnInfo x, .defnInfo y =>
      [cmpE f "value" x.value y.value, flag (hintsEq x.hints y.hints) "hints",
       flag (safetyEq x.safety y.safety) "safety", flag (x.all.map f == y.all) "all"]
    | .thmInfo x, .thmInfo y => [cmpE f "value" x.value y.value, flag (x.all.map f == y.all) "all"]
    | .opaqueInfo x, .opaqueInfo y =>
      [cmpE f "value" x.value y.value, flag (x.isUnsafe == y.isUnsafe) "unsafe"]
    | .axiomInfo x, .axiomInfo y => [flag (x.isUnsafe == y.isUnsafe) "unsafe"]
    | .quotInfo _, .quotInfo _ => []
    | .inductInfo x, .inductInfo y =>
      [flag (x.numParams == y.numParams && x.numIndices == y.numIndices && x.all.map f == y.all &&
        x.ctors.map f == y.ctors && x.numNested == y.numNested && x.isRec == y.isRec &&
        x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive) "inductive header"]
    | .ctorInfo x, .ctorInfo y =>
      [flag (f x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
        x.numFields == y.numFields && x.isUnsafe == y.isUnsafe) "constructor header"]
    | .recInfo x, .recInfo y =>
      flag (x.all.map f == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
        x.numMotives == y.numMotives && x.numMinors == y.numMinors && x.k == y.k &&
        x.isUnsafe == y.isUnsafe && x.rules.length == y.rules.length) "recursor header" ::
      (x.rules.zip y.rules).map fun (r, s) =>
        if f r.ctor == s.ctor && r.nfields == s.nfields then cmpE f "rule" r.rhs s.rhs
        else .diff "rule header"
    | _, _ => [.diff "kind"]
  combine (base ++ rest)

/-- parser descriptors, macro rules and unexpanders made by `notation` / `macro` / `syntax`: their names and
string payloads embed the module name and namespace as flat strings, they are not referenced by any
theorem, and they are matched by count, not by name. -/
def syntaxTypes : List Name :=
  [``Lean.ParserDescr, ``Lean.TrailingParserDescr, ``Lean.Macro, ``Lean.PrettyPrinter.Unexpander]

def isSyntax (c : ConstantInfo) : Bool :=
  match c.type.getAppFn.constName? with
  | some k => syntaxTypes.contains k
  | none => false

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"

def main (args : List String) : IO UInt32 := do
  let [o, n, mp] := args | throw <| IO.userError "usage: OleanDiff ORIG.olean NEW.olean MAP"
  let m ← loadMap mp
  let f := rnName m
  let (mo, _) ← readModuleData o
  let (mn, _) ← readModuleData n
  let mut newMap : Std.HashMap Name ConstantInfo := {}
  for c in mn.constants do
    newMap := newMap.insert c.name c
  let mut seen : Std.HashSet Name := {}
  let mut nSame := 0
  let mut nHyg := 0
  let mut nAlpha := 0
  let mut nDiff := 0
  let mut nMiss := 0
  let mut nSynO := 0
  let mut hygShown := 0
  for c in mo.constants do
    if isSyntax c then
      nSynO := nSynO + 1
      continue
    let nm := f c.name
    match newMap[nm]? with
    | none =>
      nMiss := nMiss + 1
      IO.println s!"MISSING {c.name} (as {nm})"
    | some d =>
      seen := seen.insert nm
      match cmpConst f c d with
      | .same => nSame := nSame + 1
      | .hyg =>
        nHyg := nHyg + 1
        if hygShown < 3 then
          hygShown := hygShown + 1
          let a' := rnExpr f c.type
          let w := (firstBinderDiff a' d.type).orElse fun _ =>
            match c.value?, d.value? with
            | some x, some y => firstBinderDiff (rnExpr f x) y
            | _, _ => none
          IO.println s!"HYGIENE-ONLY (example) {c.name}: {w.map fun (x, y) => s!"{x} vs {y}"}"
      | .alpha w =>
        nAlpha := nAlpha + 1
        IO.println s!"ALPHA-ONLY {c.name}: {w}"
      | .diff w =>
        nDiff := nDiff + 1
        IO.println s!"DIFF {c.name}: {w}"
  let mut nSynN := 0
  let mut nExtra := 0
  for c in mn.constants do
    if isSyntax c then
      nSynN := nSynN + 1
    else unless seen.contains c.name do
      nExtra := nExtra + 1
      IO.println s!"EXTRA (non-syntax) {c.name} : {kindName c}"
  for s in ["candidate_strict_improvement", "candidate_critical_line_bound",
            "candidate_critical_line_bound_cumulative"] do
    let nm := s.toName
    match mo.constants.find? (·.name == nm), newMap[nm]? with
    | some a, some b =>
      -- `ConstantInfo.value?` does not return theorem values in this Lean version: read them directly
      let vEq := match a, b with
        | .thmInfo x, .thmInfo y => toString ((rnExpr f x.value).equal y.value)
        | .defnInfo x, .defnInfo y => toString ((rnExpr f x.value).equal y.value)
        | _, _ => "no value"
      IO.println s!"SCORED {s}: {kindName a}/{kindName b}; type Expr.equal (no renaming applied) = {a.type.equal b.type}; value Expr.equal modulo renaming = {vEq}"
    | _, _ => IO.println s!"SCORED {s}: NOT FOUND"
  IO.println s!"syntax machinery (parser / macro / unexpander definitions): orig {nSynO}, new {nSynN}"
  IO.println s!"orig constants {mo.constants.size}, new constants {mn.constants.size}: identical {nSame}, identical up to hygienic binder-name suffixes {nHyg}, alpha-only {nAlpha}, different {nDiff}, missing {nMiss}, extra non-syntax {nExtra}"
  return if nDiff + nMiss + nExtra + nAlpha == 0 then 0 else 1
