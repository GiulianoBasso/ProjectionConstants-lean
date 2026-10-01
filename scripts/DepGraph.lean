/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants

/-!
# Export the declaration dependency graph of the library

Run with `lake env lean --run scripts/DepGraph.lean <output.json>` (or `scripts/diagram/build.sh`,
which also draws `diagram/dependency-tree.html`).

Nodes are the source-level declarations of the modules `ProjectionConstants.*`; auxiliary
constants (`proof_i`, `match_i`, equation lemmas, projections, recursors, …) are merged into
their parent declaration. There is an edge `a → b` if `b` occurs in the type or the value of `a`
(or of one of its auxiliary constants).
-/

open Lean Meta

/-- The module of a constant, if it belongs to the library. -/
def libModule? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let mod := env.header.moduleNames[idx.toNat]!
  if (`ProjectionConstants).isPrefixOf mod then some mod else none

/-- Is this a source-level declaration (a node of the graph)? -/
def isNode (env : Environment) (n : Name) : Bool :=
  let n' := (privateToUserName? n).getD n
  !n'.isInternalDetail && !isAuxRecursor env n && !isNoConfusion env n &&
    !(env.isProjectionFn n) && !(Lean.Meta.isMatcherCore env n) &&
    (match env.find? n with
      | some (.ctorInfo _) => false
      | some (.recInfo _) => false
      | _ => true) &&
    !(n'.components.any fun c ↦
      c == `injEq || c == `inj || c == `sizeOf_spec || c == `ctorIdx || c == `ext_iff ||
      c == `eq_def || c == `induct || c == `splitter || c == `noConfusionType ||
      c == `congr_simp || c.isInternalDetail)

/-- The parent node of an auxiliary constant. -/
partial def parentNode (env : Environment) (n : Name) : Option Name :=
  if isNode env n then some n
  else match n with
    | .str p _ => parentNode env p
    | .num p _ => parentNode env p
    | .anonymous => none

/-- Library constants used in a declaration. -/
def usedConsts (env : Environment) (n : Name) : Array Name := Id.run do
  let some ci := env.find? n | return #[]
  let mut s : NameSet := {}
  for c in ci.type.getUsedConstants do s := s.insert c
  if let some v := ci.value? (allowOpaque := true) then
    for c in v.getUsedConstants do s := s.insert c
  if let .inductInfo ii := ci then
    for ctor in ii.ctors do
      if let some cci := env.find? ctor then
        for c in cci.type.getUsedConstants do s := s.insert c
  return s.toArray.filter fun c ↦ (libModule? env c).isSome

/-- Node-level dependencies, expanding auxiliary constants. -/
partial def nodeDeps (env : Environment) (n : Name) (visited : NameSet := {}) :
    NameSet × NameSet := Id.run do
  let mut out : NameSet := {}
  let mut vis := visited.insert n
  for c in usedConsts env n do
    if vis.contains c then continue
    if isNode env c then
      out := out.insert c
    else
      -- structure projections, constructors, recursors: point to the type
      let target :=
        if let some info := env.getProjectionFnInfo? c then
          match env.find? info.ctorName with
          | some (.ctorInfo ci) => some ci.induct
          | _ => none
        else match env.find? c with
          | some (.ctorInfo ci) => some ci.induct
          | some (.recInfo ri) => some ri.getMajorInduct
          | _ => none
      match target with
      | some t => if isNode env t then out := out.insert t
      | none => pure ()
      -- auxiliary constants of the same declaration: expand
      let (o, v) := nodeDeps env c vis
      vis := v
      for d in o do out := out.insert d
  return (out, vis)

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .inductInfo _ => "structure"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | _ => "other"

def jsonStr (s : String) : String := (Json.str s).compress

unsafe def main (args : List String) : IO Unit := do
  let out := args.headD "depgraph.json"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `ProjectionConstants }] {} (loadExts := true)
  let mut nodes : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (libModule? env n).isSome && isNode env n then
      nodes := nodes.push n
  IO.println s!"nodes: {nodes.size}"
  let nodeSet : NameSet := nodes.foldl (·.insert ·) {}
  let mut lines : Array String := #[]
  let mut nEdges := 0
  for n in nodes do
    let some ci := env.find? n | continue
    let mod := (libModule? env n).getD .anonymous
    let (deps, _) := nodeDeps env n
    let deps := deps.toArray.filter fun d ↦ d != n && nodeSet.contains d
    nEdges := nEdges + deps.size
    let doc := (← findDocString? env n).getD ""
    let isInst := (Lean.Meta.instanceExtension.getState env).instanceNames.contains n
    let kind := if isInst then "instance" else kindOf ci
    let userName := (privateToUserName? n).getD n
    let ranges := declRangeExt.find? (level := .exported) env n <|>
      declRangeExt.find? (level := .server) env n
    let line := match ranges with
      | some r => r.range.pos.line
      | none => 0
    let depsJson := "[" ++ ",".intercalate (deps.toList.map fun d ↦
      jsonStr ((privateToUserName? d).getD d).toString) ++ "]"
    lines := lines.push ("{\"name\":" ++ jsonStr userName.toString ++
      ",\"module\":" ++ jsonStr mod.toString ++ ",\"kind\":" ++ jsonStr kind ++
      ",\"line\":" ++ toString line ++ ",\"doc\":" ++ jsonStr doc ++
      ",\"deps\":" ++ depsJson ++ "}")
  IO.println s!"edges: {nEdges}"
  IO.FS.writeFile out ("[\n" ++ ",\n".intercalate lines.toList ++ "\n]\n")
