import Lean
open Lean Elab Command

namespace HironakaNativeMigrationCanonical

def node (tag : String) (xs : List Json := []) : Json :=
  toJson (Json.str tag :: xs)

def nameTree : Name → Json
  | .anonymous => node "anonymous"
  | .str p s => node "str" [nameTree p,toJson s]
  | .num p k => node "num" [nameTree p,toJson k]

-- Only the exact original module in an actual private constant is renamed.
-- Every namespace component, numerical index and auxiliary suffix is retained.
def namespaceRules : List (Name × Name) := [(`TranscendentalNakamaye.FirstPass.NonKahlerLocus, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI2, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI3, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI4, `Hironaka), (`TranscendentalNakamaye.Pending.HironakaAPI, `Hironaka), (`TranscendentalNakamaye.Pending, `Hironaka), (`TranscendentalNakamaye.FirstPass, `Hironaka), (`TranscendentalNakamaye.Upstream, `Hironaka), (`TranscendentalNakamaye, `Hironaka)]

def renameNamespace (n : Name) : Name := Id.run do
  for (a,b) in namespaceRules do
    if a.isPrefixOf n then return n.replacePrefix a b
  return n

def renamePrivate (mods : List (Name × Name)) (n : Name) : Name := Id.run do
  -- Explicit full private-constant pairs are derived from actual moduleData.
  -- Names must match after the documented namespace transformation, preserving
  -- every private numerical index and every auxiliary suffix.
  for (a,b) in mods do
    if (`_private).isPrefixOf a && a == n then return b
  for (a,b) in mods do
    if (`_private ++ a).isPrefixOf n then
      let rest := n.replacePrefix (`_private ++ a) .anonymous
      match rest.components with
      | index :: tail =>
        let ns := tail.foldl (· ++ ·) .anonymous
        return (`_private ++ b) ++ index ++ renameNamespace ns
      | [] => return n
  return renameNamespace n

-- Raw component concatenation avoids Name.append's macro-scope handling
-- on incomplete hygienic prefixes; every name component stays exact.
def appendNameRaw (a : Name) : Name → Name
  | .anonymous => a
  | .str p s => .str (appendNameRaw a p) s
  | .num p k => .num (appendNameRaw a p) k

-- The embedded module after _@ may occur below an arbitrary binder prefix.
-- All spelling, macro scopes, hygiene tags and numeric seeds are retained.
def isHygieneContextTail (n : Name) : Bool :=
  match n.components with
  | .num .anonymous _ :: .str .anonymous "_hygCtx" :: _ => true
  | .str .anonymous "_hyg" :: .num .anonymous _ :: _ => true
  | _ => false

def renameContextAt (mods : List (Name × Name)) (pre n : Name) : Option Name := Id.run do
  for (a,b) in mods do
    let oldPre := appendNameRaw pre a
    if a != b && oldPre.isPrefixOf n &&
        isHygieneContextTail (n.replacePrefix oldPre .anonymous) then
      return some (n.replacePrefix oldPre (appendNameRaw pre b))
  return none

def renameBinderOnce (mods : List (Name × Name)) (n : Name) : Name := Id.run do
  let mut pre : Name := .anonymous
  let mut previous : Name := .anonymous
  let mut afterAt := false
  for c in n.components do
    pre := appendNameRaw pre c
    if c == Name.mkSimple "_@" then
      afterAt := true
      if let some result := renameContextAt mods pre n then return result
      let internal := appendNameRaw (appendNameRaw pre (Name.mkSimple "_internal"))
        (Name.num .anonymous 0)
      if let some result := renameContextAt mods internal n then return result
    else if afterAt && previous == Name.mkSimple "_hygCtx" then
      match c with
      | .num .anonymous _ =>
        if let some result := renameContextAt mods pre n then return result
      | _ => pure ()
    previous := c
  return n

-- Rename every explicitly recognized module-context frame, including nested
-- contexts after _hygCtx.<scope>. The exact tail guard retains all original
-- numeric context hashes/scopes/seeds and all surrounding Name components.
partial def renameBinder (mods : List (Name × Name)) (n : Name) : Name := Id.run do
  let mut result := n
  let mut changed := true
  while changed do
    let next := renameBinderOnce mods result
    changed := next != result
    result := next
  return result

def levelTree : Level → Json
  | .zero => node "zero"
  | .succ u => node "succ" [levelTree u]
  | .max u v => node "max" [levelTree u,levelTree v]
  | .imax u v => node "imax" [levelTree u,levelTree v]
  | .param n => node "param" [nameTree n]
  | .mvar v => node "mvar" [nameTree v.name]

def substringTree (s : Substring.Raw) : Json :=
  node "substring" [toJson s.str,toJson s.startPos.byteIdx,toJson s.stopPos.byteIdx]

def sourceInfoTree : SourceInfo → Json
  | .original l p t e => node "original" [substringTree l,toJson p.byteIdx,substringTree t,toJson e.byteIdx]
  | .synthetic p e c => node "synthetic" [toJson p.byteIdx,toJson e.byteIdx,toJson c]
  | .none => node "none"

def preresolvedTree : Syntax.Preresolved → Json
  | .namespace n => node "namespace" [nameTree n]
  | .decl n fs => node "declaration" [nameTree n,toJson fs]

partial def syntaxTree : Syntax → Json
  | .missing => node "missing"
  | .node i k xs => node "syntaxNode" [sourceInfoTree i,nameTree k,toJson (xs.toList.map syntaxTree)]
  | .atom i s => node "atom" [sourceInfoTree i,toJson s]
  | .ident i r n ps => node "identifier" [sourceInfoTree i,substringTree r,nameTree n,toJson (ps.map preresolvedTree)]

-- Entire metadata is encoded structurally, including syntax/source positions.
-- No pretty-print representation, hash, dropping or metadata normalization.
def dataTree : DataValue → Json
  | .ofString s => node "string" [toJson s]
  | .ofBool b => node "bool" [toJson b]
  | .ofName n => node "name" [nameTree n]
  | .ofNat k => node "nat" [toJson k]
  | .ofInt k => node "int" [toJson k]
  | .ofSyntax s => node "syntax" [syntaxTree s]

def binderInfoTree : BinderInfo → Json
  | .default => node "default"
  | .implicit => node "implicit"
  | .strictImplicit => node "strictImplicit"
  | .instImplicit => node "instanceImplicit"

structure DagState where
  cache : ExprStructMap Nat := {}
  nodes : Array Json := #[]

-- ExprStructMap's BEq is Expr.equal; it keeps binder names and annotations.
-- Ordinary ExprMap/Expr.eqv must never be used here.
partial def internExpr (mods : List (Name × Name)) (e : Expr) : StateM DagState Nat := do
  if let some id := (← get).cache.get? ⟨e⟩ then return id
  let (tag,data,children) ← match e with
    | .bvar k => pure ("bvar",[toJson k],[])
    | .fvar f => pure ("fvar",[nameTree f.name],[])
    | .mvar m => pure ("mvar",[nameTree m.name],[])
    | .sort u => pure ("sort",[levelTree u],[])
    | .const c us => pure ("constant",[nameTree (renamePrivate mods c),toJson (us.map levelTree)],[])
    | .app f a => do
      let fi ← internExpr mods f
      let ai ← internExpr mods a
      pure ("application",[],[fi,ai])
    | .lam n t b i => do
      let ti ← internExpr mods t
      let bi ← internExpr mods b
      pure ("lambda",[nameTree (renameBinder mods n),binderInfoTree i],[ti,bi])
    | .forallE n t b i => do
      let ti ← internExpr mods t
      let bi ← internExpr mods b
      pure ("forall",[nameTree (renameBinder mods n),binderInfoTree i],[ti,bi])
    | .letE n t v b nd => do
      let ti ← internExpr mods t
      let vi ← internExpr mods v
      let bi ← internExpr mods b
      pure ("let",[nameTree (renameBinder mods n),toJson nd],[ti,vi,bi])
    | .lit (.natVal k) => pure ("naturalLiteral",[toJson k],[])
    | .lit (.strVal s) => pure ("stringLiteral",[toJson s],[])
    | .mdata md b => do
      let bi ← internExpr mods b
      pure ("metadata",[toJson (md.entries.map fun (n,v) => node "entry" [nameTree n,dataTree v])],[bi])
    | .proj s i b => do
      let bi ← internExpr mods b
      pure ("projection",[nameTree (renamePrivate mods s),toJson i],[bi])
  let st ← get
  let id := st.nodes.size
  let record := Json.mkObj [("tag",toJson tag),("data",toJson data),("children",toJson children)]
  set ({ cache := st.cache.insert ⟨e⟩ id, nodes := st.nodes.push record } : DagState)
  return id

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def exportModuleData (env : Environment) (modules : List (Name × Name))
    (mods : List (Name × Name)) (out : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk out .write
  let mut found : List Name := []
  let mut count := 0
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if let some (_,canonicalModule) := modules.find? (fun p => p.1 == m) then
      found := m :: found
      for ci in env.header.moduleData[i]!.constants do
        let value := ci.value? (allowOpaque := true)
        if ["definition","theorem","opaque"].contains (kind ci) && value.isNone then
          throw (IO.userError s!"Missing full actual body {ci.name}; no fallback")
        let compute : StateM DagState (Nat × Option Nat) := do
          let t ← internExpr mods ci.type
          let v ← value.mapM (internExpr mods)
          pure (t,v)
        let ((typeRoot,valueRoot),dag) := compute.run {}
        let record := Json.mkObj [
          ("module",toJson canonicalModule.toString),
          ("name",toJson (renamePrivate mods ci.name).toString),
          ("exact_name_tree",nameTree (renamePrivate mods ci.name)),
          ("kind",toJson (kind ci)),
          ("levelParams",toJson (ci.levelParams.map nameTree)),
          ("typeRoot",toJson typeRoot),
          ("valueRoot",toJson valueRoot),
          ("fullExprNodes",toJson dag.nodes)]
        handle.putStrLn record.compress
        handle.flush
        count := count + 1
  for (m,_) in modules do
    unless found.contains m do
      throw (IO.userError s!"Requested actual module not loaded {m}; no fallback")
  handle.flush
  IO.println s!"EXPORTED ALL {count} actual moduleData constants; COMPLETE Name/Level/Expr/DataValue/Syntax DAG; all types/definitions/theorem and opaque bodies; exact module private/hygienic-binder renaming only. ExprStructMap uses Expr.equal, NOT alpha Expr.eqv. ZERO fallback, unfolding, defeq, auxiliary skips or numeric erasure."

end HironakaNativeMigrationCanonical

def readExactModulePairs (file : String) : IO (List (Lean.Name × Lean.Name)) := do
  let mut pairs : List (Lean.Name × Lean.Name) := []
  for line in ← IO.FS.lines file do
    match line.splitOn "\t" with
    | [a,b] =>
      if a.isEmpty || b.isEmpty then throw (IO.userError s!"Empty module in {file}")
      pairs := pairs ++ [(a.toName,b.toName)]
    | _ => throw (IO.userError s!"Invalid exact module-map line in {file}: {line}")
  pure pairs

def main (args : List String) : IO UInt32 := do
  match args with
  | [ownFile,publicFile,renameFile,out] =>
    Lean.initSearchPath (← Lean.findSysroot)
    let ownModules ← readExactModulePairs ownFile
    let publicModules ← readExactModulePairs publicFile
    let moduleRenames ← readExactModulePairs renameFile
    let env ← Lean.importModules (((ownModules ++ publicModules).map (·.1)).toArray.map fun m => {module := m}) {}
    let mut publicPrivateUsers : Lean.NameSet := {}
    for i in [0:env.header.moduleNames.size] do
      if (`Hironaka).isPrefixOf env.header.moduleNames[i]! then
        for ci in env.header.moduleData[i]!.constants do
          if let some user := Lean.privateToUserName? ci.name then
            publicPrivateUsers := publicPrivateUsers.insert user
    let mut pending : Array Lean.Name := #[]
    for i in [0:env.header.moduleNames.size] do
      if ownModules.any (fun pair => pair.1 == env.header.moduleNames[i]!) then
        for ci in env.header.moduleData[i]!.constants do
          pending := pending ++ ci.type.getUsedConstants
          pending := pending ++ ((ci.value? (allowOpaque := true)).map Lean.Expr.getUsedConstants).getD #[]
    let mut seen : Lean.NameSet := {}
    let mut missing : Array Lean.Json := #[]
    while !pending.isEmpty do
      let c := pending.back!
      pending := pending.pop
      if seen.contains c then continue
      seen := seen.insert c
      let some idx := env.getModuleIdxFor? c | continue
      let owner := env.header.moduleNames[idx.toNat]!
      unless (`TranscendentalNakamaye).isPrefixOf owner do continue
      if ownModules.any (fun p => p.1 == owner) then continue
      let target := HironakaNativeMigrationCanonical.renamePrivate moduleRenames c
      if env.contains target && target != c then continue
      if let some user := Lean.privateToUserName? c then
        if publicPrivateUsers.contains (HironakaNativeMigrationCanonical.renameNamespace user) then continue
      missing := missing.push (Lean.Json.mkObj [("source",Lean.toJson c.toString),("owner",Lean.toJson owner.toString),("target",Lean.toJson target.toString),("private",Lean.toJson (Lean.privateToUserName? c).isSome)])
      let some ci := env.header.moduleData[idx.toNat]!.constants.find? (·.name == c) | continue
      pending := pending ++ ci.type.getUsedConstants
      pending := pending ++ ((ci.value? (allowOpaque := true)).map Lean.Expr.getUsedConstants).getD #[]
    IO.FS.writeFile out (Lean.Json.arr missing).pretty
    IO.println s!"MISSING_DEPENDENCIES {missing.size}; inspected {seen.size} actual referenced names"
    pure 0
  | _ => throw (IO.userError "own modules, existing public modules, exact renames, output")
