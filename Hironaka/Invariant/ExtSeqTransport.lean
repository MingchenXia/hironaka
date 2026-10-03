/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantSeq
set_option autoImplicit false

/-!
# Transporting results about resolution invariants from the uniform form of (8) to the per-sequence form

The Step 1 (maximal-order) value of `hir:maximal-order-step` and its properties were formalized for a lower invariant
`R : ResolutionInvariantExt.ResolutionInvariant n (k - 1) Λ`.  Their proofs use `R` only through its value function and its
properties (1)--(7), (4'), never through property (8) and never through the constructor.  The command of this module makes this
precise and gives the same results for `R : ResolutionInvariantSeq.ResolutionInvariant n (k - 1) Λ`.

## The command

Its type and value are those of the old constant with

* the structure `ResolutionInvariantExt.ResolutionInvariant` replaced by `ResolutionInvariantSeq.ResolutionInvariant` (same
  parameters, same universe levels);
* the projection `R.inv` replaced by `R.inv` of the new structure, and each projection `R.admissible`, `R.usc`, `R.decrease`,
  `R.emptyStep`, `R.emptyPrefix`, `R.restrictOpen`, `R.towerIso`, `R.representative` by the field of the same name of
  `R.isInvValue : ResolutionInvariantSeq.IsInvValue n k R.inv` (the types of the fields agree, `ResolutionInvariantSeq.isInvValue_ext`);
* every constant depending on the old structure replaced by its new counterpart.

`transport_ext_to_seq_module M₁ M₂ …` does this for every declaration of the modules `Mᵢ` that depends on the old structure.

Every new constant is added with `addDecl`, i.e. **checked by the kernel**; nothing is assumed. The command fails if
a value uses property (8) (`locallyFinite`), the constructor or any other declaration of the old structure, so a
successful transport is a proof that the transported results need only properties (1)--(7), (4'). Definitions are
added as `noncomputable`, with the reducibility of the original; theorems as theorems.
-/

namespace Hironaka.ExtSeqTransport

open Lean Meta Elab Command

/-- The old structure (uniform form of (8)). -/
def extStruct : Name := `Hironaka.ResolutionInvariantExt.ResolutionInvariant

/-- The new structure (per-sequence form of (8)). -/
def seqStruct : Name := `Hironaka.ResolutionInvariantSeq.ResolutionInvariant

/-- The predicate of properties (1)--(7), (4') of the new structure. -/
def seqIsInvValue : Name := `Hironaka.ResolutionInvariantSeq.IsInvValue

/-- The fields (1)--(7), (4') shared by the old structure and `IsInvValue`. -/
def sharedFields : List Name :=
  [`admissible, `usc, `decrease, `emptyStep, `emptyPrefix, `restrictOpen, `towerIso, `representative]

/-- The name of the transported constant: `Seq` inserted after `Hironaka`. -/
def seqName (c : Name) : Name :=
  let p := `Hironaka
  if p.isPrefixOf c then c.replacePrefix p (p ++ `Seq) else (p ++ `Seq) ++ c

/-- Constants used in the type and in the value of a declaration. -/
def usedConsts (ci : ConstantInfo) : Array Name :=
  let s := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => s ++ v.getUsedConstants
  | none => s

def isProjectConst (c : Name) : Bool :=
  (`Hironaka).isPrefixOf c || (`_private.Hironaka).isPrefixOf c

/-- The constants to transport, in dependency order (the given ones and every project constant they use, transitively, which
depends on the old structure, except those already transported, whose new name exists), and the set of all project constants
used which depend on the old structure (to be renamed). -/
partial def collect (roots : Array Name) : CoreM (Array Name × NameSet) := do
  let env ← getEnv
  let memo ← IO.mkRef ({} : Std.HashMap Name Bool)
  let order ← IO.mkRef (#[] : Array Name)
  let rec visit (c : Name) : CoreM Bool := do
    if let some b := (← memo.get).get? c then return b
    memo.modify (·.insert c false)
    if c == extStruct || extStruct.isPrefixOf c then
      memo.modify (·.insert c true); return true
    if !isProjectConst c then return false
    let some ci := env.find? c | return false
    let mut r := false
    for d in usedConsts ci do
      if (← visit d) then r := true
    memo.modify (·.insert c r)
    if r && !(env.contains (seqName c)) then order.modify (·.push c)
    return r
  for c in roots do
    if c == extStruct || extStruct.isPrefixOf c then
      throwError "transport_ext_to_seq: {c} is a declaration of {extStruct} itself"
    unless (← visit c) do
      throwError "transport_ext_to_seq: {c} does not depend on {extStruct}"
  let deps := (← memo.get).fold (init := ({} : NameSet)) fun s c b =>
    if b && !(c == extStruct || extStruct.isPrefixOf c) then s.insert c else s
  return (← order.get, deps)

/-- Replace the old structure, its projections and the transported constants in an expression (a purely syntactic
replacement; the kernel checks the result). A projection `R.inv` becomes `R.inv` of the new structure, a projection
`R.f` for a field `f` of (1)--(7), (4') becomes `R.isInvValue.f`. -/
partial def replaceExt (ported : NameSet) (e : Expr) : Expr :=
  e.replace fun e =>
    match e with
    | .const c us =>
      if c == extStruct then some (.const seqStruct us)
      else if ported.contains c then some (.const (seqName c) us)
      else none
    | .proj s i b =>
      if s != extStruct then none
      else
        let b' := replaceExt ported b
        if i == 0 then some (.proj seqStruct 0 b')
        else if i ≤ sharedFields.length then some (.proj seqIsInvValue (i - 1) (.proj seqStruct 1 b'))
        else none
    | .app .. =>
      match e.getAppFn with
      | .const c us =>
        if extStruct.isPrefixOf c && c != extStruct && e.getAppNumArgs == 5 then
          let args := e.getAppArgs.map (replaceExt ported)
          let inv := mkAppN (.const (seqStruct ++ `inv) us) args
          if c == extStruct ++ `inv then some inv
          else match sharedFields.find? (fun f => c == extStruct ++ f) with
            | some f =>
              let isv := mkAppN (.const (seqStruct ++ `isInvValue) us) args
              some (mkAppN (.const (seqIsInvValue ++ f) us) ((args.extract 0 4) ++ #[inv, isv]))
            | none => none
        else none
      | _ => none
    | _ => none

def transportExpr (ported : NameSet) (e : Expr) : MetaM Expr := do
  let e := replaceExt ported e
  let bad := e.getUsedConstants.filter fun c => c == extStruct || extStruct.isPrefixOf c
  unless bad.isEmpty do
    throwError "transport_ext_to_seq: {bad} is used (only (1)-(7), (4') and the value function can be transported)"
  if (e.find? fun e => match e with | .proj s _ _ => s == extStruct | _ => false).isSome then
    throwError "transport_ext_to_seq: property (8) of {extStruct} is used"
  return e

/-- Transport one constant (its dependencies are already transported). -/
def transportConst (ported : NameSet) (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let new := seqName c
  let ty ← transportExpr ported ci.type
  match ci with
  | .thmInfo v =>
    let val ← transportExpr ported v.value
    addDecl (.thmDecl { name := new, levelParams := v.levelParams, type := ty, value := val })
  | .defnInfo v =>
    let val ← transportExpr ported v.value
    let d : DefinitionVal :=
      { name := new
        levelParams := v.levelParams
        type := ty
        value := val
        hints := v.hints
        safety := v.safety
        all := [new] }
    addDecl (.defnDecl d)
    modifyEnv (addNoncomputable · new)
    setReducibilityStatus new (← getReducibilityStatus c)
  | .opaqueInfo v =>
    let val ← transportExpr ported v.value
    let d : OpaqueVal :=
      { name := new
        levelParams := v.levelParams
        type := ty
        value := val
        isUnsafe := v.isUnsafe
        all := [new] }
    addDecl (.opaqueDecl d)
  | _ => throwError "transport_ext_to_seq: {c} is not a theorem, definition or opaque constant"
  addDocStringCore new s!"Transported by `transport_ext_to_seq` from `{c}` (`ResolutionInvariantExt` → `ResolutionInvariantSeq`)."

/-- `transport_ext_to_seq c₁ c₂ …`: see the module documentation. -/
syntax (name := transportExtToSeq) "transport_ext_to_seq " ident+ : command

@[command_elab transportExtToSeq] def elabTransportExtToSeq : CommandElab := fun stx => do
  let ids := stx[1].getArgs
  let roots ← ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM do
    let (order, ported) ← collect roots
    for c in order do
      transportConst ported c

/-- An auxiliary constant (internal name, matcher, abstracted proof, equation lemma): never a root of the module form. -/
def isAuxName (c : Name) : Bool :=
  c.isInternal ||
    match c with
    | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" || s.startsWith "_"
    | _ => true

/-- The declarations of a module which depend on the old structure (auxiliary constants excluded). -/
partial def moduleRoots (m : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let some i := env.getModuleIdx? m | throwError "transport_ext_to_seq_module: unknown module {m}"
  let memo ← IO.mkRef ({} : Std.HashMap Name Bool)
  let rec dep (c : Name) : CoreM Bool := do
    if let some b := (← memo.get).get? c then return b
    memo.modify (·.insert c false)
    if c == extStruct || extStruct.isPrefixOf c then
      memo.modify (·.insert c true); return true
    if !isProjectConst c then return false
    let some ci := env.find? c | return false
    let mut r := false
    for d in usedConsts ci do
      if (← dep d) then r := true
    memo.modify (·.insert c r)
    return r
  let mut out := #[]
  for c in env.header.moduleData[i.toNat]!.constNames do
    if isAuxName c || c == extStruct || extStruct.isPrefixOf c then continue
    if (← dep c) then out := out.push c
  return out

/-- `transport_ext_to_seq_module M₁ M₂ …`: `transport_ext_to_seq` applied to every declaration of the modules `Mᵢ` which depends
on `ResolutionInvariantExt.ResolutionInvariant` (auxiliary constants are transported when used). -/
syntax (name := transportExtToSeqModule) "transport_ext_to_seq_module " ident+ : command

@[command_elab transportExtToSeqModule] def elabTransportExtToSeqModule : CommandElab := fun stx => do
  let ids := stx[1].getArgs
  liftTermElabM do
    let mut roots := #[]
    for id in ids do
      roots := roots ++ (← moduleRoots id.getId)
    let (order, ported) ← collect roots
    for c in order do
      transportConst ported c

end Hironaka.ExtSeqTransport
