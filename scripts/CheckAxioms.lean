/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom check

`lake test` (or `lake env lean scripts/CheckAxioms.lean`) prints the axioms of selected public endpoints and fails if
any declaration owned by a `Hironaka` or `DeJongAlterations` module, including
private and generated declarations, depends on axioms other than `propext`,
`Classical.choice` and `Quot.sound`.
-/

open Lean Elab Command

#print axioms Hironaka.forall_isNonzeroAlongAt_univ_iff
#print axioms Hironaka.exists_principalization
#print axioms Hironaka.exists_principalization_of_isCompact
#print axioms Hironaka.exists_principalization_of_subset_isCompact
#print axioms Hironaka.exists_principalization_local
#print axioms Hironaka.exists_principalization_boundary
#print axioms Hironaka.exists_embeddedResolution
#print axioms Hironaka.exists_embeddedResolution_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_pure
#print axioms Hironaka.exists_embeddedResolution_pure_of_isCompact
#print axioms Hironaka.not_le_vanishingIdeal_univ
#print axioms Hironaka.exists_principalization_of_connected
#print axioms Hironaka.exists_principalization_boundary_of_compactSpace
#print axioms Hironaka.exists_principalization_boundary_of_subset_isCompact
#print axioms Hironaka.exists_principalization_boundary_local
#print axioms Hironaka.exists_embeddedResolution_local
#print axioms Hironaka.exists_embeddedResolution_pure_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_boundary_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_boundary
#print axioms Hironaka.exists_embeddedResolution_boundary_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_boundary_local
#print axioms Hironaka.eq_iUnion_dimensionPart
#print axioms Hironaka.isComplexAnalyticSubset_dimensionPart
#print axioms Hironaka.exists_embeddedResolution_dimensionPart_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_dimensionPart
#print axioms Hironaka.exists_embeddedResolution_dimensionPart_boundary_of_isCompact
#print axioms Hironaka.canonicalResolution
#print axioms Hironaka.exists_embeddedResolution_analytic_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary
#print axioms Hironaka.exists_separation
#print axioms Hironaka.isAdmissibleBlowupSequence_comp
#print axioms Hironaka.isIsomorphismOver_compl_of_isAdmissibleBlowupSequence
#print axioms Hironaka.exceptionalLocus_subset_of_isAdmissibleBlowupSequence
#print axioms Hironaka.exists_embeddedResolution_analytic_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic_local
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary_local
#print axioms Hironaka.exists_separation_of_subset_isCompact
#print axioms Hironaka.exists_restrict_opens
#check @Hironaka.deJongAlterationTheorem
#print axioms Hironaka.deJongAlterationTheorem
#print axioms Hironaka.exists_alterationWithBoundary
#check @DeJongAlterations.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem
#print axioms DeJongAlterations.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem

-- Namespace OR exact module ownership also covers adopted native-namespace APIs.
run_cmd do
  let env ← getEnv
  let moduleIndices := env.const2ModIdx
  let moduleNames := env.header.moduleNames
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut hironakaCount : Nat := 0
  let mut deJongCount : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (c, _) in env.constants.toList do
    let (hironakaOwned, deJongOwned) := match moduleIndices[c]? with
      | some idx =>
          ((`Hironaka).isPrefixOf moduleNames[idx]!,
           (`DeJongAlterations).isPrefixOf moduleNames[idx]!)
      | none => (false, false)
    if hironakaOwned || deJongOwned || (`Hironaka).isPrefixOf c ||
        (`DeJongAlterations).isPrefixOf c then
      n := n + 1
      if hironakaOwned then hironakaCount := hironakaCount + 1
      if deJongOwned then deJongCount := deJongCount + 1
      for a in (← liftCoreM <| collectAxioms c) do
        unless allowed.contains a do bad := bad.push (c, a)
  if hironakaCount == 0 || deJongCount == 0 then
    throwError "axioms check: refusing an empty Hironaka or DeJongAlterations audit"
  if bad.isEmpty then
    logInfo m!"axioms check: {n} declarations ({hironakaCount} Hironaka-owned, {deJongCount} DeJongAlterations-owned), including private/generated, all within [propext, Classical.choice, Quot.sound]"
  else
    throwError m!"axioms check: non-standard axioms: {bad.toList.take 20}"
