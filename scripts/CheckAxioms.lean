/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka

/-!
# Axiom check

`lake test` (or `lake env lean scripts/CheckAxioms.lean`) prints the axioms of every public theorem and fails if
any declaration of the library depends on axioms other than `propext`, `Classical.choice` and `Quot.sound`.
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

-- every non-internal declaration of every `Hironaka` module uses only the three standard axioms
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless (`Hironaka).isPrefixOf m do continue
    for c in env.header.moduleData[i]!.constNames do
      if c.isInternalDetail then continue
      n := n + 1
      for a in (← liftCoreM <| collectAxioms c) do
        unless allowed.contains a do bad := bad.push (c, a)
  if bad.isEmpty then
    logInfo m!"axioms check: {n} declarations, all within [propext, Classical.choice, Quot.sound]"
  else
    throwError m!"axioms check: non-standard axioms: {bad.toList.take 20}"
