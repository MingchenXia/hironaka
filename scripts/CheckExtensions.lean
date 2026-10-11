/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka

open Lean Elab Command

#print axioms Hironaka.HironakaDimensionGlobalComponents.isPureDim_closure_component
#print axioms Hironaka.HironakaDimensionGlobalComponents.exists_unique_isPureDim_of_mem_globalComponents
#print axioms Hironaka.HironakaDimensionGlobalComponents.isClosed_sUnion_globalComponents_subfamily
#print axioms Hironaka.HironakaDimensionGlobalComponents.subset_dimensionPart_of_mem_globalComponents_of_isPureDim
#print axioms Hironaka.HironakaDimensionGlobalComponents.dimensionPart_eq_sUnion_globalComponents
#print axioms Hironaka.HironakaDimensionGlobalComponents.isPureDim_dimensionPart
#print axioms Hironaka.HironakaDimensionGlobalComponents.isPureDim_iff_subset_dimensionPart_of_mem_globalComponents
#print axioms Hironaka.HironakaDimensionGlobalComponents.localDecomposition_dimensionPart
#print axioms Hironaka.HironakaDimensionGlobalComponents.exists_localDecomposition_dimensionPart
#print axioms Hironaka.HironakaNormalCrossingsTransversality.isTransverse_of_hasNormalCrossings_of_subset_closure_diff
#print axioms Hironaka.HironakaNormalCrossingsTransversality.isTransverse_strictTransform_of_support_subset
#print axioms Hironaka.HironakaNormalCrossingsTransversality.isTransverse_strictTransform_of_admissible_of_preimage_subset_exceptional
#print axioms Hironaka.HironakaNormalCrossingsTransversality.isTransverse_strictTransform_of_admissible
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_pure_transverse_of_isCompact
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_pure_transverse
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_boundary_transverse_of_isCompact
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_boundary_transverse
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_analytic_transverse_of_isCompact
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_analytic_boundary_transverse_of_isCompact
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_pure_transverse_of_subset_isCompact
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_boundary_transverse_of_subset_isCompact
#print axioms Hironaka.HironakaNormalCrossingsTransversality.exists_embeddedResolution_boundary_transverse_local
#print axioms Hironaka.HironakaDivisorPowers.cosupport_idealPow_mul_succ_eq
#print axioms Hironaka.HironakaDivisorPowers.isDivNear_idealPow_mul_succ_iff
#print axioms Hironaka.HironakaDivisorPowers.isNonzeroAt_idealPow
#print axioms Hironaka.HironakaDivisorPowers.divExp_idealPow
#print axioms Hironaka.HironakaDivisorPowers.cosupport_idealPow_mul_succ_eq_along
#print axioms Hironaka.HironakaDivisorPowers.isDivNearAlong_idealPow_mul_succ_iff
#print axioms Hironaka.HironakaDivisorPowers.isNonzeroAlongAt_idealPow
#print axioms Hironaka.HironakaDivisorPowers.divExpAlong_idealPow
#print axioms Hironaka.HironakaDivisorPowers.isNonzeroAt_of_isInvertible
#print axioms Hironaka.HironakaDivisorPowers.divExp_divisor_idealPow
#print axioms Hironaka.HironakaDivisorResidual.isLocallyConstant_divExp_on_submanifold
#print axioms Hironaka.HironakaDivisorResidual.exists_divExp_on_connected_submanifold
#print axioms Hironaka.HironakaDivisorResidual.interior_eq_empty_of_smooth_hypersurface
#print axioms Hironaka.HironakaDivisorResidual.exists_residual_on_connected_hypersurface
#print axioms Hironaka.HironakaDivisorResidual.exists_residual_power_on_connected_hypersurface
#print axioms Hironaka.HironakaDivisorResidual.componentPowerProduct
#print axioms Hironaka.HironakaDivisorResidual.isCoherent_componentPowerProduct
#print axioms Hironaka.HironakaDivisorResidual.exists_residual_on_finite_connected_hypersurfaces

/- Audit every constant in the 2026-10-11 extension/support modules. -/
run_cmd do
  let env ← getEnv
  let modules : List Name := [`Hironaka.Analytic.GlobalComponents, `Hironaka.Resolution.HironakaDimensionGlobalComponents, `Hironaka.Resolution.HironakaNormalCrossingsTransversality, `Hironaka.Analytic.ActualInvertibleIdealDifference, `Hironaka.Resolution.HironakaDivisorPowers, `Hironaka.Resolution.HironakaDivisorResidual, `Hironaka.Analytic.GeometricPureDimension, `Hironaka.Analytic.GlobalComponentRegularity, `Hironaka.Invariant.AmbientDivisorExponent, `Hironaka.Blowup.SmoothHypersurfaceIdeal]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  let mut publicN : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless modules.contains env.header.moduleNames[i]! do continue
    for c in env.header.moduleData[i]!.constNames do
      total := total + 1
      let user := (privateToUserName? c).getD c
      unless user.isInternalDetail do publicN := publicN + 1
      let axs ← liftCoreM <| collectAxioms c
      logInfo m!"{c}: {axs}"
      for a in axs do
        unless allowed.contains a do throwError m!"non-standard axiom {a} in {c}"
  logInfo m!"Extension axiom check: {total} constants, {publicN} non-internal declarations, all within [propext, Classical.choice, Quot.sound]"
