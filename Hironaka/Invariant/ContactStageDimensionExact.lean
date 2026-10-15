/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.ContactStageInvDomain

/-! Exact original contact-stage dimension fragment, retaining every original
section hypothesis and proof; no lower TEST or geometry certificate is added. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.ContactStageInvDomain
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdealAlong
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealEquivalence
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterTowerAlong
  ContactEquivalenceAlong MaximalContactAlongTower ContactEquivalenceStage DivisorExponentAlong CodimOneSupportAlong
  NormalCrossings
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open ResolutionInvariantSpec (DimLE IsInvDomain)
noncomputable section
variable {n : ℕ}
section Stage
variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hd : 1 ≤ 𝔪.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u)
  {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower 𝔪 T₀)

include hN h𝔞 hd hu hT₀ in
/-- **`dim N ≤ k` gives `dim (N ∩ V(u))_{T₀} ≤ k - 1` over `U`.** -/
theorem dimLE_strictAlong_stage {k : ℕ} (hk : DimLE n 𝔪.N k) :
    DimLE n ((Subtype.val : openPreimage T₀ U → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) (k - 1) := by
  intro y hy
  obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ y.2 hy
  obtain ⟨j', hj'k, hj'⟩ := InvDomainTowerAlong.dimLE_geoTransformAlong hN h𝔞 hk T₀ hT₀ y hj1.2.1
  have hjj := RegularPointDimension.eq_of_regularAtDim hj1 hj'
  exact ⟨j, by omega, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩


end Stage
end
end Hironaka.ContactStageInvDomain
