/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalBirthCartierBoundary
import Hironaka.Resolution.HironakaLocalPrincipalization

/-! Actual finite blowup surjectivity and proper closed images supply the
whole original ambient/curve coverage of the SAME global sharp endpoint. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveOriginalGlobalEndpoint
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalStrictClosure HironakaSharpActualCurveGlobalGoodIsomorphism
  HironakaSharpActualCurveGluedStrictSets HironakaSharpOriginalMultiBoundaryBadLocus
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- A genuine original finite projection supplies a real point of every
full global fibre, before any global surjectivity is asserted. -/
theorem gluedProjection_surjective (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) : Function.Surjective (gluedProjection A) := by
  intro x
  obtain ⟨i,hxi⟩ := hc x
  let T := (A.prefixTower i).append (A.tail i)
  obtain ⟨z,hz⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective
    T.isBlowupSequence (⟨x,hxi⟩ : A.openSet i)
  refine ⟨endpointLocalInclusion A i z,?_⟩
  rw [gluedProjection_local_full A i z,hz]

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

theorem originalEndpointProjection_surjective :
    Function.Surjective (originalEndpointProjection hn hW hE hdense hr) :=
  gluedProjection_surjective _ (originalEndpointHistories_cover hn hW hE hdense hr)

/-- Genuine proper closed-image theory and ORIGINAL good-set density give
BOTH full image directions, including points over the original bad set. -/
theorem image_conventionalStrictCurve_eq_original :
    (originalEndpointProjection hn hW hE hdense hr) ''
      strictTransform n (originalEndpointProjection hn hW hE hdense hr) W=W := by
  let π := originalEndpointProjection hn hW hE hdense hr
  have hπ := originalEndpointProjection_contMDiff hn hW hE hdense hr
  have hIso := originalEndpointProjection_isIsomorphismOver_good hn hW hE hdense hr
  have hClosed : IsClosed (π '' strictTransform n π W) :=
    (originalEndpointProjection_isProperMap hn hW hE hdense hr).isClosedMap _ isClosed_closure
  have hIn : strictTransform n π W⊆π ⁻¹' W :=
    closure_minimal sdiff_subset (hW.1.preimage hπ.continuous)
  have hDenseImage : W \ ⋃ H∈E,H ⊆ π '' strictTransform n π W := by
    intro x hx
    have hGood : x∈originalGoodLocus (n := n) W E := by
      by_contra hNot
      have hBad : x∈originalSharpBadLocus (n := n) W E := by
        rw [originalSharpBadLocus_eq_compl_good]
        exact hNot
      exact hx.2 (originalSharpBadLocus_subset_boundary hW hBad).2
    obtain ⟨z,hzGood,hzx⟩ := hIso.1.2.2 hGood
    have hzNot : z∉exceptionalLocus n π :=
      fun hzExc => disjoint_left.mp hIso.2 hzGood hzExc
    refine ⟨z,subset_closure ⟨?_,hzNot⟩,hzx⟩
    change π z∈W
    rw [hzx]
    exact hx.1
  exact Subset.antisymm (by rintro x ⟨z,hz,rfl⟩;exact hIn hz)
    (hdense.trans (closure_minimal hDenseImage hClosed))

theorem image_gluedStrictCurve_eq_original :
    (originalEndpointProjection hn hW hE hdense hr) ''
      originalGluedStrictSet hn hW hE hdense hr W=W := by
  rw [originalGluedStrictCurve_eq_strictTransform hn hW hE hdense hr]
  exact image_conventionalStrictCurve_eq_original hn hW hE hdense hr

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveOriginalGlobalEndpoint
