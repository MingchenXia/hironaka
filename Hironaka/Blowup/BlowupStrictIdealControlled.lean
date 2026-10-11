/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.ControlledTransformUniqueness

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.BlowupStrictIdeal
open Hironaka VanishingIdealCoherent
noncomputable section
open BlowupSequences HolomorphicIdealSheaves BlowupStrictSubmanifold
open GermIdealTotalTransform IdealWeightPowers BlowupExceptionalDivisor BlowupControlledTransform
universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The controlled transform of the ideal of `N ⊇ C` with the mark one is the ideal of the
strict transform**: `σ^c(𝓘_N, 1) = 𝓘_{N'}`. -/
theorem controlledTransform_vanishingIdeal (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) :
    controlledTransform hπ (vanishingIdeal (n := n) N) 1 =
      vanishingIdeal (n := n) (geoStrictTransform π C N) := by
  refine (eq_controlledTransform_of_eq_mul hπ (isCoherent_vanishingIdeal
    (isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN)) ?_).symm
  rw [idealPow_one_exceptionalDivisor, pullback_vanishingIdeal_eq_mul hπ hN hCN]

/-! ### Comparison with the library's strict transform -/

/-- The geometric strict transform lies in the library's one. -/
theorem geoStrictTransform_subset_strictTransform (hπ : IsBlowupAlong n C π) (N : Set X) :
    geoStrictTransform π C N ⊆ strictTransform n π N := by
  unfold geoStrictTransform strictTransform
  exact closure_mono fun u hu => ⟨hu.1, fun hE =>
    hu.2 (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hE)⟩

/-- **If the centre is nowhere dense in `N`, the geometric strict transform
`closure (π⁻¹(N \ C))` is the library's `strictTransform n π N = closure (π⁻¹N \ Exc π)`.**
Off `Exc π` the blowup is open (inverse function theorem), so points of `N \ C` near `π u`
lift to points near `u`. -/
theorem geoStrictTransform_eq_strictTransform (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : N ⊆ closure (N \ C)) :
    geoStrictTransform π C N = strictTransform n π N := by
  refine (geoStrictTransform_subset_strictTransform hπ N).antisymm ?_
  show closure (π ⁻¹' N \ exceptionalLocus n π) ⊆ _
  refine closure_minimal (fun u hu => ?_) isClosed_closure
  obtain ⟨huN, huE⟩ := hu
  rw [geoStrictTransform, mem_closure_iff_nhds]
  intro V hV
  have hmap := StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
    hπ.contMDiff huE
  have himg : π '' V ∈ 𝓝 (π u) := by
    rw [← hmap]; exact image_mem_map hV
  obtain ⟨x, ⟨v, hvV, rfl⟩, hx⟩ := mem_closure_iff_nhds.mp (hN huN) _ himg
  exact ⟨v, hvV, hx⟩


end
end Hironaka.BlowupStrictIdeal
