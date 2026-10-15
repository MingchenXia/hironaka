/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Resolution.StrictTransformComposition

/-! Exact original geometric strict-transform fragments omitted by the older
public selection. Complete original statements/proofs, without new premises. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.BlowupStrictIdeal
open Hironaka Hironaka.BlowupSequences Hironaka.BlowupStrictSubmanifold
noncomputable section
variable {n : ℕ}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

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

namespace Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka Hironaka.BlowupStrictSubmanifold
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] (𝔪 : MarkedIdeal n M) (C : Set M) (π : M' → M)
variable {𝔪 C π}

/-- **A set inside the centre has empty strict transform**: this is what removes, e.g., an
exceptional member `H` blown up again as a codimension-one centre `C = H`. -/
theorem geoStrictTransform_eq_empty_of_subset {A : Set M} (hA : A ⊆ C) :
    geoStrictTransform π C A = ∅ := by
  rw [geoStrictTransform, sdiff_eq_empty.mpr hA, preimage_empty, closure_empty]

end
end Hironaka.MarkedIdeals.MarkedIdeal
