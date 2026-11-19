import Hironaka.Resolution.HironakaG8CuspChartGlobalRegularity
import Hironaka.Resolution.HironakaG8CuspModelRegularity

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CuspRegularityPropagation

open Hironaka.BlowupSequences BlowupTowers HironakaEmbeddedAnalytic
  HironakaG8CuspChartGlobalRegularity HironakaG8CuspModelRegularity
  HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource HironakaStageCenters

variable {X Y : CMfd.{0} 3} {W : Set X} {x : X} {π : Y → X}

/-- With a unique strict point on the exceptional fibre, the only possible
remaining nonregular point is the next cusp anchor. -/
theorem cusp_step_regular_away
    (hπ : IsBlowupAlong 3 ({x} : Set X) π) (hW : IsClosed W)
    (hAway : ∀ u ∈ W, u ≠ x → RegularAtDim (n := 3) W u 1)
    (e : OpenPartialHomeomorph Y (ComplexModel 3)) (he : e ∈ atlas (ComplexModel 3) Y)
    {z : Y} (hz : z ∈ e.source) (h0 : e z = 0) (hFibre :
      strictTransform 3 π W ∩ π ⁻¹' ({x} : Set X) = {z})
    (p : ℕ) (hRead : ∀ y ∈ e.source, y ∈ strictTransform 3 π W ↔ e y ∈ embeddedCuspSet p) :
    ∀ y ∈ strictTransform 3 π W, y ≠ z →
      RegularAtDim (n := 3) (strictTransform 3 π W) y 1 := by
  have hCover : strictTransform 3 π W ∩ π ⁻¹' ({x} : Set X) ⊆ e.source := by
    rwa [hFibre,singleton_subset_iff]
  intro y hy hNe
  apply strictTransform_regular_outside_chart_exception hπ hW 1 hAway e he
    (embeddedCuspSet p) ({0} : Set (ComplexModel 3)) hRead hCover
    (fun u hu => regularAtDim_embedded_cusp_off_zero hu) y hy
  intro hv
  apply hNe
  exact e.injOn hv.1 hz ((mem_singleton_iff.mp hv.2).trans h0.symm)

/-- The whole terminal cusp is smooth once its unique strict exceptional
point is read in the exponent-one chart. -/
theorem cusp_last_step_smooth
    (hπ : IsBlowupAlong 3 ({x} : Set X) π) (hW : IsClosed W)
    (hAway : ∀ u ∈ W, u ≠ x → RegularAtDim (n := 3) W u 1)
    (e : OpenPartialHomeomorph Y (ComplexModel 3)) (he : e ∈ atlas (ComplexModel 3) Y)
    {z : Y} (hz : z ∈ e.source) (h0 : e z = 0) (hFibre :
      strictTransform 3 π W ∩ π ⁻¹' ({x} : Set X) = {z})
    (hRead : ∀ y ∈ e.source, y ∈ strictTransform 3 π W ↔ e y ∈ embeddedCuspSet 1) :
    IsClosedSubmanifold 3 (strictTransform 3 π W) := by
  refine ⟨isClosed_closure,fun y hy => ?_⟩
  by_cases h : y = z
  · subst y
    obtain ⟨d,hd⟩ := embedded_cusp_one_isClosedSubmanifold.2 (e z) ((hRead z hz).mp hy)
    exact ⟨d,(regularAtDim_atlas_chart e he hz _ _ hRead d).mpr hd⟩
  · exact ⟨1,cusp_step_regular_away hπ hW hAway e he hz h0 hFibre 1 hRead y hy h⟩

end Hironaka.HironakaG8CuspRegularityPropagation
