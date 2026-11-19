import Hironaka.Resolution.HironakaG8CuspRegularityPropagation
import Hironaka.Resolution.HironakaG8DimensionZeroSingularTest
import Hironaka.Resolution.HironakaG8ActualCuspExceptionalFibre

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CuspPointTowerEndpoint

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaEmbeddedAnalytic HironakaG8OddCuspVanishingStalk
  HironakaG8OddCuspGeometricSource HironakaStageCenters HironakaG8OccupiedSlotComparison
  HironakaG8CuspPointTower HironakaG8CuspChartGlobalRegularity HironakaG8DimensionZeroSingularTest
  HironakaG8CuspRegularityPropagation HironakaG8CuspModelRegularity HironakaG8OddCuspStrictChart
  HironakaG8ActualCuspExceptionalFibre
  AnalyticDimensionBasics RegularPointDimension BlowupExistenceOriginIdeal NormalCrossings

private theorem zero_mem_cusp (p : ℕ) (hp : 0 < p) : (0 : ComplexModel 3) ∈ embeddedCuspSet p :=
  (embedded_cusp_mem_iff p _).mpr (by simp [zero_pow hp.ne'])

private theorem dimLE_centre_of_centred_chart {X : CMfd.{0} 3}
    (e : OpenPartialHomeomorph X (ComplexModel 3))
    (he : e ∈ atlas (ComplexModel 3) X) {x : X} (hx : x ∈ e.source)
    (h0 : e x = 0) : DimLE (n := 3) ({x} : Set X) 0 := by
  have hChart : ∀ y ∈ e.source, y ∈ ({x} : Set X) ↔ e y ∈ ({0} : Set (ComplexModel 3)) := by
    intro y hy
    simp only [mem_singleton_iff]
    exact ⟨fun h => h ▸ h0,fun h => e.injOn hy hx (h.trans h0.symm)⟩
  have hs : RegularAtDim (n := 3) ({x} : Set X) x 0 :=
    (regularAtDim_atlas_chart e he hx _ _ hChart 0).mpr (h0.symm ▸ regularAtDim_zero)
  intro y k hy
  have hyx := mem_singleton_iff.mp hy.2.1
  subst y
  exact (eq_of_regularAtDim hy hs).le

/-- Three genuine successive point blowups have intrinsically singular
centres with the same exact original footprint. Their whole terminal strict
carrier is smooth, and the tower is a test of the original mark-one ideal. -/
theorem exists_three_cusp_point_blowups_smooth
:
    ∃ (Z : CMfd.{0} 3) (T : BlowupTower CuspAmbient Z),
      T.length = 3 ∧
      IsClosedSubmanifold 3 (strictTransform 3 T.proj (embeddedCuspSet 7)) ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := 3) (embeddedCuspSet 7),1⟩ :
        MarkedIdeal 3 CuspAmbient) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 3)
        (strictTransform 3 P.proj (embeddedCuspSet 7))) T ∧
      (∀ i < 3, slotFootprint T i = ({0} : Set CuspAmbient)) ∧
      ∃ (e : OpenPartialHomeomorph Z (ComplexModel 3)) (z : Z),
        e ∈ atlas (ComplexModel 3) Z ∧ z ∈ e.source ∧ e z = 0 ∧
        T.proj z = 0 ∧
        ∀ y ∈ e.source, y ∈ strictTransform 3 T.proj (embeddedCuspSet 7) ↔
          e y ∈ embeddedCuspSet 1 := by
  have hUnique {X Y : CMfd.{0} 3} {W : Set X} {x : X} {π : Y → X}
      (hπ : IsBlowupAlong 3 ({x} : Set X) π) (p : ℕ) (hp : 2 < p)
      (e : OpenPartialHomeomorph X (ComplexModel 3))
      (he : e ∈ atlas (ComplexModel 3) X) (hx : x ∈ e.source) (h0 : e x = 0)
      (hRead : ∀ u ∈ e.source, u ∈ W ↔ e u ∈ embeddedCuspSet p) :
      (strictTransform 3 π W ∩ π ⁻¹' ({x} : Set X)).Subsingleton := by
    obtain ⟨z,_,hOnly⟩ := existsUnique_actual_cusp_exceptional_fibre hπ e he hx h0 W p hp hRead
    intro u hu v hv
    exact (hOnly u ⟨hu.1,hu.2⟩).trans (hOnly v ⟨hv.1,hv.2⟩).symm
  let e := chartAt (ComplexModel 3) (0 : CuspAmbient)
  have he : e = OpenPartialHomeomorph.refl (ComplexModel 3) := chartAt_self_eq
  have hRead : ∀ y ∈ e.source,
      y ∈ strictTransform 3 (id : CuspAmbient → CuspAmbient) (embeddedCuspSet 7) ↔
        e y ∈ embeddedCuspSet 7 := by
    rw [he, strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id,
      (embedded_cusp_isAnalytic 7).isClosed.closure_eq]
    intro y _
    rfl
  have hStart : (0 : CuspAmbient) ∈ e.source := mem_chart_source _ _
  have hZero : e (0 : CuspAmbient) = 0 := by rw [he]; rfl
  let T₀ : BlowupTower CuspAmbient CuspAmbient := .refl
  obtain ⟨Y₁,π₁,H₁,e₁,z₁,ha₁,hs₁,hz₁,he₁,hS₁,hR₁⟩ :=
    extend_cusp_point_tower (X := CuspAmbient) (Y := CuspAmbient) (embeddedCuspSet 7) T₀ 7 (by decide) (by decide) e
      (chart_mem_atlas _ _) 0 hStart hZero (by simpa only [T₀, BlowupTower.proj_refl] using hRead)
  let T₁ := T₀.step {0} π₁ H₁
  obtain ⟨Y₂,π₂,H₂,e₂,z₂,ha₂,hs₂,hz₂,he₂,hS₂,hR₂⟩ :=
    extend_cusp_point_tower (embeddedCuspSet 7) T₁ 5 (by decide) (by decide) e₁
      ha₁ z₁ hs₁ hz₁ hR₁
  let T₂ := T₁.step {z₁} π₂ H₂
  obtain ⟨Y₃,π₃,H₃,e₃,z₃,ha₃,hs₃,hz₃,he₃,hS₃,hR₃⟩ :=
    extend_cusp_point_tower (embeddedCuspSet 7) T₂ 3 (by decide) (by decide) e₂
      ha₂ z₂ hs₂ hz₂ hR₂
  let T₃ := T₂.step {z₂} π₃ H₃
  have hStage : StageCentres (fun P C => C ⊆ singularSet (n := 3)
      (strictTransform 3 P.proj (embeddedCuspSet 7))) T₃ :=
    ⟨⟨⟨trivial,hS₁⟩,hS₂⟩,hS₃⟩
  have hPoint : StageCentres (fun _ C => DimLE (n := 3) C 0) T₃ :=
    ⟨⟨⟨trivial,dimLE_centre_of_centred_chart e (chart_mem_atlas _ _) hStart hZero⟩,
      dimLE_centre_of_centred_chart e₁ ha₁ hs₁ hz₁⟩,
      dimLE_centre_of_centred_chart e₂ ha₂ hs₂ hz₂⟩
  have hTest := zero_dimensional_singular_centres_is_original_test
    (X := CuspAmbient) (embeddedCuspSet 7) (embedded_cusp_isAnalytic 7) [] isSNCDivisor_nil
    T₃ hStage hPoint
  let W : Set CuspAmbient := embeddedCuspSet 7
  have hEq₁ : strictTransform 3 T₁.proj W = strictTransform 3 π₁ W := rfl
  have hEq₂ : strictTransform 3 T₂.proj W = strictTransform 3 π₂ (strictTransform 3 T₁.proj W) :=
    StrictTransformComposition.strictTransform_comp T₁.contMDiff_proj H₂.contMDiff W
  have hEq₃ : strictTransform 3 T₃.proj W = strictTransform 3 π₃ (strictTransform 3 T₂.proj W) :=
    StrictTransformComposition.strictTransform_comp T₂.contMDiff_proj H₃.contMDiff W
  have hWClosed : IsClosed W := (embedded_cusp_isAnalytic 7).isClosed
  have hRead₀ : ∀ u ∈ e.source, u ∈ W ↔ e u ∈ embeddedCuspSet 7 := by
    intro u _
    rw [he]
    rfl
  have hF₁ : strictTransform 3 π₁ W ∩ π₁ ⁻¹' ({0} : Set CuspAmbient) = {z₁} := by
    apply (hUnique H₁ 7 (by decide) e (chart_mem_atlas _ _) hStart hZero hRead₀).eq_singleton_of_mem
    exact ⟨hEq₁ ▸ (hR₁ z₁ hs₁).mpr (hz₁.symm ▸ zero_mem_cusp 5 (by decide)),he₁⟩
  have hF₂ : strictTransform 3 π₂ (strictTransform 3 T₁.proj W) ∩ π₂ ⁻¹' ({z₁} : Set Y₁) = {z₂} := by
    apply (hUnique H₂ 5 (by decide) e₁ ha₁ hs₁ hz₁ hR₁).eq_singleton_of_mem
    exact ⟨hEq₂ ▸ (hR₂ z₂ hs₂).mpr (hz₂.symm ▸ zero_mem_cusp 3 (by decide)),he₂⟩
  have hF₃ : strictTransform 3 π₃ (strictTransform 3 T₂.proj W) ∩ π₃ ⁻¹' ({z₂} : Set Y₂) = {z₃} := by
    apply (hUnique H₃ 3 (by decide) e₂ ha₂ hs₂ hz₂ hR₂).eq_singleton_of_mem
    exact ⟨hEq₃ ▸ (hR₃ z₃ hs₃).mpr (hz₃.symm ▸ zero_mem_cusp 1 (by decide)),he₃⟩
  have hReg₁ : ∀ u ∈ strictTransform 3 T₁.proj W, u ≠ z₁ →
      RegularAtDim (n := 3) (strictTransform 3 T₁.proj W) u 1 := by
    rw [hEq₁]
    exact cusp_step_regular_away H₁ hWClosed
      (fun _ hu => regularAtDim_embedded_cusp_off_zero hu) e₁ ha₁ hs₁ hz₁ hF₁ 5 hR₁
  have hReg₂ : ∀ u ∈ strictTransform 3 T₂.proj W, u ≠ z₂ →
      RegularAtDim (n := 3) (strictTransform 3 T₂.proj W) u 1 := by
    rw [hEq₂]
    exact cusp_step_regular_away H₂ isClosed_closure hReg₁ e₂ ha₂ hs₂ hz₂ hF₂ 3
      (fun u hu => hEq₂ ▸ hR₂ u hu)
  have hSmooth : IsClosedSubmanifold 3 (strictTransform 3 T₃.proj W) := by
    rw [hEq₃]
    exact cusp_last_step_smooth H₃ isClosed_closure hReg₂ e₃ ha₃ hs₃ hz₃ hF₃
      (fun u hu => hEq₃ ▸ hR₃ u hu)
  refine ⟨Y₃,T₃,rfl,hSmooth,hTest,hStage,?_,e₃,z₃,ha₃,hs₃,hz₃,?_,hR₃⟩
  · intro i hi
    interval_cases i <;> simp [T₃,T₂,T₁,T₀,slotFootprint,BlowupTower.proj_step,he₁,he₂]
  · simp [T₃,T₂,T₁,T₀,BlowupTower.proj_step,he₁,he₂,he₃]

end Hironaka.HironakaG8CuspPointTowerEndpoint
