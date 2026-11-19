import Hironaka.Resolution.HironakaG8CuspPointTower
import Hironaka.Invariant.CodimOnePartCanonical

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CuspChartGlobalRegularity

open Hironaka.BlowupSequences BlowupTowers HironakaEmbeddedAnalytic
  HironakaG8StrictTransformAtlasSquare HironakaBaseChange HironakaStageCenters
  CodimOnePartCanonical

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Regular dimensions transfer in both directions on an actual atlas chart. -/
theorem regularAtDim_atlas_chart
    (e : OpenPartialHomeomorph Y (ComplexModel n)) (he : e ∈ atlas (ComplexModel n) Y)
    {y : Y} (hy : y ∈ e.source) (W : Set Y) (A : Set (ComplexModel n))
    (hA : ∀ z ∈ e.source, z ∈ W ↔ e z ∈ A) (d : ℕ) :
    RegularAtDim (n := n) W y d ↔ RegularAtDim (n := n) A (e y) d := by
  let U : Opens Y := ⟨e.source,e.open_source⟩
  obtain ⟨V,Φ,hΦ⟩ := atlas_open_holo_embedding e he
  let z : U := ⟨y,hy⟩
  have hEq : (Subtype.val : U → Y) ⁻¹' W = Φ ⁻¹' ((Subtype.val : V → ComplexModel n) ⁻¹' A) :=
    Set.ext fun u => (hA u.val u.property).trans ((congrArg (· ∈ A) (hΦ u)).to_iff)
  rw [show e y = (Φ z).val from hΦ z]
  calc
    RegularAtDim (n := n) W y d ↔
        RegularAtDim (n := n) ((Subtype.val : U → Y) ⁻¹' W) z d :=
      (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U) (x := z)).symm
    _ ↔ RegularAtDim (n := n) ((Subtype.val : V → ComplexModel n) ⁻¹' A) (Φ z) d := by
      rw [hEq]
      exact regularAtDim_preimage_iff Φ
    _ ↔ _ := AnalyticSubsetOpens.regularAtDim_preimage_val_iff

/-- If all strict points on the exceptional fibre lie on one specified
chart, ordinary regularity off the centre and the chart calculation
control the whole strict transform. -/
theorem strictTransform_regular_outside_chart_exception
    {C W : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    (d : ℕ) (hAway : ∀ x ∈ W, x ∉ C → RegularAtDim (n := n) W x d)
    (e : OpenPartialHomeomorph Y (ComplexModel n)) (he : e ∈ atlas (ComplexModel n) Y)
    (A B : Set (ComplexModel n))
    (hA : ∀ y ∈ e.source, y ∈ strictTransform n π W ↔ e y ∈ A)
    (hCover : strictTransform n π W ∩ π ⁻¹' C ⊆ e.source)
    (hModel : ∀ z ∈ A, z ∉ B → RegularAtDim (n := n) A z d) :
    ∀ y ∈ strictTransform n π W, y ∉ e.source ∩ e ⁻¹' B →
      RegularAtDim (n := n) (strictTransform n π W) y d := by
  intro y hy hBad
  by_cases hC : π y ∈ C
  · have heY := hCover ⟨hy,hC⟩
    have hB : e y ∉ B := fun h => hBad ⟨heY,h⟩
    exact (regularAtDim_atlas_chart e he heY _ _ hA d).mpr (hModel _ ((hA y heY).mp hy) hB)
  · have hyE : y ∉ exceptionalLocus n π :=
      fun h => hC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
    have hyW : π y ∈ W :=
      (HironakaAdmissibleCalculus.mem_strictTransform_iff_of_notMem hπ.contMDiff.continuous hW hyE).mp hy
    exact (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus hπ.contMDiff hW hyE d).mpr
      (hAway _ hyW hC)

end Hironaka.HironakaG8CuspChartGlobalRegularity
