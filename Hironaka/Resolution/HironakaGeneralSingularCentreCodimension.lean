import Hironaka.Resolution.HironakaEmbeddedAnalytic
import Hironaka.Resolution.HironakaDimensionGlobalComponents
import Hironaka.Resolution.HironakaDimensionThreeStepOneCurveEnvelope
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels

/-!
# Normal codimension of an intrinsic singular centre

The target is an arbitrary reduced analytic subset, including mixed dimensions
and ambient-dimensional components. Blueprint:
`hironaka-general-singular-centre-codimension-20261101.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaGeneralSingularCentreCodimension

noncomputable section

open AnalyticDimensionBasics HironakaEmbeddedDimensionParts
  HironakaEmbeddedAnalytic HironakaDimensionGlobalComponents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The same actual ambient-dimensional part is the clopen interior. -/
theorem dimensionPart_top_eq_interior {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    dimensionPart (n := n) W n = interior W := by
  have hr : regularLocus (n := n) W n = interior W := by
    ext x
    constructor
    · intro hx
      exact mem_interior_iff_mem_nhds.mpr
        (EmbeddedFromResolution.mem_nhds_of_regularAtDim_self hx)
    · intro hx
      exact EmbeddedFromResolution.regularAtDim_of_mem_nhds
        (mem_interior_iff_mem_nhds.mp hx)
  unfold dimensionPart
  rw [hr, hW.isClosed_interior.closure_eq]

private def lowerParts (W : Set M) : Set M :=
  ⋃ j : Fin (n - 1), dimensionPart (n := n) W j.val

private theorem analytic_lower_parts_dim {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (lowerParts (n := n) W) ∧
      DimLE (n := n) (lowerParts (n := n) W) (n - 2) := by
  have h := HironakaDimensionThreeStepOneCurveEnvelope.analytic_dimLE_finset_union
    (Finset.univ : Finset (Fin (n - 1)))
    (fun j => dimensionPart (n := n) W j.val) (d := n - 2)
    (fun j _ => isComplexAnalyticSubset_dimensionPart hW j.val)
    (fun j _ y k hy => by
      have hk := isPureDim_dimensionPart hW j.val y k hy
      have hj := j.isLt
      omega)
  simpa [lowerParts] using h

/-- The finite covering is derived from the SAME target, with no purity input. -/
private theorem intrinsic_singular_subset_cover {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (hn : 0 < n) :
    singularSet (n := n) W ⊆ lowerParts (n := n) W ∪
      (dimensionPart (n := n) W (n - 1) \
        regularLocus (n := n) (dimensionPart (n := n) W (n - 1)) (n - 1)) := by
  intro x hx
  by_cases hxlow : x ∈ lowerParts (n := n) W
  · exact Or.inl hxlow
  have hxsing := mem_singularSet_iff.mp hx
  have hxint : x ∉ interior W := fun h => hxsing.2 n
    (EmbeddedFromResolution.regularAtDim_of_mem_nhds
      (mem_interior_iff_mem_nhds.mp h))
  have hclosed : IsClosed (lowerParts (n := n) W) :=
    (analytic_lower_parts_dim hW).1.isClosed
  let U : Set M := (interior W ∪ lowerParts (n := n) W)ᶜ
  have hU : IsOpen U := (hW.isClosed_interior.union hclosed).isOpen_compl
  have hxU : x ∈ U := by
    rintro (h | h)
    · exact hxint h
    · exact hxlow h
  have heq : W ∩ U = dimensionPart (n := n) W (n - 1) ∩ U := by
    ext y
    constructor
    · rintro ⟨hyW, hyU⟩
      obtain ⟨j, hyj⟩ := mem_iUnion.mp ((eq_iUnion_dimensionPart hW) ▸ hyW)
      have hjlow : ¬ j.val < n - 1 := by
        intro hj
        exact hyU (Or.inr (mem_iUnion.mpr ⟨⟨j.val, hj⟩, hyj⟩))
      have hjtop : j.val ≠ n := by
        intro hj
        rw [hj, dimensionPart_top_eq_interior hW] at hyj
        exact hyU (Or.inl hyj)
      have hj : j.val = n - 1 := by have := j.isLt; omega
      exact ⟨hj ▸ hyj, hyU⟩
    · rintro ⟨hyA, hyU⟩
      exact ⟨dimensionPart_subset hW.isClosed (n - 1) hyA, hyU⟩
  have hxA : x ∈ dimensionPart (n := n) W (n - 1) := by
    have hh : x ∈ W ∩ U := ⟨hxsing.1, hxU⟩
    rw [heq] at hh
    exact hh.1
  refine Or.inr ⟨hxA, fun hreg => ?_⟩
  exact hxsing.2 (n - 1)
    (RegularPointDimension.regularAtDim_of_inter_eq hU hxU heq.symm hreg)

private theorem analytic_singular_cover_dim {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (lowerParts (n := n) W ∪
      (dimensionPart (n := n) W (n - 1) \
        regularLocus (n := n) (dimensionPart (n := n) W (n - 1)) (n - 1))) ∧
    DimLE (n := n) (lowerParts (n := n) W ∪
      (dimensionPart (n := n) W (n - 1) \
        regularLocus (n := n) (dimensionPart (n := n) W (n - 1)) (n - 1))) (n - 2) := by
  have hL := analytic_lower_parts_dim hW
  have hA := isComplexAnalyticSubset_dimensionPart hW (n - 1)
  have hp := isPureDim_dimensionPart hW (n - 1)
  apply HironakaDimensionThreeStepOneCurveEnvelope.analytic_dimLE_union hL.1 hL.2
    (PureSingularLocus.isComplexAnalyticSubset_diff_regularLocus hA hp)
  intro y k hy
  have hk := PureSingularLocus.dimLE_diff_regularLocus hA hp y k hy
  omega

/-- Every regular piece of the SAME actual intrinsic singular centre has
normal codimension at least two, for arbitrary mixed-dimensional target. -/
theorem regular_intrinsic_singular_centre_add_two_le {W C : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W)
    (hCS : C ⊆ singularSet (n := n) W)
    {x : M} {d : ℕ} (hreg : RegularAtDim (n := n) C x d) : d + 2 ≤ n := by
  have hxS := mem_singularSet_iff.mp (hCS hreg.2.1)
  by_cases hn0 : n = 0
  · subst n
    have hdim : DimLE (n := 0) W 0 := fun y k hy => hy.1
    exact False.elim (hxS.2 0
      (HironakaOneDimensionalCanonicalSuperlevels.regularAtDim_zero_of_analytic_dimLE_zero
        hW hdim hxS.1))
  by_cases hn1 : n = 1
  · subst n
    have hcover := intrinsic_singular_subset_cover hW (by decide) (hCS hreg.2.1)
    rcases hcover with hlow | ⟨hxA, hnot⟩
    · simp [lowerParts] at hlow
    · exact False.elim (hnot
        (HironakaOneDimensionalCanonicalSuperlevels.regularAtDim_zero_of_analytic_dimLE_zero
          (isComplexAnalyticSubset_dimensionPart hW 0)
          (isPureDim_dimensionPart hW 0).dimLE hxA))
  have hn : 2 ≤ n := by omega
  obtain ⟨hcover, hdim⟩ := analytic_singular_cover_dim hW
  have hC := DimensionMonotone.DimLE.anti hcover
    (hCS.trans (intrinsic_singular_subset_cover hW (by omega))) hdim
  have hd := hC x d hreg
  omega

/-- The normal count for the SAME centre chart; no target purity or
positive target dimension is assumed. -/
theorem normal_codimension_two_of_intrinsic_singular_centre {d t : ℕ}
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (d + t)) X]
    [IsComplexManifold (d + t) X] {W C : Set X}
    (hW : IsComplexAnalyticSubset (n := d + t) W)
    (hCS : C ⊆ singularSet (n := d + t) W)
    {x : X} (hreg : RegularAtDim (n := d + t) C x d) : 2 ≤ t := by
  have h := regular_intrinsic_singular_centre_add_two_le hW hCS hreg
  omega

end
end Hironaka.HironakaGeneralSingularCentreCodimension
