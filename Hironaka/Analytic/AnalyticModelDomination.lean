import Hironaka.Analytic.AnalyticModificationComposition

/-! Actual holomorphic domination between original smooth proper models.
The complete mathematical route is analytic-model-domination.tex in this
work packet. No common model, inverse or exceptional certificate is input.
No source coverage or production acceptance is claimed by this work file. -/

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AnalyticModelDomination

open Hironaka.BlowupSequences AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- A genuine original modification pulls every thin set back to a thin set. -/
theorem interior_preimage_eq_empty_of_isAnalyticModification {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) {A : Set X}
    (hA : interior A = ∅) : interior (π ⁻¹' A) = ∅ := by
  obtain ⟨E, _hEc, _hEa, hEi, _hinj, hnon⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hπ
  have hsub : exceptionalLocus n π ⊆ E := by
    intro y hy
    by_contra hyE
    exact hnon y hyE hy
  have hthin : interior (exceptionalLocus n π) = ∅ :=
    subset_empty_iff.mp ((interior_mono hsub).trans hEi.subset)
  exact BlowupSequenceTotalTransform.interior_preimage_eq_empty hπ.1 hthin hA

/-- An actual holomorphic map over the same original space between two genuine
proper analytic models internally acquires the full modification dictionary. -/
theorem isAnalyticModification_of_holomorphic_over
    {πY : Y → X} {πZ : Z → X} {g : Z → Y}
    (hY : IsAnalyticModification (n := n) πY)
    (hZ : IsAnalyticModification (n := n) πZ)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hover : πY ∘ g = πZ) : IsAnalyticModification (n := n) g := by
  obtain ⟨AY, BY, sY, _hAYc, _hAYa, _hAYi, hBYc, hBYa, hBYi,
    hpreY, _hsY, _hrightY, hleftY⟩ := hY.2.2
  obtain ⟨AZ, BZ, sZ, _hAZc, _hAZa, _hAZi, hBZc, hBZa, hBZi,
    hpreZ, hsZ, hrightZ, hleftZ⟩ := hZ.2.2
  let D : Set X := BY ∪ BZ
  let E : Set Y := πY ⁻¹' D
  let F : Set Z := πZ ⁻¹' D
  have hDc : IsClosed D := hBYc.union hBZc
  have hDa : IsComplexAnalyticSubset (n := n) D :=
    ConstantRankImage.IsComplexAnalyticSubset.union hBYa hBZa
  have hDi : interior D = ∅ := by
    change interior (BY ∪ BZ) = ∅
    rw [interior_union_isClosed_of_interior_empty hBYc hBZi]
    exact hBYi
  have hEc : IsClosed E := hDc.preimage hY.1.continuous
  have hFc : IsClosed F := hDc.preimage hZ.1.continuous
  have hEa : IsComplexAnalyticSubset (n := n) E :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hY.1 hDa
  have hFa : IsComplexAnalyticSubset (n := n) F :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hZ.1 hDa
  have hEi : interior E = ∅ :=
    interior_preimage_eq_empty_of_isAnalyticModification hY hDi
  have hFi : interior F = ∅ :=
    interior_preimage_eq_empty_of_isAnalyticModification hZ hDi
  have hpre : g ⁻¹' E = F := by
    change (πY ∘ g) ⁻¹' D = πZ ⁻¹' D
    rw [hover]
  have hproper : IsProperMap g :=
    isProperMap_of_comp_of_t2 hg.continuous hY.1.continuous (hover.symm ▸ hZ.2.1)
  have hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (sZ ∘ πY) Eᶜ := by
    apply hsZ.comp hY.1.contMDiffOn
    intro y hy
    exact fun h => hy (Or.inr h)
  refine ⟨hg, hproper, F, E, sZ ∘ πY, hFc, hFa, hFi, hEc, hEa, hEi,
    hpre, hs, ?_, ?_⟩
  · intro y hy
    have hyBY : πY y ∉ BY := fun h => hy (Or.inl h)
    have hyBZ : πY y ∉ BZ := fun h => hy (Or.inr h)
    have heq : πY (g (sZ (πY y))) = πY y := by
      rw [show πY (g (sZ (πY y))) = πZ (sZ (πY y)) from
        congrFun hover (sZ (πY y))]
      exact hrightZ (πY y) hyBZ
    have hyAY : y ∉ AY := by
      rw [← hpreY]
      exact hyBY
    have hgyAY : g (sZ (πY y)) ∉ AY := by
      rw [← hpreY]
      change πY (g (sZ (πY y))) ∉ BY
      rwa [heq]
    exact (hleftY _ hgyAY).symm.trans ((congrArg sY heq).trans (hleftY y hyAY))
  · intro z hz
    change sZ (πY (g z)) = z
    rw [show πY (g z) = πZ z from congrFun hover z]
    apply hleftZ
    rw [← hpreZ]
    exact fun h => hz (Or.inr h)

end Hironaka.AnalyticModelDomination
