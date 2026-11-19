import Hironaka.Analytic.AnalyticModificationLocalDiscrepancy
import Hironaka.Blowup.BlowupSequenceTotalTransform
import Hironaka.Analytic.ProperMappingTheorem
import Hironaka.Analytic.AnalyticSubsetPreimage

set_option autoImplicit false

/-! # Actual global analytic modifications compose over their original space -/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AnalyticModificationComposition

open Hironaka.BlowupSequences AnalyticModificationLocalDiscrepancy
  ConstantRankImage

noncomputable section

variable {n : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

private theorem interior_exceptional_eq_empty {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) :
    interior (exceptionalLocus n π) = ∅ := by
  obtain ⟨A, _hAc, _hAa, hAi, _hinj, hnon⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hπ
  have hsub : exceptionalLocus n π ⊆ A := by
    intro y hy
    by_contra hyA
    exact hnon y hyA hy
  exact subset_empty_iff.mp ((interior_mono hsub).trans hAi.subset)

private theorem interior_image_eq_empty {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) {D : Set Y} (hDi : interior D = ∅) :
    interior (π '' D) = ∅ := by
  obtain ⟨A, B, s, hAc, _hAa, _hAi, _hBc, _hBa, hBi, hpre, _hs, hright, hleft⟩ :=
    hπ.2.2
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hnot : ¬ interior (π '' D) ⊆ B := by
    intro hsub
    have hxB := interior_maximal hsub isOpen_interior hx
    rw [hBi] at hxB
    exact hxB
  obtain ⟨x₀, hx₀, hx₀B⟩ := not_subset.mp hnot
  have hsy : s x₀ ∉ A := by
    rw [← hpre]
    change π (s x₀) ∉ B
    rw [hright x₀ hx₀B]
    exact hx₀B
  let W := π ⁻¹' interior (π '' D) ∩ Aᶜ
  have hW : IsOpen W := (isOpen_interior.preimage hπ.1.continuous).inter hAc.isOpen_compl
  have hyW : s x₀ ∈ W := by
    refine ⟨?_, hsy⟩
    change π (s x₀) ∈ interior (π '' D)
    rwa [hright x₀ hx₀B]
  have hsub : W ⊆ D := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := interior_subset hz.1
    have hzB : π z ∉ B := by
      intro hzB
      exact hz.2 (by simpa only [← hpre, mem_preimage] using hzB)
    have hwA : w ∉ A := by
      rw [← hpre]
      change π w ∉ B
      rwa [hwz]
    have hwz' : w = z :=
      (hleft w hwA).symm.trans ((congrArg s hwz).trans (hleft z hz.2))
    exact hwz' ▸ hw
  have hyD := interior_maximal hsub hW hyW
  rw [hDi] at hyD
  exact hyD

/-- The actual proper, analytic and inverse data compose over the whole original space. -/
theorem isAnalyticModification_comp {π : Y → X} {σ : Z → Y}
    (hπ : IsAnalyticModification (n := n) π)
    (hσ : IsAnalyticModification (n := n) σ) :
    IsAnalyticModification (n := n) (π ∘ σ) := by
  obtain ⟨A, B, s, hAc, hAa, hAi, hBc, hBa, hBi, hpreπ, hs, hrightπ, hleftπ⟩ := hπ.2.2
  obtain ⟨C, D, t, hCc, hCa, hCi, hDc, hDa, hDi, hpreσ, ht, hrightσ, hleftσ⟩ := hσ.2.2
  let A' := σ ⁻¹' A ∪ C
  let B' := B ∪ π '' D
  have hA'c : IsClosed A' := (hAc.preimage hσ.1.continuous).union hCc
  have hA'a : IsComplexAnalyticSubset (n := n) A' :=
    ConstantRankImage.IsComplexAnalyticSubset.union
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hσ.1 hAa) hCa
  have hprei : interior (σ ⁻¹' A) = ∅ :=
    BlowupSequenceTotalTransform.interior_preimage_eq_empty hσ.1
      (interior_exceptional_eq_empty hσ) hAi
  have hA'i : interior A' = ∅ := by
    change interior (σ ⁻¹' A ∪ C) = ∅
    rw [interior_union_isClosed_of_interior_empty (hAc.preimage hσ.1.continuous) hCi]
    exact hprei
  have himgc : IsClosed (π '' D) := hπ.2.1.isClosedMap D hDc
  have himga : IsComplexAnalyticSubset (n := n) (π '' D) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hπ.1 hDa fun K hK =>
      (hπ.2.1.isCompact_preimage hK).inter_left hDc
  have hB'c : IsClosed B' := hBc.union himgc
  have hB'a : IsComplexAnalyticSubset (n := n) B' :=
    ConstantRankImage.IsComplexAnalyticSubset.union hBa himga
  have hB'i : interior B' = ∅ := by
    change interior (B ∪ π '' D) = ∅
    rw [interior_union_isClosed_of_interior_empty hBc (interior_image_eq_empty hπ hDi)]
    exact hBi
  have hpre : (π ∘ σ) ⁻¹' B' = A' := by
    ext z
    constructor
    · intro hz
      rcases hz with hzB | hzD
      · exact Or.inl (by simpa only [← hpreπ, mem_preimage, Function.comp_apply] using hzB)
      · by_cases hzA : σ z ∈ A
        · exact Or.inl hzA
        · obtain ⟨w, hw, hwz⟩ := hzD
          have hzB : π (σ z) ∉ B := by
            intro h
            exact hzA (by simpa only [← hpreπ, mem_preimage] using h)
          have hwA : w ∉ A := by
            rw [← hpreπ]
            change π w ∉ B
            rwa [hwz]
          have hwz' : w = σ z :=
            (hleftπ w hwA).symm.trans ((congrArg s hwz).trans (hleftπ (σ z) hzA))
          exact Or.inr (by simpa only [← hpreσ, mem_preimage] using hwz' ▸ hw)
    · rintro (hzA | hzC)
      · exact Or.inl (by simpa only [← hpreπ, mem_preimage, Function.comp_apply] using hzA)
      · exact Or.inr ⟨σ z, by simpa only [← hpreσ, mem_preimage] using hzC, rfl⟩
  have hsmap : MapsTo s B'ᶜ Dᶜ := by
    intro x hx
    have hxB : x ∉ B := fun h => hx (Or.inl h)
    intro hsD
    exact hx (Or.inr ⟨s x, hsD, hrightπ x hxB⟩)
  have hs' : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (t ∘ s) B'ᶜ :=
    ht.comp (hs.mono fun _ hx h => hx (Or.inl h)) hsmap
  refine ⟨hπ.1.comp hσ.1, hπ.2.1.comp hσ.2.1, A', B', t ∘ s,
    hA'c, hA'a, hA'i, hB'c, hB'a, hB'i, hpre, hs', ?_, ?_⟩
  · intro x hx
    have hxB : x ∉ B := fun h => hx (Or.inl h)
    have hsD := hsmap hx
    change π (σ (t (s x))) = x
    rw [hrightσ (s x) hsD, hrightπ x hxB]
  · intro z hz
    have hzA : σ z ∉ A := fun h => hz (Or.inl h)
    have hzC : z ∉ C := fun h => hz (Or.inr h)
    change t (s (π (σ z))) = z
    rw [hleftπ (σ z) hzA, hleftσ z hzC]

end
end Hironaka.AnalyticModificationComposition
