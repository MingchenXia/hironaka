import Hironaka.Resolution.HironakaG3IndexedResidualHeadNonerasure
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedContainedOriginalGood
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3IndexedResidualFixedHeadClass
  HironakaG3IndexedResidualHeadNonerasure

/-- If an indexed boundary member contains the target, the G3 original
boundary-relative bad support is exactly the target. -/
theorem indexed_original_bad_eq_target_of_containment {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} (C : Set X) (D : ι → Set X) (r : ℕ)
    (hContained : ∃ i, C ⊆ D i) :
    C \ regularLocus (n := n) C r ∪ C ∩ (⋃ i, D i) = C := by
  obtain ⟨i,hi⟩ := hContained
  ext x
  constructor
  · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx
  · intro hx
    exact Or.inr ⟨hx,mem_iUnion.mpr ⟨i,hi hx⟩⟩

/-- Positive containing-label count forces that same exact bad-support identity. -/
theorem indexed_original_bad_eq_target_of_positive_containing_count {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} (C : Set X) (D : ι → Set X) (hC : C.Nonempty) (hD : LocallyFinite D)
    (r : ℕ) (hpos : 0 < (containingLabels C D hC hD).card) :
    C \ regularLocus (n := n) C r ∪ C ∩ (⋃ i, D i) = C := by
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hpos
  exact indexed_original_bad_eq_target_of_containment C D r ⟨i,(mem_containingLabels C D hC hD i).mp hi⟩

/-- The same glued residual-head map is an isomorphism on the exact G3
original indexed boundary-relative good locus in the positive-contact case. -/
theorem glued_indexed_residual_head_isomorphism_original_good {d t : ℕ} (ht : 0 < t)
    {X Z : CMfd.{0} (d+t)} {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    (hS : (containingLabels C D hC.nonempty hD.1).card = t) (r : ℕ)
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d)
    {P : Z → X} (h : IsGluedFrom (residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
      (containingLabels C D hC.nonempty hD.1)) Z P) :
    IsIsomorphismOver (d+t) P (C \ regularLocus (n := d+t) C r ∪ C ∩ ⋃ i, D i)ᶜ := by
  have hpos : 0 < (containingLabels C D hC.nonempty hD.1).card := by rw [hS]; exact ht
  rw [indexed_original_bad_eq_target_of_positive_containing_count C D hC.nonempty hD.1 r hpos]
  exact glued_indexed_residual_head_isomorphism_off_target _ hNc hN C hC.analytic r D _ h
end
end Hironaka.HironakaG3IndexedContainedOriginalGood
