import Hironaka.Resolution.HironakaG3DifferentBoundaryStoppingOpens
import Hironaka.Resolution.HironakaG3ResidualWindowTraces
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualStoppingOpens
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers MaxLocusLocal HironakaG3RBoundaryEmbedded
  HironakaOriginalTerminalOverlapComparison HironakaOriginalBoundaryEmptyBaseComparison
  HironakaG3ResidualWindowTraces HironakaG3DifferentBoundaryStoppingOpens

/-- Complete residual windows have the same stopping open on their actual overlap. -/
theorem residual_overlap_stopping_opens {n : ℕ} {X : CMfd.{0} n} {ι : Type*} [LinearOrder ι]
    (V : Set X) (hV : IsClosed V) (d : ℕ) (D : ι → Set X) (hD : ∀ i, IsClosed (D i))
    (S R₁ R₂ : Finset ι) (hD₁ : Disjoint S R₁) (hD₂ : Disjoint S R₂) (U₁ U₂ : Opens X)
    (hVis₁ : ∀ i, i ∉ S → (D i ∩ (U₁ : Set X)).Nonempty → i ∈ R₁)
    (hVis₂ : ∀ i, i ∉ S → (D i ∩ (U₂ : Set X)).Nonempty → i ∈ R₂) :
    nestedOpens (nestedOpens U₁ (U₁ ⊓ U₂))
        (nestedOpens U₁ (bdryOpen V d ((R₁.sort (· ≤ ·)).map D))) =
      baseOpen (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂))
          (nestedOpens U₂ (bdryOpen V d ((R₂.sort (· ≤ ·)).map D)))) := by
  let W := U₁ ⊓ U₂
  let F (i : ι) : Set W := (Subtype.val : W → X) ⁻¹' D i
  have hs₁ : ∀ i, i ∉ S → (F i).Nonempty → i ∈ R₁ := by
    intro i hi ⟨q,hq⟩
    exact hVis₁ i hi ⟨q.val,hq,q.property.1⟩
  have hs₂ : ∀ i, i ∉ S → (F i).Nonempty → i ∈ R₂ := by
    intro i hi ⟨q,hq⟩
    exact hVis₂ i hi ⟨q.val,hq,q.property.2⟩
  have hfilter := residual_window_traces_agree F S R₁ R₂ hD₁ hD₂ hs₁ hs₂
  have hfilter' : (((R₁.sort (· ≤ ·)).map D).map ((Subtype.val : W → X) ⁻¹' ·)).filter
      (fun H => decide H.Nonempty) =
      (((R₂.sort (· ≤ ·)).map D).map ((Subtype.val : W → X) ⁻¹' ·)).filter
      (fun H => decide H.Nonempty) := by
    simpa [F,List.map_map,Function.comp_def] using hfilter
  apply overlap_stopping_opens_eq_of_nonempty_traces V hV d _ _ ?_ ?_ U₁ U₂ hfilter'
  · intro H hH
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    exact hD i
  · intro H hH
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    exact hD i
end
end Hironaka.HironakaG3ResidualStoppingOpens
