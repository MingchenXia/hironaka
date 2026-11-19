import Hironaka.Resolution.HironakaG3ResidualOverlapBoundary
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualFullOverlapBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals MaxLocusLocal
  HironakaOriginalTerminalOverlapComparison HironakaG3ResidualOverlapBoundary
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)

/-- Complete residual windows, followed by the same containing-label list,
have equal ordered nonempty original boundary traces on the overlap. -/
theorem residual_full_overlap_marked_boundary {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (D : ι → Set X) (S R₁ R₂ : Finset ι)
    (hD₁ : Disjoint S R₁) (hD₂ : Disjoint S R₂) (U₁ U₂ : Opens X)
    (hVis₁ : ∀ i, i ∉ S → (D i ∩ (U₁ : Set X)).Nonempty → i ∈ R₁)
    (hVis₂ : ∀ i, i ∉ S → (D i ∩ (U₂ : Set X)).Nonempty → i ∈ R₂)
    (J : GermIdeal n X) :
    let M₁ : MarkedIdeal n X := ⟨univ,(R₁.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D,J,1⟩
    let M₂ : MarkedIdeal n X := ⟨univ,(R₂.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D,J,1⟩
    let Φ := overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
    ((pullback (Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁)
      (pullback (Subtype.val : U₁ → X) M₁)).E).filter (fun H => decide H.Nonempty) =
    (((pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂)
      (pullback (Subtype.val : U₂ → X) M₂)).E).map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  have hR := residual_overlap_marked_boundary D S R₁ R₂ hD₁ hD₂ U₁ U₂ hVis₁ hVis₂ J
  simp only [pullback,List.map_append,List.map_map,Function.comp_def,List.filter_append] at hR ⊢
  rw [hR]
  congr 1
end
end Hironaka.HironakaG3ResidualFullOverlapBoundary
