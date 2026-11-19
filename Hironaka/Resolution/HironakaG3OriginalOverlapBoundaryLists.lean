import Hironaka.Resolution.HironakaG3StoppedAmbientFullBoundary
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG3OriginalOverlapBoundaryLists
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsoTail MaxLocusLocal HironakaOriginalTerminalOverlapComparison

theorem original_overlap_boundary_lists {n : ℕ} {X : CMfd.{u} n} (U₁ U₂ : Opens X)
    (E : List (Set X)) :
    (E.map ((fun p : nestedOpens U₁ (U₁ ⊓ U₂) => (p.val : U₁).val) ⁻¹' ·)) =
      (E.map ((fun p : nestedOpens U₂ (U₁ ⊓ U₂) => (p.val : U₂).val) ⁻¹' ·)).map
        (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right ⁻¹' ·) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro H hH
  ext p
  rfl

theorem original_overlap_boundary_closed {n : ℕ} {X : CMfd.{u} n} (U₁ U₂ : Opens X)
    (E : List (Set X)) (hE : ∀ H ∈ E, IsClosed H) :
    ∀ H ∈ E.map ((fun p : nestedOpens U₂ (U₁ ⊓ U₂) => (p.val : U₂).val) ⁻¹' ·), IsClosed H := by
  intro H hH
  obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
  exact (hE K hK).preimage (continuous_subtype_val.comp continuous_subtype_val)
end
end Hironaka.HironakaG3OriginalOverlapBoundaryLists
