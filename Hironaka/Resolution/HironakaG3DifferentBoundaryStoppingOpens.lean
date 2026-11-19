import Hironaka.Resolution.HironakaG3BoundaryStoppingOpenRestriction
import Hironaka.Resolution.HironakaG3StoppedDifferentBoundaries
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DifferentBoundaryStoppingOpens
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3RBoundaryEmbedded
  HironakaG3BoundaryStoppingOpenRestriction HironakaOriginalTerminalOverlapComparison
  HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RTowerClass MaxLocusLocal

/-- Nonempty original boundary traces determine the same literal stopping
open on two differently presented sides of an ambient overlap. -/
theorem overlap_stopping_opens_eq_of_nonempty_traces {n : ℕ} {X : CMfd.{0} n}
    (V : Set X) (hV : IsClosed V) (d : ℕ) (E₁ E₂ : List (Set X))
    (hE₁ : ∀ H ∈ E₁, IsClosed H) (hE₂ : ∀ H ∈ E₂, IsClosed H)
    (U₁ U₂ : Opens X)
    (hfilter : (E₁.map ((Subtype.val : (U₁ ⊓ U₂ : Opens X) → X) ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
      (E₂.map ((Subtype.val : (U₁ ⊓ U₂ : Opens X) → X) ⁻¹' ·)).filter (fun H => decide H.Nonempty)) :
    nestedOpens (nestedOpens U₁ (U₁ ⊓ U₂)) (nestedOpens U₁ (bdryOpen V d E₁)) =
      baseOpen (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ (bdryOpen V d E₂))) := by
  let W := U₁ ⊓ U₂
  let F := E₁.map ((Subtype.val : W → X) ⁻¹' ·)
  have h₁ := bdryOpen_restrict_of_nonempty_filter V hV d E₁ hE₁ W F rfl
  have h₂ := bdryOpen_restrict_of_nonempty_filter V hV d E₂ hE₂ W F hfilter
  have hsame : nestedOpens W (bdryOpen V d E₁) = nestedOpens W (bdryOpen V d E₂) := by
    apply Opens.ext
    exact h₁.symm.trans h₂
  apply Opens.ext
  ext x
  change ((x.val : U₁) : X) ∈ bdryOpen V d E₁ ↔ ((x.val : U₁) : X) ∈ bdryOpen V d E₂
  have hh := congrArg (fun O : Opens W => (⟨((x.val : U₁) : X),x.property⟩ : W) ∈ O) hsame
  exact iff_of_eq hh
end
end Hironaka.HironakaG3DifferentBoundaryStoppingOpens
