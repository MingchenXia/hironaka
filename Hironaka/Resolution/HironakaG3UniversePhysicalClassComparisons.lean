import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaG3RTowerClass
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniversePhysicalClassComparisons
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaG3RTowerClass
  G3UniverseEmptyAwareCore HironakaOriginalTerminalOverlapComparison MaxLocusLocal

def HasPhysicalComparisons {n : ℕ} {X : CMfd.{u} n} (K : LocalTowerClass X) : Prop :=
  ∀ (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{u} n)
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂),
    K U₁ Y₁ T₁ → K U₂ Y₂ T₂ →
    ∃ β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β

/-- Forget the centre data of this particular physical overlap while
retaining its endpoint map and literal projections to the original base. -/
theorem physical_overlap_proj_comm {n : ℕ} {X : CMfd.{u} n}
    (U₁ U₂ : Opens X) {Y₁ Y₂ : CMfd.{u} n}
    {T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁} {T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂}
    {β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂)))}
    (hβ : EmptyAwareTowerIso (overlapBaseEquiv (n := n)
      (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
      (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁)
      (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β) :
    ∀ y, ((T₂.proj (β y).val : U₂) : X) = ((T₁.proj y.val : U₁) : X) := by
  intro y
  have hz := congrArg (fun q : nestedOpens U₂ (U₁ ⊓ U₂) => q.val.val) (emptyAware_proj_comm hβ y)
  rw [overlapBaseEquiv_point] at hz
  have htproj := congrArg (fun q : U₂ => q.val) (proj_restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂ (β y))
  have hsproj := congrArg (fun q : U₁ => q.val) (proj_restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁ y)
  exact htproj.symm.trans (hz.trans hsproj)

theorem physical_comparisons_to_comparisons {n : ℕ} {X : CMfd.{u} n} {K : LocalTowerClass X}
    (h : HasPhysicalComparisons K) : HasComparisons K := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  obtain ⟨β,hβ⟩ := h U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  exact ⟨β, physical_overlap_proj_comm U₁ U₂ hβ⟩
end
end Hironaka.G3UniversePhysicalClassComparisons
