import Hironaka.Resolution.HironakaG3EmptyAwareFilteredBoundary
import Hironaka.Resolution.HironakaG3BoundaryRestrictInitialList
import Hironaka.Resolution.HironakaG3ResidualFullBoundaryTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BornBoundaryPhysicalOverlap
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MaxLocusLocal HironakaDisjointFiniteControlledHistory
  HironakaOriginalTerminalOverlapComparison HironakaG3EmptyAwareHistory HironakaG3EmptyAwareFilteredBoundary
  HironakaG3EmptyAwareFullBoundary HironakaG3EmptyAwareBornSlots HironakaG3BoundaryRestrictInitialList
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)

theorem born_boundary_physical_overlap {n : ℕ} {X : CMfd.{0} n} (U₁ U₂ : Opens X)
    {Y₁ Y₂ : CMfd.{0} n} (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))))
    (hβ : EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
      (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β) :
    ((bornAlong T₁).map ((Subtype.val : openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)) → Y₁) ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
    (((bornAlong T₂).map ((Subtype.val : openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂)) → Y₂) ⁻¹' ·)).filter (fun H => decide H.Nonempty)).map (β ⁻¹' ·) := by
  let J := vanishingIdeal (n := n) (∅ : Set X)
  let M₁ : MarkedIdeal n (CMfd.of (n := n) U₁) := fullMarked [] (GermIdeal.pullback (Subtype.val : U₁ → X) J)
  let M₂ : MarkedIdeal n (CMfd.of (n := n) U₂) := fullMarked [] (GermIdeal.pullback (Subtype.val : U₂ → X) J)
  let N₁ := pullback (Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁) M₁
  let N₂ := pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) M₂
  have hE : N₁.E.filter (fun H => decide H.Nonempty) =
      (N₂.E.map ((overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
    simp [N₁,N₂,M₁,M₂,pullback,fullMarked]
  have hclosed : ∀ H ∈ N₂.E, IsClosed H := by simp [N₂,M₂,pullback,fullMarked]
  have ht := full_boundary_transport_of_filtered_initial hβ N₁ N₂ hE hclosed
  have hN₁ : N₁.E = M₁.E.map ((Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁) ⁻¹' ·) := by rfl
  have hN₂ : N₂.E = M₂.E.map ((Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) ⁻¹' ·) := by rfl
  rw [boundary_restrict_of_initial_eq M₁ _ N₁ hN₁ T₁, boundary_restrict_of_initial_eq M₂ _ N₂ hN₂ T₂] at ht
  have hB₁ : (geoTransformAlong M₁ T₁).E = bornAlong T₁ := by rw [boundary_decomp]; rfl
  have hB₂ : (geoTransformAlong M₂ T₂).E = bornAlong T₂ := by rw [boundary_decomp]; rfl
  rwa [hB₁,hB₂] at ht
end
end Hironaka.HironakaG3BornBoundaryPhysicalOverlap
