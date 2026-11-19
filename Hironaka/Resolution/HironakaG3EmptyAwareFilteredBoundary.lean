import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3EmptyAwareFilteredBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareFullBoundary HironakaG3EmptyAwareBornSlots
  HironakaOriginalBoundaryEmptyFilterComparison HironakaOriginalBoundaryEmptyBaseComparison

/-- An empty-aware physical comparison transports the full transformed
boundary after filtering empty slots, even when the initial ordered lists
differ by empty slots. -/
theorem full_boundary_transport_of_filtered_initial {d : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{u} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (M₁ : MarkedIdeal d P₁) (M₂ : MarkedIdeal d P₂)
    (hE : M₁.E.filter (fun H => decide H.Nonempty) =
      (M₂.E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty))
    (hclosed : ∀ H ∈ M₂.E, IsClosed H) :
    (geoTransformAlong M₁ T₁).E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong M₂ T₂).E.filter (fun H => decide H.Nonempty)).map (ψ ⁻¹' ·) := by
  have he : (nonemptyBoundary M₁).E = ((nonemptyBoundary M₂).E).map (Φ ⁻¹' ·) := by
    change M₁.E.filter (fun H => decide H.Nonempty) =
      (M₂.E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·)
    rw [← filter_map_bijection Φ Φ.surjective]
    exact hE
  have hc : ∀ H ∈ (nonemptyBoundary M₂).E, IsClosed H := by
    intro H hH
    exact hclosed H (List.mem_of_mem_filter hH)
  have hh := full_boundary_transport h (nonemptyBoundary M₁) (nonemptyBoundary M₂) he hc
  rwa [filtered_boundary_nonemptyBoundary_along,filtered_boundary_nonemptyBoundary_along] at hh
end
end Hironaka.HironakaG3EmptyAwareFilteredBoundary
