import Hironaka.Resolution.HironakaG3ResidualFullOverlapBoundary
import Hironaka.Resolution.HironakaG3EmptyAwareFilteredBoundary
import Hironaka.Resolution.HironakaG3BoundaryRestrictInitialList
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualFullBoundaryTransport
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MaxLocusLocal HironakaDisjointFiniteControlledHistory
  HironakaOriginalTerminalOverlapComparison HironakaG3EmptyAwareHistory HironakaG3EmptyAwareFilteredBoundary
  HironakaG3ResidualFullOverlapBoundary HironakaG3BoundaryRestrictInitialList
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)

/-- A physical overlap isomorphism transports both full residual-plus-containing
boundaries after empty trace filtering. -/
theorem residual_full_boundary_transport_on_overlap {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (D : ι → Set X) (hD : ∀ i, IsClosed (D i)) (S R₁ R₂ : Finset ι)
    (hD₁ : Disjoint S R₁) (hD₂ : Disjoint S R₂) (U₁ U₂ : Opens X)
    (hVis₁ : ∀ i, i ∉ S → (D i ∩ (U₁ : Set X)).Nonempty → i ∈ R₁)
    (hVis₂ : ∀ i, i ∉ S → (D i ∩ (U₂ : Set X)).Nonempty → i ∈ R₂)
    (J : GermIdeal n X) {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))))
    (hβ : EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
      (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β) :
    let E₁ := (R₁.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D
    let E₂ := (R₂.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D
    let A₁ := fullMarked (E₁.map ((Subtype.val : U₁ → X) ⁻¹' ·))
      (GermIdeal.pullback (m := n) (Subtype.val : U₁ → X) J)
    let A₂ := fullMarked (E₂.map ((Subtype.val : U₂ → X) ⁻¹' ·))
      (GermIdeal.pullback (m := n) (Subtype.val : U₂ → X) J)
    ((geoTransformAlong A₁ T₁).E.map
      ((Subtype.val : openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)) → Y₁) ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
    (((geoTransformAlong A₂ T₂).E.map
      ((Subtype.val : openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂)) → Y₂) ⁻¹' ·)).filter (fun H => decide H.Nonempty)).map (β ⁻¹' ·) := by
  let E₁ := (R₁.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D
  let E₂ := (R₂.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D
  let A₁ := fullMarked (E₁.map ((Subtype.val : U₁ → X) ⁻¹' ·))
    (GermIdeal.pullback (m := n) (Subtype.val : U₁ → X) J)
  let A₂ := fullMarked (E₂.map ((Subtype.val : U₂ → X) ⁻¹' ·))
    (GermIdeal.pullback (m := n) (Subtype.val : U₂ → X) J)
  let G₁ : MarkedIdeal n X := ⟨univ,E₁,J,1⟩
  let G₂ : MarkedIdeal n X := ⟨univ,E₂,J,1⟩
  let C₁ := pullback (Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁) (pullback (Subtype.val : U₁ → X) G₁)
  let C₂ := pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X) G₂)
  have hC₁ : C₁.E = A₁.E.map ((Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁) ⁻¹' ·) := by
    simp [C₁,A₁,G₁,pullback,fullMarked]
  have hC₂ : C₂.E = A₂.E.map ((Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) ⁻¹' ·) := by
    simp [C₂,A₂,G₂,pullback,fullMarked]
  have hE := residual_full_overlap_marked_boundary D S R₁ R₂ hD₁ hD₂ U₁ U₂ hVis₁ hVis₂ J
  have hclosedE₂ : ∀ H ∈ E₂, IsClosed H := by
    intro H hH
    rcases List.mem_append.mp hH with hR | hS
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hR
      exact hD i
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hS
      exact hD i
  have hclosed : ∀ H ∈ C₂.E, IsClosed H := by
    intro H hH
    rw [hC₂] at hH
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
    obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hK
    exact ((hclosedE₂ L hL).preimage continuous_subtype_val).preimage continuous_subtype_val
  have htransport := full_boundary_transport_of_filtered_initial hβ C₁ C₂ hE hclosed
  rw [boundary_restrict_of_initial_eq A₁ _ C₁ hC₁ T₁,
    boundary_restrict_of_initial_eq A₂ _ C₂ hC₂ T₂] at htransport
  exact htransport
end
end Hironaka.HironakaG3ResidualFullBoundaryTransport
