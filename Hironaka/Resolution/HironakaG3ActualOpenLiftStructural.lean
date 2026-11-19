import Hironaka.Resolution.HironakaG3GeometricLiftStructural
import Hironaka.Resolution.HironakaG3ActualOpenLiftComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ActualOpenLiftStructural
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3CoupledOpenRestriction
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeOpenLift
  HironakaDisjointNativeReferenceWindow HironakaSharpActualCurveComparisonRestriction
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition HironakaG3EmptyAwareSymmetry
  HironakaG3GeometricLiftComparison HironakaG3GeometricLiftStructural
  HironakaG3ActualOpenLiftComparison ResolutionInvariantSpec

/-- Two actual coupled histories restrict to ambient towers which compare
whenever their genuine restricted intrinsic histories align. -/
theorem compare_restricted_actual_coupled_structural
    {d t : ℕ} {X₁ X₂ : CMfd.{0} (d+t)} {N₁ : Set X₁} {N₂ : Set X₂}
    (hNc₁ : IsClosed N₁) (hN₁ : ∀ x ∈ N₁, RegularAtDim (n := d+t) N₁ x d)
    (hNc₂ : IsClosed N₂) (hN₂ : ∀ x ∈ N₂, RegularAtDim (n := d+t) N₂ x d)
    {B₁ : List (Set X₁)} {B₂ : List (Set X₂)} {J₁ : GermIdeal (d+t) X₁} {J₂ : GermIdeal (d+t) X₂}
    {M₁ : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N₁ hN₁)}
    {M₂ : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N₂ hN₂)}
    (hM₁ : IsInvDomain d M₁) (hM₂ : IsInvDomain d M₂)
    {Q₁ Q₂ : CMfd.{0} d} {Y₁ Y₂ : CMfd.{0} (d+t)}
    {T₁ : BlowupTower (nativeManifold (Nat.le_add_right d t) N₁ hN₁) Q₁}
    {T₂ : BlowupTower (nativeManifold (Nat.le_add_right d t) N₂ hN₂) Q₂}
    {U₁ : BlowupTower X₁ Y₁} {U₂ : BlowupTower X₂ Y₂} {η₁ : Q₁ → Y₁} {η₂ : Q₂ → Y₂}
    (hT₁ : IsGeoTestTower M₁ T₁) (hT₂ : IsGeoTestTower M₂ T₂)
    (hU₁ : IsGeoTestTower (fullMarked B₁ J₁) U₁) (hU₂ : IsGeoTestTower (fullMarked B₂ J₂) U₂)
    (h₁ : CoupledHistory N₁ B₁ J₁ (Subtype.val : N₁ → X₁) M₁ T₁ U₁ η₁)
    (h₂ : CoupledHistory N₂ B₂ J₂ (Subtype.val : N₂ → X₂) M₂ T₂ U₂ η₂)
    (O₁ : Opens X₁) (O₂ : Opens X₂)
    (Ξ : CMfd.of (n := d+t) O₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ CMfd.of (n := d+t) O₂)
    (Ω : CMfd.of (n := d) (contactWindow N₁ hN₁ O₁) ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      CMfd.of (n := d) (contactWindow N₂ hN₂ O₂))
    (hcompat : ∀ p : contactWindow N₁ hN₁ O₁,
      (Ξ ⟨p.val.val,p.property⟩).val = (Ω p).val.val)
    (ψ : CMfd.of (n := d) (openPreimage T₁ (contactWindow N₁ hN₁ O₁))
      ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      CMfd.of (n := d) (openPreimage T₂ (contactWindow N₂ hN₂ O₂)))
    (hAlign : EmptyAwareTowerIso Ω (restrict (contactWindow N₁ hN₁ O₁) T₁)
      (restrict (contactWindow N₂ hN₂ O₂) T₂) ψ) :
    ∃ β : CMfd.of (n := d+t) (openPreimage U₁ O₁)
      ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯
        CMfd.of (n := d+t) (openPreimage U₂ O₂),
      EmptyAwareTowerIso Ξ (restrict O₁ U₁) (restrict O₂ U₂) β := by
  let := chartedSpace (Nat.le_add_right d t) hN₁
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN₁
  let := chartedSpace (Nat.le_add_right d t) hN₂
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN₂
  obtain ⟨_hSc₁,_hS₁,R₁,α₁,β₁,hL₁,hI₁,hα₁,hβ₁⟩ :=
    exists_open_native_lift_of_coupled hNc₁ hN₁
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel d) (nativeManifold (Nat.le_add_right d t) N₁ hN₁) ∞)
      (ι := (Subtype.val : N₁ → X₁)) (fun _ => rfl) hM₁ hT₁ hU₁ h₁ O₁
  obtain ⟨_hSc₂,_hS₂,R₂,α₂,β₂,hL₂,hI₂,hα₂,hβ₂⟩ :=
    exists_open_native_lift_of_coupled hNc₂ hN₂
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel d) (nativeManifold (Nat.le_add_right d t) N₂ hN₂) ∞)
      (ι := (Subtype.val : N₂ → X₂)) (fun _ => rfl) hM₂ hT₂ hU₂ h₂ O₂
  have hLow := HironakaG3EmptyAwareComposition.trans
    (HironakaG3EmptyAwareSymmetry.symm (emptyAware_of_isTowerIso hI₁))
    (HironakaG3EmptyAwareComposition.trans hAlign (emptyAware_of_isTowerIso hI₂))
  have hBase : ∀ p, Ξ p.val = (α₁.symm.trans (Ω.trans α₂) p).val := by
    intro p
    let q := α₁.symm p
    have hq := hcompat q
    have he₁ := hα₁ q
    have he₂ := hα₂ (Ω q)
    apply Subtype.ext
    have hqv : (⟨q.val.val,q.property⟩ : O₁) = p.val := by
      apply Subtype.ext
      simpa only [q, α₁.apply_symm_apply] using he₁.symm
    change (Ξ p.val).val = ((α₂ (Ω q)).val : O₂).val
    rw [he₂, ← hq, hqv]
  obtain ⟨β,hβ,_hη⟩ := compare_geom_lifts_structural Ξ _ hLow hBase
    (geomCoupled_of_native_lift hL₁) (geomCoupled_of_native_lift hL₂)
  exact ⟨β,hβ⟩

end
end Hironaka.HironakaG3ActualOpenLiftStructural
