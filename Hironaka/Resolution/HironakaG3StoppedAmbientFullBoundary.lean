import Hironaka.Resolution.HironakaG3StoppedAmbientStructural
import Hironaka.Resolution.HironakaG3ActualOpenLiftStructural
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedAmbientFullBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport SubmanifoldChartedSpace MaxLocusLocal
  HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow
  HironakaActualNativeSectionFiniteHistory HironakaG3ActualOpenLiftComparison
  HironakaG3ActualOpenLiftStructural HironakaG3AmbientContactEquiv
  HironakaG3StoppedBoundaryStructuralOverlap HironakaG3StoppedBoundaryAmbientBridge
  HironakaG3RStoppedOverlap HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition
  HironakaG3EmptyAwareSymmetry HironakaG3StoppedAmbientStructural HironakaG3EmptyAwareFullBoundary HironakaSharpActualCurveComparisonRestriction
  HironakaOriginalTerminalOverlapComparison HironakaG3RTowerClass
  HironakaDisjointFiniteControlledHistory HironakaG3RTowerGluing
open ResolutionInvariantSpec (IsInvDomain)

/-- Actual local coupled test histories whose intrinsic transports are in
the stopped class have compatible ambient restrictions on the overlap. -/
theorem stopped_coupled_ambient_overlap_full_boundary {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (V : Set (nativeManifold (Nat.le_add_right d t) N hN)) (hV : IsClosed V)
    (E : List (Set (nativeManifold (Nat.le_add_right d t) N hN)))
    (O : Opens (nativeManifold (Nat.le_add_right d t) N hN))
    (hEO : ∀ H ∈ E, Disjoint H (O : Set (nativeManifold (Nat.le_add_right d t) N hN))) {r : ℕ}
    (hpure : ∀ x : O, (x : nativeManifold (Nat.le_add_right d t) N hN) ∈ V →
      RegularAtDim (n := d) V x r) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain d (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
      MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)))
    (U₁ U₂ : Opens X)
    {B₁ : List (Set U₁)} {B₂ : List (Set U₂)} {J₁ : GermIdeal (d+t) U₁} {J₂ : GermIdeal (d+t) U₂}
    {M₁ : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) (openSection N U₁) (openSection_regular hN U₁))}
    {M₂ : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) (openSection N U₂) (openSection_regular hN U₂))}
    (hM₁ : IsInvDomain d M₁) (hM₂ : IsInvDomain d M₂)
    {Q₁ Q₂ : CMfd.{0} d} {Y₁ Y₂ : CMfd.{0} (d+t)}
    (T₁ : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N U₁) (openSection_regular hN U₁)) Q₁)
    (T₂ : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N U₂) (openSection_regular hN U₂)) Q₂)
    (S₁ : BlowupTower (CMfd.of (n := d+t) U₁) Y₁) (S₂ : BlowupTower (CMfd.of (n := d+t) U₂) Y₂)
    {η₁ : Q₁ → Y₁} {η₂ : Q₂ → Y₂}
    (hT₁ : IsGeoTestTower M₁ T₁) (hT₂ : IsGeoTestTower M₂ T₂)
    (hS₁ : IsGeoTestTower (fullMarked B₁ J₁) S₁) (hS₂ : IsGeoTestTower (fullMarked B₂ J₂) S₂)
    (hC₁ : CoupledHistory (openSection N U₁) B₁ J₁ (Subtype.val : openSection N U₁ → U₁) M₁ T₁ S₁ η₁)
    (hC₂ : CoupledHistory (openSection N U₂) B₂ J₂ (Subtype.val : openSection N U₂ → U₂) M₂ T₂ S₂ η₂)
    (hStopped₁ : stoppedClass (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
      MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
      (nativeWindow (Nat.le_add_right d t) N hN U₁) _
      (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U₁).symm T₁).tower)
    (hStopped₂ : stoppedClass (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
      MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
      (nativeWindow (Nat.le_add_right d t) N hN U₂) _
      (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U₂).symm T₂).tower)
    (A₁ : MarkedIdeal (d+t) (CMfd.of (n := d+t) (nestedOpens U₁ (U₁ ⊓ U₂))))
    (A₂ : MarkedIdeal (d+t) (CMfd.of (n := d+t) (nestedOpens U₂ (U₁ ⊓ U₂))))
    (hA : A₁.E = A₂.E.map ((overlapBaseEquiv (n := d+t) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) ⁻¹' ·))
    (hClosed : ∀ H ∈ A₂.E, IsClosed H) :
    ∃ β : CMfd.of (n := d+t) (openPreimage S₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯
        CMfd.of (n := d+t) (openPreimage S₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := d+t) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) S₁)
        (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) S₂) β ∧
      (geoTransformAlong A₁ (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) S₁)).E.filter
        (fun H => decide H.Nonempty) =
      ((geoTransformAlong A₂ (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) S₂)).E.filter
        (fun H => decide H.Nonempty)).map (β ⁻¹' ·) := by
  obtain ⟨β,hβ⟩ := stopped_coupled_ambient_overlap_structural hd N hNc hN V hV E O hEO hpure hdense hdom
    U₁ U₂ hM₁ hM₂ T₁ T₂ S₁ S₂ hT₁ hT₂ hS₁ hS₂ hC₁ hC₂ hStopped₁ hStopped₂
  exact ⟨β,hβ,full_boundary_transport hβ A₁ A₂ hA hClosed⟩

end
end Hironaka.HironakaG3StoppedAmbientFullBoundary
