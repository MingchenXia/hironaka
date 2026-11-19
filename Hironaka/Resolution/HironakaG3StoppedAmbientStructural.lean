import Hironaka.Resolution.HironakaG3StoppedBoundaryAmbientBridge
import Hironaka.Resolution.HironakaG3ActualOpenLiftStructural
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedAmbientStructural
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport SubmanifoldChartedSpace MaxLocusLocal
  HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow
  HironakaActualNativeSectionFiniteHistory HironakaG3ActualOpenLiftComparison
  HironakaG3ActualOpenLiftStructural HironakaG3AmbientContactEquiv
  HironakaG3StoppedBoundaryStructuralOverlap HironakaG3StoppedBoundaryAmbientBridge
  HironakaG3RStoppedOverlap HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition
  HironakaG3EmptyAwareSymmetry HironakaSharpActualCurveComparisonRestriction
  HironakaOriginalTerminalOverlapComparison HironakaG3RTowerClass
  HironakaDisjointFiniteControlledHistory HironakaG3RTowerGluing
open ResolutionInvariantSpec (IsInvDomain)

/-- Actual local coupled test histories whose intrinsic transports are in
the stopped class have compatible ambient restrictions on the overlap. -/
theorem stopped_coupled_ambient_overlap_structural {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
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
      (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U₂).symm T₂).tower) :
    ∃ β : CMfd.of (n := d+t) (openPreimage S₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯
        CMfd.of (n := d+t) (openPreimage S₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := d+t) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) S₁)
        (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) S₂) β := by
  obtain ⟨ψ,hψ⟩ := stopped_contact_histories_align_bdry hd N hNc hN V hV E O hEO hpure hdense hdom U₁ U₂
    T₁ T₂ hStopped₁ hStopped₂
  let O₁ := nestedOpens U₁ (U₁ ⊓ U₂)
  let O₂ := nestedOpens U₂ (U₁ ⊓ U₂)
  let Ξ := overlapBaseEquiv (n := d+t) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  let Ω := overlapContactEquiv N hNc hN U₁ U₂
  have hcompat : ∀ p : contactWindow (openSection N U₁) (openSection_regular hN U₁) O₁,
      (Ξ ⟨p.val.val,p.property⟩).val = (Ω p).val.val := by
    intro p
    rfl
  obtain ⟨β,hβ⟩ := compare_restricted_actual_coupled_structural
    (hNc.preimage continuous_subtype_val) (openSection_regular hN U₁)
    (hNc.preimage continuous_subtype_val) (openSection_regular hN U₂)
    hM₁ hM₂ hT₁ hT₂ hS₁ hS₂ hC₁ hC₂ O₁ O₂ Ξ Ω hcompat ψ hψ
  exact ⟨β,hβ⟩

end
end Hironaka.HironakaG3StoppedAmbientStructural
