import Hironaka.Resolution.HironakaG3StoppedAmbientBridge
import Hironaka.Resolution.HironakaG3StoppedBoundaryStructuralOverlap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedBoundaryAmbientBridge
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport SubmanifoldChartedSpace MaxLocusLocal
  HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow
  HironakaActualNativeSectionFiniteHistory HironakaG3ActualOpenLiftComparison
  HironakaG3AmbientContactEquiv HironakaG3StoppedBoundaryStructuralOverlap
  HironakaG3RStoppedOverlap HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition
  HironakaG3EmptyAwareSymmetry HironakaSharpActualCurveComparisonRestriction
  HironakaOriginalTerminalOverlapComparison HironakaG3RTowerClass
  HironakaDisjointFiniteControlledHistory HironakaG3RTowerGluing
open ResolutionInvariantSpec (IsInvDomain)

/-- Stopped-class histories, transported from the actual native contacts in
ambient charts, align on the actual ambient overlap. -/
theorem stopped_contact_histories_align_bdry {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
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
    {Q₁ Q₂ : CMfd.{0} d}
    (T₁ : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N U₁) (openSection_regular hN U₁)) Q₁)
    (T₂ : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N U₂) (openSection_regular hN U₂)) Q₂)
    (hStopped₁ : stoppedClass (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
      MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
      (nativeWindow (Nat.le_add_right d t) N hN U₁) _
      (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U₁).symm T₁).tower)
    (hStopped₂ : stoppedClass (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
      MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
      (nativeWindow (Nat.le_add_right d t) N hN U₂) _
      (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U₂).symm T₂).tower) :
    ∃ ψ : CMfd.of (n := d) (openPreimage T₁ (contactWindow (openSection N U₁) (openSection_regular hN U₁)
      (nestedOpens U₁ (U₁ ⊓ U₂)))) ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      CMfd.of (n := d) (openPreimage T₂ (contactWindow (openSection N U₂) (openSection_regular hN U₂)
      (nestedOpens U₂ (U₁ ⊓ U₂)))),
      EmptyAwareTowerIso (overlapContactEquiv N hNc hN U₁ U₂)
        (restrict (contactWindow (openSection N U₁) (openSection_regular hN U₁) (nestedOpens U₁ (U₁ ⊓ U₂))) T₁)
        (restrict (contactWindow (openSection N U₂) (openSection_regular hN U₂) (nestedOpens U₂ (U₁ ⊓ U₂))) T₂) ψ := by
  let A₁ := nativeWindow (Nat.le_add_right d t) N hN U₁
  let A₂ := nativeWindow (Nat.le_add_right d t) N hN U₂
  let e₁ := windowEquiv (Nat.le_add_right d t) N hN hNc U₁
  let e₂ := windowEquiv (Nat.le_add_right d t) N hN hNc U₂
  let S₁ := transport e₁.symm T₁
  let S₂ := transport e₂.symm T₂
  let C₁ := contactWindow (openSection N U₁) (openSection_regular hN U₁) (nestedOpens U₁ (U₁ ⊓ U₂))
  let C₂ := contactWindow (openSection N U₂) (openSection_regular hN U₂) (nestedOpens U₂ (U₁ ⊓ U₂))
  have hR₁ := HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction
    (transport_isTowerIso e₁.symm T₁) C₁
  have hR₂ := HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction
    (transport_isTowerIso e₂.symm T₂) C₂
  obtain ⟨ψ,hψ⟩ := stopped_structural_overlap_bdry hd hV O hEO hpure hdense hdom A₁ A₂ S₁.tower S₂.tower hStopped₁ hStopped₂
  have hAlign := HironakaG3EmptyAwareComposition.trans
    (HironakaG3EmptyAwareSymmetry.symm (emptyAware_of_isTowerIso hR₁))
    (HironakaG3EmptyAwareComposition.trans hψ (emptyAware_of_isTowerIso hR₂))
  have hBase : (openRestriction e₁.symm (preimageOpen e₁.symm C₁) C₁ rfl).symm.trans
      ((overlapBaseEquiv (n := d) (inf_le_left : A₁ ⊓ A₂ ≤ A₁) inf_le_right).trans
        (openRestriction e₂.symm (preimageOpen e₂.symm C₂) C₂ rfl)) =
      overlapContactEquiv N hNc hN U₁ U₂ := by
    ext p
    apply Subtype.ext
    apply Subtype.ext
    rfl
  exact ⟨_,hBase ▸ hAlign⟩

/-- Actual local coupled test histories whose intrinsic transports are in
the stopped class have compatible ambient restrictions on the overlap. -/
theorem stopped_coupled_ambient_overlap_bdry {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
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
      ∀ y, (((S₂.proj (β y).val : U₂) : X)) = (((S₁.proj y.val : U₁) : X)) := by
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
  obtain ⟨β,hβ⟩ := compare_restricted_actual_coupled
    (hNc.preimage continuous_subtype_val) (openSection_regular hN U₁)
    (hNc.preimage continuous_subtype_val) (openSection_regular hN U₂)
    hM₁ hM₂ hT₁ hT₂ hS₁ hS₂ hC₁ hC₂ O₁ O₂ Ξ Ω hcompat ψ hψ
  refine ⟨β,fun y => ?_⟩
  have hz := congrArg (fun q : O₂ => q.val.val) (hβ y)
  rw [overlapBaseEquiv_point] at hz
  have ht := congrArg (fun q : U₂ => q.val) (proj_restrict O₂ S₂ (β y))
  have hs := congrArg (fun q : U₁ => q.val) (proj_restrict O₁ S₁ y)
  exact ht.symm.trans (hz.trans hs)

/-- A cover carrying actual local stopped coupled histories glues from the
derived ambient overlap maps, without supplying an ambient atlas. -/
theorem exists_glued_stopped_coupled_cover_bdry {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (V : Set (nativeManifold (Nat.le_add_right d t) N hN)) (hV : IsClosed V)
    (E : List (Set (nativeManifold (Nat.le_add_right d t) N hN)))
    (O : Opens (nativeManifold (Nat.le_add_right d t) N hN))
    (hEO : ∀ H ∈ E, Disjoint H (O : Set (nativeManifold (Nat.le_add_right d t) N hN))) {r : ℕ}
    (hpure : ∀ x : O, (x : nativeManifold (Nat.le_add_right d t) N hN) ∈ V →
      RegularAtDim (n := d) V x r) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain d (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
      MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)))
    (I : Type) (U : I → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (B : ∀ i, List (Set (U i))) (J : ∀ i, GermIdeal (d+t) (U i))
    (M : ∀ i, MarkedIdeal d (nativeManifold (Nat.le_add_right d t) (openSection N (U i)) (openSection_regular hN (U i))))
    (hM : ∀ i, IsInvDomain d (M i))
    (Q : I → CMfd.{0} d) (Y : I → CMfd.{0} (d+t))
    (T : ∀ i, BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N (U i)) (openSection_regular hN (U i))) (Q i))
    (S : ∀ i, BlowupTower (CMfd.of (n := d+t) (U i)) (Y i)) (η : ∀ i, Q i → Y i)
    (hT : ∀ i, IsGeoTestTower (M i) (T i))
    (hS : ∀ i, IsGeoTestTower (fullMarked (B i) (J i)) (S i))
    (hC : ∀ i, CoupledHistory (openSection N (U i)) (B i) (J i)
      (Subtype.val : openSection N (U i) → U i) (M i) (T i) (S i) (η i))
    (hStopped : ∀ i, stoppedClass (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ :
      MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
      (nativeWindow (Nat.le_add_right d t) N hN (U i)) _
      (transport (windowEquiv (Nat.le_add_right d t) N hN hNc (U i)).symm (T i)).tower) :
    ∃ (Z : CMfd.{0} (d+t)) (P : Z → X),
      ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ P ∧ IsProperMap P ∧
      Surjective P ∧ ∀ i, ∃ W : Opens Z, (W : Set Z) = P ⁻¹' (U i : Set X) ∧
        ∃ φ : Y i ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ CMfd.of (n := d+t) W,
          ∀ y, P (φ y : Z) = (((S i).proj y : U i) : X) := by
  let A : TowerAtlas X := {
    J := I
    U := U
    cover := hcover
    Y := Y
    T := S
    compare := fun i j => stopped_coupled_ambient_overlap_bdry hd N hNc hN V hV E O hEO hpure hdense hdom
      (U i) (U j) (hM i) (hM j) (T i) (T j) (S i) (S j)
      (hT i) (hT j) (hS i) (hS j) (hC i) (hC j) (hStopped i) (hStopped j) }
  exact A.exists_glued

end
end Hironaka.HironakaG3StoppedBoundaryAmbientBridge
