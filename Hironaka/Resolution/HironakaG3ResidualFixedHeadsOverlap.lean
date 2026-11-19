import Hironaka.Resolution.HironakaG3ResidualStoppedOverlapFinite
import Hironaka.Resolution.HironakaG3StoppedAmbientStructural
import Hironaka.Resolution.HironakaG3FixedContactHeadClass
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualFixedHeadsOverlap
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport SubmanifoldChartedSpace MaxLocusLocal
  HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow HironakaActualNativeSectionFiniteHistory
  HironakaG3ActualOpenLiftComparison HironakaG3ActualOpenLiftStructural HironakaG3AmbientContactEquiv
  HironakaG3StoppedBoundaryAmbientBridge HironakaG3StoppedAmbientStructural HironakaG3RStoppedOverlap
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition HironakaG3EmptyAwareSymmetry
  HironakaSharpActualCurveComparisonRestriction HironakaOriginalTerminalOverlapComparison HironakaG3RTowerClass
  HironakaDisjointFiniteControlledHistory HironakaG3RTowerGluing HironakaG3FixedContactHeadClass
  HironakaG3BoundaryContainedAnalyticTrace HironakaActualNativeInvariantDomain
  HironakaG3ResidualStoppedOverlapFinite

/-- Actual coupled fixed-contact heads for two visible residual windows align
on their literal ambient overlap. -/
theorem fixed_heads_residual_overlap {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
    {ι : Type*} [LinearOrder ι] (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (C : Set X) (hCa : IsComplexAnalyticSubset (n := d+t) C) (hCN : C ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (D : ι → Set X) (hD : ∀ i, IsClosed (D i)) (S R₁ R₂ : Finset ι)
    (hD₁ : Disjoint S R₁) (hD₂ : Disjoint S R₂)
    (hSNC₁ : IsSNCDivisor (d+t) ((R₁.sort (· ≤ ·)).map D))
    (hSNC₂ : IsSNCDivisor (d+t) ((R₂.sort (· ≤ ·)).map D))
    (hTr₁ : IsTransverse (d+t) N ((R₁.sort (· ≤ ·)).map D))
    (hTr₂ : IsTransverse (d+t) N ((R₂.sort (· ≤ ·)).map D))
    (hAvoid₁ : C ⊆ closure (C \ ⋃ H ∈ (R₁.sort (· ≤ ·)).map D, H))
    (hAvoid₂ : C ⊆ closure (C \ ⋃ H ∈ (R₂.sort (· ≤ ·)).map D, H))
    (U₁ U₂ : Opens X)
    (hVis₁ : ∀ i, i ∉ S → (D i ∩ (U₁ : Set X)).Nonempty → i ∈ R₁)
    (hVis₂ : ∀ i, i ∉ S → (D i ∩ (U₂ : Set X)).Nonempty → i ∈ R₂)
    {Y₁ Y₂ : CMfd.{0} (d+t)} (A₁ : BlowupTower (CMfd.of (n := d+t) U₁) Y₁)
    (A₂ : BlowupTower (CMfd.of (n := d+t) U₂) Y₂)
    (h₁ : fixedContactHead N hNc hN ((R₁.sort (· ≤ ·)).map D) C r U₁ Y₁ A₁)
    (h₂ : fixedContactHead N hNc hN ((R₂.sort (· ≤ ·)).map D) C r U₂ Y₂ A₂) :
    ∃ β : CMfd.of (n := d+t) (openPreimage A₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯
        CMfd.of (n := d+t) (openPreimage A₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := d+t) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) A₁)
        (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) A₂) β := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let V : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' C
  have hImage : (Subtype.val : N → X) '' V = C := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩; exact hp
    · intro hy; exact ⟨⟨y,hCN hy⟩,hy,rfl⟩
  have hVa := native_analytic_of_ambient_image N hN V (by rwa [hImage])
  have hVp := native_pure_of_ambient_image N hNc hN V r (by rwa [hImage])
  let D' (i : ι) : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' D i
  have hD' : ∀ i, IsClosed (D' i) := fun i => (hD i).preimage continuous_subtype_val
  have hSN₁ : IsSNCDivisor d ((R₁.sort (· ≤ ·)).map D') := by
    have h := isSNCDivisor_native_preimage (by omega) (Nat.le_add_right d t) hN hSNC₁ hTr₁
    simpa [D',List.map_map,Function.comp_def] using h
  have hSN₂ : IsSNCDivisor d ((R₂.sort (· ≤ ·)).map D') := by
    have h := isSNCDivisor_native_preimage (by omega) (Nat.le_add_right d t) hN hSNC₂ hTr₂
    simpa [D',List.map_map,Function.comp_def] using h
  have hAV₁ : V ⊆ closure (V \ ⋃ H ∈ (R₁.sort (· ≤ ·)).map D', H) := by
    have h := native_dense_avoid_of_ambient_image N hNc hN V ((R₁.sort (· ≤ ·)).map D) (by rwa [hImage])
    simpa [D',List.map_map,Function.comp_def] using h
  have hAV₂ : V ⊆ closure (V \ ⋃ H ∈ (R₂.sort (· ≤ ·)).map D', H) := by
    have h := native_dense_avoid_of_ambient_image N hNc hN V ((R₂.sort (· ≤ ·)).map D) (by rwa [hImage])
    simpa [D',List.map_map,Function.comp_def] using h
  let W₁ := nativeWindow (Nat.le_add_right d t) N hN U₁
  let W₂ := nativeWindow (Nat.le_add_right d t) N hN U₂
  have hV₁ : ∀ i, i ∉ S → (D' i ∩ (W₁ : Set _)).Nonempty → i ∈ R₁ := by
    intro i hi ⟨p,hpD,hpU⟩
    exact hVis₁ i hi ⟨p.val,hpD,hpU⟩
  have hV₂ : ∀ i, i ∉ S → (D' i ∩ (W₂ : Set _)).Nonempty → i ∈ R₂ := by
    intro i hi ⟨p,hpD,hpU⟩
    exact hVis₂ i hi ⟨p.val,hpD,hpU⟩
  obtain ⟨Q₁,T₁,η₁,hM₁,hT₁,hA₁,hC₁,hStop₁⟩ := h₁
  obtain ⟨Q₂,T₂,η₂,hM₂,hT₂,hA₂,hC₂,hStop₂⟩ := h₂
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
  have hStop₁' : HironakaG3RBoundaryEmbedded.bdryClass V r ((R₁.sort (· ≤ ·)).map D') W₁ _ S₁.tower := by
    simpa only [HironakaG3RBoundaryEmbedded.bdryClass,D',List.map_map,Function.comp_def] using hStop₁
  have hStop₂' : HironakaG3RBoundaryEmbedded.bdryClass V r ((R₂.sort (· ≤ ·)).map D') W₂ _ S₂.tower := by
    simpa only [HironakaG3RBoundaryEmbedded.bdryClass,D',List.map_map,Function.comp_def] using hStop₂
  obtain ⟨ψ,hψ⟩ := residual_stopped_histories_overlap_of_window_avoid hd V hVa hr hVp D' hD' S R₁ R₂
    hD₁ hD₂ hSN₁ hSN₂ hAV₁ hAV₂ W₁ W₂ hV₁ hV₂ S₁.tower S₂.tower hStop₁' hStop₂'
  have hAlign := HironakaG3EmptyAwareComposition.trans
    (HironakaG3EmptyAwareSymmetry.symm (emptyAware_of_isTowerIso hR₁))
    (HironakaG3EmptyAwareComposition.trans hψ (emptyAware_of_isTowerIso hR₂))
  have hBase : (openRestriction e₁.symm (preimageOpen e₁.symm C₁) C₁ rfl).symm.trans
      ((overlapBaseEquiv (n := d) (inf_le_left : W₁ ⊓ W₂ ≤ W₁) inf_le_right).trans
        (openRestriction e₂.symm (preimageOpen e₂.symm C₂) C₂ rfl)) =
      overlapContactEquiv N hNc hN U₁ U₂ := by
    ext p
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hContact := hBase ▸ hAlign
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
    hM₁ hM₂ hT₁ hT₂ hA₁ hA₂ hC₁ hC₂ O₁ O₂ Ξ Ω hcompat _ hContact
  exact ⟨β,hβ⟩
end
end Hironaka.HironakaG3ResidualFixedHeadsOverlap
