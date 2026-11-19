import Hironaka.Resolution.HironakaG1ExhaustivePositiveHead
import Hironaka.Resolution.HironakaG1LocalBornOrderContinuation
import Hironaka.Resolution.HironakaG1LocalizedLaterBornRead

/-! The same retained positive head supplies the supported recursive comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1ChronologicalPositiveSupported

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres MarkedIdealBiholomorphism
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime TangentDirectionAlong
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci InvDomainTowerAlong
  HironakaCoherentTransformExtension HironakaG1RecursiveMemberValueTransport
  HironakaG1ChronologicalCompanionSuffix HironakaG1ChronologicalTrueMarkZero
  HironakaG1ChronologicalSupportDomainObstruction HironakaG1AdvancingSupportPowerGap
  CoefficientIdealRestriction ContactEquivalenceAlong InvDomainMemberRestriction
  BoundaryCount DivisorExponentAlong AnalyticDimensionBasics RelativePrincipalizationSpan
  HironakaG3RRawRegimeLocality HironakaG1LocalizedBornWindowRestriction DerivativeIdealAlongEtale

open HironakaG1LocalBornOrderContinuation HironakaG8GapNormalizedExponent
  HironakaG1CoefficientCarrierClassData HironakaActualCoefficientDivisorExponentGap
  HironakaG1LocalizedLaterBornRead HironakaCoherentTransformExtension HironakaG11InvBMClass
  HironakaG1OriginalUnequalMarkCanonical HironakaG1SupportedGapEmptyEpoch
  HironakaG1ChosenCommonContactClassData GermIdealOrder

set_option maxHeartbeats 2000000 in
/-- At the genuine next positive head, the supported nonspecial branch
supplies the contact carrier and the actual selected supported record.
Both initial coefficient gaps follow from the literal member constructions;
they give comparison of every recursive canonical history and its order. -/
theorem chronological_positive_supported_recursive_comparison {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hR : IsInvDomain (k+1) R) (hClass : LocWPEquiv J R)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y)
    (u : X → ℂ)
    (hu : IsTangentDirectionAlong (barMarked J).N (barMarked J).ideal (barMarked J).d
      (⊤ : Opens X) u)
    (hTrace : (barMarked J).N ∩ {x | u x = 0} = R.N) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    ¬ IsSpecial R H p →
    ∃ (D F : CMfd.{0} n) (M C P : MarkedIdeal n D) (w : D → ℂ)
      (U : BlowupTower D F) (z : F),
      IsInvDomain (k+1) M ∧ IsInvDomain k C ∧ IsInvDomain k P ∧
      IsTangentDirectionAlong M.N M.ideal M.d univ w ∧
      C = withN (coeffMarkedAlong M) (M.N ∩ {x | w x = 0}) ∧
      C.N = P.N ∧ C.E = P.E ∧ LocWPEquiv C P ∧
      (∀ G ∈ C.E, ∀ a ∈ C.cosupp, a ∈ G →
        P.d * divExpAlong n C.N C.ideal G a = C.d * divExpAlong n P.N P.ideal G a) ∧
      IsCanonical M ((invFamily hn (k+1)).inv M) U ∧ z ∈ (geoTransformAlong M U).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y =
        toLex (b+1, ((invFamily hn (k+1)).inv M U z : WithTop (ValTy (k+1)))) ∧
      (∀ {Y' : CMfd.{0} n} (T' : BlowupTower D Y'),
        IsCanonical C ((invFamily hn k).inv C) T' ↔ IsCanonical P ((invFamily hn k).inv P) T') ∧
      ∀ {Y' Z' : CMfd.{0} n} (T' : BlowupTower D Y') (S' : BlowupTower D Z'),
        IsCanonical C ((invFamily hn k).inv C) T' →
        IsCanonical C ((invFamily hn k).inv C) S' →
        ∀ a ∈ (geoTransformAlong C T').cosupp, ∀ b ∈ (geoTransformAlong C S').cosupp,
          ((invFamily hn k).inv C T' a < (invFamily hn k).inv C S' b ↔
            (invFamily hn k).inv P T' a < (invFamily hn k).inv P S' b) := by
  intro r H S p hNSR
  obtain ⟨O, hpO, _, _, hDom⟩ :=
    chronological_supported_domain_of_nonspecial_anchor hn J R hJ hR hClass
      hMax T hCan y hy hLevel hNS hNSR
  obtain ⟨hHead, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    positive_companion_chronological_suffix (k := k+1) hn J hJ hMax T hCan y hy hLevel hNS
  obtain ⟨V, v, _, _, _, hTan, _, hContactN, _, _, _, hContactClass,
      hpV, hK, hCanK, _, hyK, hRead⟩ :=
    positive_companion_chronological_tangent (k := k+1) hn J R hJ hR hClass hMax
      T hCan y hy hLevel hNS u hu hTrace
  let A := CMfd.of (n := n) V
  let K : MarkedIdeal n A := positiveMemberOn J H p V
  let K' : MarkedIdeal n A := positiveMemberOn R H p V
  let S₀ := restrict V S
  let z₀ : openPreimage S V := ⟨y,hpV⟩
  let O' : Opens (split T r).1 := V ⊓ O
  have hOV : O' ≤ V := inf_le_left
  let W := MaxLocusLocal.nestedOpens V O'
  let B := CMfd.of (n := n) W
  let L : MarkedIdeal n B := MarkedIdeal.pullback (Subtype.val : W → A) K
  let P : MarkedIdeal n B := MarkedIdeal.pullback (Subtype.val : W → A) K'
  let w : B → ℂ := fun x => v x.val.val
  let U := restrict W S₀
  have hpW : S₀.proj z₀ ∈ W := by
    change (S₀.proj z₀).val ∈ O'
    rw [show (S₀.proj z₀).val = p from proj_restrict V S z₀]
    exact ⟨hpV,hpO⟩
  let z : openPreimage S₀ W := ⟨z₀,hpW⟩
  have hJH := ((bar_local_any_boundary J hJ).wEquiv.2 H).1.mpr hHead
  have hRH := (hClass.wEquiv.2 H).1.mp hJH
  have hDH := ((bar_local_any_boundary R hR).wEquiv.2 H).1.mp hRH
  let D := geoTransformAlong (barMarked R) H
  let P₀ := memberRestrict D (membersThrough D.E (origMembers R H) p)
  have hD := isInvDomain_geoTransformAlong (isInvDomain_barMarked R hR) H hDH
  have hP₀ := isWellFormed_memberRestrict hn hD.isWellFormed (membersThrough D.E (origMembers R H) p)
  have hP : IsInvDomain k P := by
    have hEq := MaxLocusLocal.pullback_val_pullback_val (𝔪 := P₀) hP₀.isCoherent hOV
    change IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → A)
      (MarkedIdeal.pullback (Subtype.val : V → _) P₀))
    rw [hEq]
    exact isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hOV)
      ((hDom O' inf_le_right).2)
  have hL : IsInvDomain (k+1) L := isInvDomain_pullback_val W hK
  have hHol : ∀ x g, K.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hg
  have hTanL : IsTangentDirectionAlong L.N L.ideal L.d univ w :=
    isTangentDirectionAlong_pullback_val W hHol
      ⟨W.isOpen, fun x _ => hTan.mem x (mem_univ _), fun x _ => hTan.multiplicity_one x (mem_univ _)⟩
  have hTraceL : L.N ∩ {x | w x = 0} = P.N := by
    change (Subtype.val : W → A) ⁻¹' (K.N ∩ {x : V | v x.val = 0}) = _
    exact congrArg (fun C : Set A => (Subtype.val : W → A) ⁻¹' C) hContactN
  have hWPL : LocWPEquiv (withN (coeffMarkedAlong L) (L.N ∩ {x | w x = 0})) P := by
    have h0 := selected_bare_contact_pullback_val K hK.isWellFormed hK.one_le_d (v ∘ Subtype.val) W
    exact Eq.mp (congrArg (fun C : MarkedIdeal n B => LocWPEquiv C P) h0)
      (hContactClass.restrict W)
  let I := invFamily hn (k+1)
  have hCanL := Seq.ResolutionInvariantExt.isCanonical_restrict I hK W S₀ hCanK
  have hz : z ∈ (geoTransformAlong L U).cosupp := by
    change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → A) K) (restrict W S₀)).cosupp
    rw [cosupp_restrict_raw K hHol W S₀]
    exact hyK
  let C := withN (coeffMarkedAlong L) (L.N ∩ {x | w x = 0})
  have hCN : C.N = P.N := hTraceL
  have hCoh : C.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hL.isWellFormed.isCoherent hL.isWellFormed.isClosedSubmanifold_N
  have hC : IsInvDomain k C := isInvDomain_of_sameCarrier_cosupp C P hP hCoh
    (ContactIndependenceAlong.one_le_coeffMarkedAlong_d L) hCN hWPL.wEquiv.1 hWPL.cosupp_eq_base
  have hGapK' : HasCosupportGap K' := chronological_supported_source_gap R hR H hRH p V
  have hCoK' : K'.ideal.IsCoherent :=
    (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hP₀ V).isCoherent
  have hGapP : HasCosupportGap P := cosupport_gap_pullback_val K' hCoK' hGapK' W
  have hGapC : HasCosupportGap C := by
    intro a _ ha
    change a ∈ cosupport n C.N (coeffMarkedAlong L).ideal (coeffMarkedAlong L).d
    rw [← coefficient_restriction_cosupport_gap L hL.isWellFormed.isClosedSubmanifold_N
      hL.isWellFormed.isCoherent hL.one_le_d C.N (fun _ hx => hx.1)]
    exact ha
  have hDim := SameCarrierDim.of_N_eq hCN
  have hExp := normalized_exponents_of_gap_sameCarrierDim hn C P hC hP hWPL hDim hGapC hGapP
  have hV := I.isInvValue.restrictOpen K hK W S₀ hCanK z hyK
  have hReadL := hRead.trans (congrArg (fun q : ValTy (k+1) =>
    toLex (b+1, (q : WithTop (ValTy (k+1))))) hV.symm)
  refine ⟨B,_,L,C,P,w,U,z,hL,hC,hP,hTanL,rfl,hCN,hWPL.wEquiv.1,hWPL,hExp,hCanL,hz,hReadL,
    (fun T' => invFamily_isCanonical_iff_of_local hn C P hC hP hWPL hDim hExp T'), ?_⟩
  intro Y' Z' T' S' hTC hSC
  exact (contact_recursive_strict_order_on_canonical_suffixes hn C P hC hP hWPL hCN hExp
    T' S' hTC hSC).2.2

#print axioms chronological_positive_supported_recursive_comparison

end Hironaka.HironakaG1ChronologicalPositiveSupported
