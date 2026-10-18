/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalWholeContactRemainderDomain
/-! Entire original contact marked records and actual prefix dictionaries in
every induction level. Source-first complete blueprint precedes code. Genuine
original masked nonzero and all-prefix whole domain are internally constructed;
no caller output certificate. Full deeper/higher/special closure remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalWholeContactMaskDictionary
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction DropMembers
  GermIdealOrder BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneZeroContactPatchValues MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HomogenizedGlueingTower GlobalComponents CodimOneSupportAlong
open DivisorExponentAlong MemberInterLocusAlong MemberInterTowerAlong
  StepOneLowerDomain StepOneValue StepOneRegime CanonicalCentres
  HironakaDimensionThreeStepOneLowerAnalyticLoci ContactEquivalenceAlong MaximalContactAlongTower TangentDirectionAlong ContactStageKept ContactStageInvDomain
  HomogenizedIdealAlong HomogenizedIdealAlongTower NormalCrossings NormalCrossingsInvariance
  HironakaCoherentTransformExtension LocalGiraudTransformAlong
open HironakaGeneralThreeNonspecialAnalyticLoci
open MaxLocusLocal BlowupTowerIsomorphism RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
open HironakaStepOneZeroContactRemainderExtension NonmonomialOrderLocal MonomialPartAlong
variable {n k b : ℕ} {X Y : CMfd.{u} n}

private theorem preimage_remaining_eq_of_nonzero (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d)
    (O : Opens X)
    (hnz : ∀ p ∈ (MarkedIdeal.pullback (Subtype.val : O → X) L).N,
      IsNonzeroAlongAt (MarkedIdeal.pullback (Subtype.val : O → X) L).N
        (MarkedIdeal.pullback (Subtype.val : O → X) L).ideal p) :
    (Subtype.val : O → X) ⁻¹' remainingComponents (n := n) L.N L.cosupp =
      (Subtype.val : O → X) ⁻¹' L.N := by
  have hcoh : (MarkedIdeal.pullback (Subtype.val : O → X) L).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  have hcs := cosupp_pullback_val L (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hI) O
  ext p
  rw [remainingComponents_eq_diff_selected hN]
  refine ⟨fun hp => hp.1, fun hp => ⟨hp, ?_⟩⟩
  intro hps
  have hnr : (p : X) ∉ remainingComponents (n := n) L.N L.cosupp := by
    rw [remainingComponents_eq_diff_selected hN]
    exact fun h => h.2 hps
  have hnear : ∀ᶠ y in 𝓝 (p : X), y ∈ L.N → y ∈ L.cosupp := by
    filter_upwards [(isClosedSubmanifold_remainingComponents hN L.cosupp).1.isOpen_compl.mem_nhds hnr] with y hy hyN
    have hys : y ∈ selectedComponents (n := n) L.N L.cosupp := by
      by_contra hnot
      exact hy (by rw [remainingComponents_eq_diff_selected hN]; exact ⟨hyN, hnot⟩)
    rcases hys with ⟨B, ⟨_, hBA⟩, hyB⟩
    exact hBA hyB
  obtain ⟨g, hg, hf⟩ := hnz p hp
  have hm := HomogenizedGlueing.eventually_mem hcoh hg
  have hv := continuous_subtype_val.continuousAt.tendsto.eventually hnear
  obtain ⟨q, ⟨hqN, hqg⟩, hqm, hqv⟩ := (hf.and_eventually (hm.and hv)).exists
  have hqcs : q ∈ (MarkedIdeal.pullback (Subtype.val : O → X) L).cosupp := by
    rw [hcs]
    exact hqv hqN
  exact hqg ((vanishesToOrderOn_one_iff hqN
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh _ _ hqm)).mp
      ((hqcs.2 g hqm).mono hd))

private theorem remainder_mask_eq (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d)
    (hk : k ≤ L.E.length) (O : Opens X)
    (hnz : ∀ p ∈ (MarkedIdeal.pullback (Subtype.val : O → X) L).N,
      IsNonzeroAlongAt (MarkedIdeal.pullback (Subtype.val : O → X) L).N
        (MarkedIdeal.pullback (Subtype.val : O → X) L).ideal p)
    (hhist : ∀ B ∈ L.E.take k, ∀ p : O, (p : X) ∉ B) :
    MarkedIdeal.pullback (Subtype.val : O → X) (contactRemainderMarked L k) =
      MarkedIdeal.pullback (Subtype.val : O → X) L := by
  have hNrec := preimage_remaining_eq_of_nonzero L hN hI hd O hnz
  have hErec : (L.E.take k).map ((Subtype.val : O → X) ⁻¹' ·) = List.replicate k ∅ := by
    apply List.eq_replicate_iff.mpr
    refine ⟨?_, ?_⟩
    · simp only [List.length_map, List.length_take, Nat.min_eq_left hk]
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
      exact eq_empty_iff_forall_notMem.mpr (hhist A hA)
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hNrec
  · change (List.replicate k ∅ ++ L.E.drop k).map ((Subtype.val : O → X) ⁻¹' ·) =
      L.E.map ((Subtype.val : O → X) ⁻¹' ·)
    rw [List.map_append, List.map_replicate, preimage_empty]
    conv_rhs => rw [← List.take_append_drop k L.E, List.map_append, hErec]
  · rfl
  · rfl

private theorem contact_remainder_initial_mask {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q))
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (p₀ : Y) (hW : maskB K H p₀ ≤ openPreimage H U)
    (hwchoice : w = (tangentChoice K (H.proj p₀)).2) :
    let V := openPreimage H U
    let W := maskB K H p₀
    let L := contactMarkedKept K w H V
    MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) (contactRemainderMarked L K.E.length) =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) := by
  dsimp only
  let V := openPreimage H U
  let W := maskB K H p₀
  let L := contactMarkedKept K w H V
  have hH := ((isGeoTestTower_append_iff _ H Q).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hLN : IsClosedSubmanifold n L.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa V subset_rfl
  have hG := isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N w H hH
  have hLI : L.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hG
  have hinit : MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) L =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) := by
    dsimp only [L]
    rw [hwchoice] at hG ⊢
    exact pullback_val_pullback_val hG hW
  have hdom := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le K hK.isWellFormed
    hK.one_le_d hK.dimLE U hw H hH W hW
    (fun z hz _ => (interior_subset hz).2.2)
    (fun A hA z hz _ => (interior_subset hz).2.1 A hA)
  have hlower : IsInvDomain (k+1) (StepOneValueMasked.lowerMarkedB K H p₀) := by
    rw [show (k+2)-1=k+1 by omega] at hdom
    simpa only [hwchoice, StepOneValueMasked.lowerMarkedB, W] using hdom
  have hsmall := InvDomainTowerAlong.isInvDomain_pullback (nestedOpensDiffeo (n := n) hW) hlower
  rw [← hinit] at hsmall
  have hh : ∀ B ∈ L.E.take K.E.length, ∀ p : nestedOpens V W, (p : V) ∉ B := by
    intro B hB p
    change B ∈ ((geoTransformAlong (barMarked K) H).E.map ((Subtype.val : V → Y) ⁻¹' ·)).take K.E.length at hB
    rw [← List.map_take] at hB
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    have hpW : ((p : V) : Y) ∈ maskB K H p₀ := p.2
    exact (interior_subset hpW).2.1 A hA
  have hlen : K.E.length ≤ L.E.length := by
    change K.E.length ≤ ((geoTransformAlong (barMarked K) H).E.map ((Subtype.val : V → Y) ⁻¹' ·)).length
    rw [List.length_map]
    exact length_E_le_length_E_geoTransformAlong (barMarked K) H
  have heq := remainder_mask_eq (X := CMfd.of (n := n) V) L K.E.length hLN hLI
    (ContactIndependenceAlong.one_le_coeffMarkedAlong_d _) hlen
    (nestedOpens V W) hsmall.isNonzeroAlongAt hh
  exact heq.trans hinit


/-- Actual contact remainder controlled transforms commute with every true open restriction. -/
theorem contact_remainder_transform_restrict (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H)
    (O : Opens (openPreimage H U)) :
    ∀ {Z : CMfd.{u} n} (Q : BlowupTower Y Z),
      IsGeoTestTower (geoTransformAlong (barMarked K) H) Q →
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → V) (contactRemainderMarked L K.E.length))
        (restrict O (restrict V Q)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage (restrict V Q) O → openPreimage Q V)
        (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V Q))
  | _, .refl, _ => rfl
  | _, .step Q C π hπ, hQ => by
    obtain ⟨hQQ,hC⟩ := hQ
    have ih := contact_remainder_transform_restrict K hK U w hw H hH O Q hQQ
    have hIT := (HironakaOriginalWholeContactRemainderDomain.contact_remainder_domain K hK U w hw H Q
      ((isGeoTestTower_append_iff _ _ _).mpr ⟨hH,hQQ⟩)).isWellFormed.isCoherent
    have hInew := (HironakaOriginalWholeContactRemainderDomain.contact_remainder_domain K hK U w hw H
      (.step Q C π hπ) ((isGeoTestTower_append_iff _ _ _).mpr ⟨hH,hQQ,hC⟩)).isWellFormed.isCoherent
    dsimp only
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → openPreimage H U)
      (contactRemainderMarked (contactMarkedKept K w H (openPreimage H U)) K.E.length))
      (restrict O (restrict (openPreimage H U) Q))).geoTransform
        ((Subtype.val : openPreimage (restrict (openPreimage H U) Q) O → _) ⁻¹'
          ((Subtype.val : openPreimage Q (openPreimage H U) → _) ⁻¹' C)) _ = _
    rw [ih]
    have hπV := BlowupRestrictOpen.isBlowupAlong_restrict hπ (openPreimage Q (openPreimage H U))
      ((openPreimage Q (openPreimage H U)).isOpen.preimage hπ.contMDiff.continuous)
    exact geoTransform_pullback_val hIT hπV hInew (openPreimage (restrict (openPreimage H U) Q) O) _

theorem contactRemainder_original_mask_record_eq (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    let W := maskB K H p₀
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      ∃ hW : W ≤ openPreimage H U,
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) (contactRemainderMarked L K.E.length) =
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) := by
  dsimp only
  obtain ⟨U, hU, _, hw, _, hW, _, _, _, _, _⟩ :=
    HironakaOriginalWholeContactRemainderDomain.exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  refine ⟨U, hU, hw, hW, ?_⟩
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+2) (invFamily hn (k+1)) K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
      (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by
    rw [head_append_tail]; exact hb.1
  exact contact_remainder_initial_mask K hK _ _ ht U _ hw _ hW rfl

theorem contact_remainder_nested_transform {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (P : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append P))
    (p₀ : Y) (hW : maskB K H p₀ ≤ openPreimage H U)
    (hwchoice : w = (tangentChoice K (H.proj p₀)).2) :
    let V := openPreimage H U
    let W := maskB K H p₀
    let L := contactMarkedKept K w H V
    let χ := nestedDiffeo (openPreimage P V)
      (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
      (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
    MarkedIdeal.pullback χ (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
      MarkedIdeal.pullback
        (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
        (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P)) := by
  dsimp only
  let V := openPreimage H U
  let W := maskB K H p₀
  let L := contactMarkedKept K w H V
  have hH := ((isGeoTestTower_append_iff _ H P).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hLN : IsClosedSubmanifold n L.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa V subset_rfl
  have hLI : L.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N w H hH)
  have htV : IsGeoTestTower L (restrict V P) := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H P hT V subset_rfl).1
  have htW := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H P hT W hW).1
  rw [hwchoice] at htW
  have hNW := isClosedSubmanifold_strictAlong_stage_of_le K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa W hW
  rw [hwchoice] at hNW
  have hIW : (StepOneValueMasked.lowerMarkedB K H p₀).ideal.IsCoherent := by
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N _ H hH)
  have hinit := contact_remainder_initial_mask K hK H P hT U w hw p₀ hW hwchoice
  have hiso := isTowerIso_restrict_nestedOpens (X := Y) hW P
  have h1 := IsTowerIso.geoTransformAlong_eq (nestedOpensDiffeo (n := n) hW) hNW hIW hiso htW
  rw [← hinit] at h1
  have hQ := ((isGeoTestTower_append_iff _ H P).mp hT).2
  have h2 := contact_remainder_transform_restrict K hK U w hw H hH (nestedOpens V W) P hQ
  exact h1.symm.trans h2


theorem contactRemainder_actual_masked_prefix_eq (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    let W := maskB K H p₀
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      ∃ hW : W ≤ openPreimage H U,
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) (contactRemainderMarked L K.E.length) =
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) ∧
      ∀ j : ℕ, let P := head Q j
        let χ := nestedDiffeo (openPreimage P V)
          (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
          (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
        IsInvDomain (k+1) (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P)) ∧
          MarkedIdeal.pullback χ
            (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
            MarkedIdeal.pullback
              (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
              (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P)) := by
  dsimp only
  obtain ⟨U, hU, _, hw, _, hW, _, _, _, _, _⟩ :=
    HironakaOriginalWholeContactRemainderDomain.exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+2) (invFamily hn (k+1)) K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
      (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by
    rw [head_append_tail]; exact hb.1
  have hsplit := (isGeoTestTower_append_iff _ _ _).mp ht
  refine ⟨U, hU, hw, hW, contact_remainder_initial_mask K hK _ _ ht U _ hw _ hW rfl, ?_⟩
  intro j
  have hpref := ((isGeoTestTower_iff_head_tail _ _ j).mp hsplit.2).1
  have htp := (isGeoTestTower_append_iff _ _ _).mpr ⟨hsplit.1, hpref⟩
  exact ⟨HironakaOriginalWholeContactRemainderDomain.contact_remainder_domain K hK U _ hw _ _ htp,
    contact_remainder_nested_transform K hK U _ hw _ _ htp _ hW rfl⟩


end
end Hironaka.HironakaOriginalWholeContactMaskDictionary
