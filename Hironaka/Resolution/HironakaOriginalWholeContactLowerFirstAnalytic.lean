/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.NonmonomialDiffeoExact
import Hironaka.Resolution.HironakaOriginalWholeContactMaskDictionary
/-! The SAME literal original contact lower first entry is an exact trace of
actual whole contact remainder Nm order equations in every induction level.
Complete source-first blueprint precedes code. Actual chosen open and complete
record/domain dictionaries are internally produced from original inputs. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalWholeContactLowerFirstAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedIdealAlong StepOneValue StepOneLowerDomain StepOneRegime CanonicalCentres
  NonmonomialOrderLocal MonomialPartAlong GermIdealOrder MaxLocusLocal
  ContactStageKept HironakaStepOneZeroContactRemainderExtension MarkedIdealBiholomorphism
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}


abbrev contactHeadAt (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) :=
  head R (HironakaOriginalFrozenRecursiveLower.runAt K R p)
abbrev contactTailAt (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) :=
  tail R (HironakaOriginalFrozenRecursiveLower.runAt K R p)
abbrev contactMaskAt (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) :=
  maskB K (contactHeadAt K R p) ((contactTailAt K R p).proj p)

def wholeContactFinalMarked (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) (U : Opens X) :=
  let H := contactHeadAt K R p
  let Q := contactTailAt K R p
  let V := openPreimage H U
  geoTransformAlong (contactRemainderMarked (contactMarkedKept K
    (tangentChoice K (H.proj (Q.proj p))).2 H V) K.E.length) (restrict V Q)

/-- The real original inclusion preserves the SAME underlying final point. -/
def contactFinalLift (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) (U : Opens X)
    (hW : contactMaskAt K R p ≤ openPreimage (contactHeadAt K R p) U) :
    openPreimage (contactTailAt K R p) (contactMaskAt K R p) →
      openPreimage (contactTailAt K R p) (openPreimage (contactHeadAt K R p) U) :=
  fun z => ⟨z,openPreimage_mono (contactTailAt K R p) hW z.property⟩

theorem contMDiff_contactFinalLift (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) (U : Opens X)
    (hW : contactMaskAt K R p ≤ openPreimage (contactHeadAt K R p) U) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (contactFinalLift K R p U hW) :=
  (ContMDiff.subtypeVal_comp_iff _ _).mp contMDiff_subtype_val

/-- The literal original level-(k+1) contact lower first threshold, retaining its actual carrier. -/
def literalContactFirstThreshold (hn : 0 < n) (k : ℕ)
    (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) (a : ℕ) :
    Set (openPreimage (contactTailAt K R p) (contactMaskAt K R p)) :=
  {z | z ∈ (geoTransformAlong (StepOneValueMasked.lowerMarkedB K (contactHeadAt K R p)
      ((contactTailAt K R p).proj p)) (restrict (contactMaskAt K R p) (contactTailAt K R p))).N ∧
    a ≤ (ofLex ((invFamily hn (k+1)).inv (StepOneValueMasked.lowerMarkedB K (contactHeadAt K R p)
      ((contactTailAt K R p).proj p)) (restrict (contactMaskAt K R p) (contactTailAt K R p)) z)).1}

/-- ONLY original contact input constructs the entire genuine whole order dictionary and equations. -/
theorem exists_actual_contact_first_order_dictionary (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) :
    ∃ U : Opens X, (U : Set X) =
        (tangentChoice K ((contactHeadAt K R p).proj ((contactTailAt K R p).proj p))).1 ∧
      ∃ hW : contactMaskAt K R p ≤ openPreimage (contactHeadAt K R p) U,
      IsInvDomain (k+1) (wholeContactFinalMarked K R p U) ∧
      (∀ z : openPreimage (contactTailAt K R p) (contactMaskAt K R p),
        (ofLex ((invFamily hn (k+1)).inv
          (StepOneValueMasked.lowerMarkedB K (contactHeadAt K R p) ((contactTailAt K R p).proj p))
          (restrict (contactMaskAt K R p) (contactTailAt K R p)) z)).1 =
          nmOrd (wholeContactFinalMarked K R p U) (contactFinalLift K R p U hW z)) ∧
      ∀ a : ℕ,
        literalContactFirstThreshold hn k K R p a =
          contactFinalLift K R p U hW ⁻¹' ordGe (wholeContactFinalMarked K R p U) a ∧
        IsComplexAnalyticSubset (n := n) (ordGe (wholeContactFinalMarked K R p U) a) ∧
        IsComplexAnalyticSubset (n := n) (literalContactFirstThreshold hn k K R p a) := by
  obtain ⟨U,hU,hw,hW,_hinit,_hprefix⟩ :=
    HironakaOriginalWholeContactMaskDictionary.contactRemainder_actual_masked_prefix_eq hn K hK hmax R hcan p hp hns hl
  let H := contactHeadAt K R p
  let Q := contactTailAt K R p
  let V := openPreimage H U
  let W := contactMaskAt K R p
  let L := contactMarkedKept K (tangentChoice K (H.proj (Q.proj p))).2 H V
  let S := geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V Q)
  let J := geoTransformAlong (StepOneValueMasked.lowerMarkedB K H (Q.proj p)) (restrict W Q)
  let O := openPreimage (restrict V Q) (nestedOpens V W)
  let χ := nestedDiffeo (n := n) (openPreimage Q V) O (openPreimage Q W)
    (mem_openPreimage_restrict_nestedOpens V W Q) (openPreimage_mono Q hW)
  have hB := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+2)
    (invFamily hn (k+1)) K hK hmax hn R hcan
  have hT : IsGeoTestTower (barMarked K) (H.append Q) := by
    change IsGeoTestTower (barMarked K) ((head R (HironakaOriginalFrozenRecursiveLower.runAt K R p)).append
      (tail R (HironakaOriginalFrozenRecursiveLower.runAt K R p)))
    rw [head_append_tail]
    exact hB.1
  have hS : IsInvDomain (k+1) S :=
    HironakaOriginalWholeContactRemainderDomain.contact_remainder_domain K hK U _ hw H Q hT
  have hrec : MarkedIdeal.pullback χ J = MarkedIdeal.pullback (Subtype.val : O → openPreimage Q V) S :=
    HironakaOriginalWholeContactMaskDictionary.contact_remainder_nested_transform K hK U _ hw H Q hT
      (Q.proj p) hW rfl
  have hH := ((isGeoTestTower_append_iff _ H Q).mp hT).1
  have hStage0 := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le K hK.isWellFormed
    hK.one_le_d hK.dimLE U hw H hH W hW
    (fun z hz _ => (interior_subset hz).2.2)
    (fun A hA z hz _ => (interior_subset hz).2.1 A hA)
  have hStage : IsInvDomain (k+1) (StepOneValueMasked.lowerMarkedB K H (Q.proj p)) := by
    simpa only [show (k+2)-1=k+1 by omega,StepOneValueMasked.lowerMarkedB,W] using hStage0
  have hTail := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
    U hw H Q hT W hW).1
  have hJ : IsInvDomain (k+1) J := InvDomainTowerAlong.isInvDomain_geoTransformAlong hStage (restrict W Q) hTail
  have hMap : ∀ z : openPreimage Q W,(χ.symm z).val=contactFinalLift K R p U hW z := by
    intro z
    apply Subtype.ext
    rfl
  have hFirst : ∀ z : openPreimage Q W,
      (ofLex ((invFamily hn (k+1)).inv (StepOneValueMasked.lowerMarkedB K H (Q.proj p)) (restrict W Q) z)).1 =
        nmOrd S (contactFinalLift K R p U hW z) := by
    intro z
    change nmOrd J z = _
    have h1 := nmOrd_pullback_diffeo hn χ hJ.isWellFormed hJ.isNonzeroAlongAt (χ.symm z)
    rw [hrec] at h1
    rw [nmOrd_pullback_val hn hS.isWellFormed hS.isNonzeroAlongAt O (χ.symm z)] at h1
    simpa only [χ.apply_symm_apply,hMap z] using h1.symm
  have hCarrier : ∀ z : openPreimage Q W,
      z ∈ J.N ↔ contactFinalLift K R p U hW z ∈ S.N := by
    intro z
    have hN := congrArg (fun A : MarkedIdeal n O => A.N) hrec
    have hz := Set.ext_iff.mp hN (χ.symm z)
    change χ (χ.symm z) ∈ J.N ↔ (χ.symm z).val ∈ S.N at hz
    rw [χ.apply_symm_apply] at hz
    rw [hMap z] at hz
    exact hz
  have hcoh := isCoherent_nonmonomialPartAlong hn hS.isWellFormed.isClosedSubmanifold_N
    hS.isWellFormed.isSNCDivisor hS.isWellFormed.isTransverse hS.isWellFormed.isCoherent hS.isNonzeroAlongAt
  have hWholeA : ∀ a : ℕ,IsComplexAnalyticSubset (n := n) (ordGe S a) := by
    intro a
    cases a with
    | zero =>
      change IsComplexAnalyticSubset (n := n) (GermIdealOrder.cosupport n _ _ 0)
      rw [GermIdealOrder.cosupport_zero
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)]
      exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hS.isWellFormed.isClosedSubmanifold_N
    | succ a =>
      exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hcoh
        hS.isWellFormed.isClosedSubmanifold_N (Nat.succ_pos a)
  refine ⟨U,hU,hW,hS,hFirst,?_⟩
  intro a
  have hEq : literalContactFirstThreshold hn k K R p a = contactFinalLift K R p U hW ⁻¹' ordGe S a := by
    ext z
    change (z ∈ J.N ∧ a ≤ (ofLex ((invFamily hn (k+1)).inv
      (StepOneValueMasked.lowerMarkedB K H (Q.proj p)) (restrict W Q) z)).1) ↔ _
    rw [hFirst z,hCarrier z]
    constructor
    · rintro ⟨hz,ha⟩
      exact (mem_ordGe_iff hS.isWellFormed hS.isNonzeroAlongAt hz a).mpr ha
    · intro hz
      have hzN := ordGe_subset_N S a hz
      exact ⟨hzN,(mem_ordGe_iff hS.isWellFormed hS.isNonzeroAlongAt hzN a).mp hz⟩
  refine ⟨hEq,hWholeA a,?_⟩
  rw [hEq]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_contactFinalLift K R p U hW) (hWholeA a)

/-- The ENTIRE literal original contact lower first threshold has a real whole analytic extension. -/
theorem isComplexAnalyticSubset_literalContactFirstThreshold (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) (a : ℕ) :
    IsComplexAnalyticSubset (n := n) (literalContactFirstThreshold hn k K R p a) := by
  obtain ⟨_,_,_,_,_,hA⟩ := exists_actual_contact_first_order_dictionary hn K hK hmax R hcan p hp hns hl
  exact (hA a).2.2

/-- Original full positive data internally construct the SAME real contact branch and equations. -/
theorem isComplexAnalyticSubset_original_companion_contact_lower_first (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+2)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp)
    (hq : 1 ≤ HironakaOriginalFrozenCompanionPresentation.orderAt m T x)
    (hsp : ¬ IsSpecial (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
      (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)
      (HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq))
    (hl : level (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
      (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)
      (HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq)=0) (a : ℕ) :
    IsComplexAnalyticSubset (n := n)
      (literalContactFirstThreshold hn k (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
        (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)
        (HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq) a) := by
  let p := HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq
  obtain ⟨_,hK,hmax,hcanK,hdict⟩ :=
    HironakaOriginalFrozenCompanionPresentation.actual_frozen_companion_domain_and_cosupport (k := k+1) hn m h T hc x hx hq
  have hp : p ∈ (geoTransformAlong (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
    (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)).cosupp := (hdict p).mpr ⟨hx,rfl⟩
  exact isComplexAnalyticSubset_literalContactFirstThreshold hn _ hK hmax _ hcanK p hp hsp hl a

end
end Hironaka.HironakaOriginalWholeContactLowerFirstAnalytic
