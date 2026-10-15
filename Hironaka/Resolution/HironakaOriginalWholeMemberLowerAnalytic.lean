/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalStepOneHistoryYearAnalytic
import Hironaka.Resolution.HironakaStepOneMemberTailExtension
/-! Actual original computed ALLk whole member lower presentations and true
GLOBAL prefix order equations, with exact literal masked lower first dictionary.
Complete source-first blueprint precedes code. Arbitrary higher/special boundary
extension and full scheduler remain open. No whole lower canonical certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalWholeMemberLowerAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedIdealAlong StepOneValue StepOneLowerDomain StepOneRegime CanonicalCentres
  NonmonomialOrderLocal MonomialPartAlong GermIdealOrder
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}

abbrev memberHeadAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :=
  head T (HironakaOriginalFrozenRecursiveLower.runAt m T x)

abbrev memberTailAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :=
  tail T (HironakaOriginalFrozenRecursiveLower.runAt m T x)

abbrev memberBasePointAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :=
  (memberTailAt m T x).proj x

/-- The existing true unselected-component whole member marked ideal at the ORIGINAL computed head. -/
def wholeMemberAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :=
  memberLowerExtension m (memberHeadAt m T x) (memberBasePointAt m T x)

private theorem positive_member_mask_transform (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m) {A : CMfd.{u} n}
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked m) H) (y : A)
    (Q : BlowupTower A Y) (hQ : IsGeoTestTower (geoTransformAlong (barMarked m) H) Q)
    (l : ℕ) (hl : level m H y=l) (hlpos : 1 ≤ l) :
    geoTransformAlong (StepOneValueMasked.lowerMarkedM m l H y)
      (restrict (lowerMask m l H y) Q) =
    MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : openPreimage Q (lowerMask m l H y) → Y)
        (geoTransformAlong (memberLowerExtension m H y) Q) := by
  cases l with
  | zero => omega
  | succ l => exact (memberLowerExtension_tail_domain_and_mask_identity hn m h H hH y hl Q hQ).2

/-- Original computed histories internally produce the true entire member prefix domains and exact literal mask. -/
theorem actual_whole_member_history_and_mask (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (hpos : 1 ≤ level m T x) :
    ∃ s : ℕ,level m T x=s+1 ∧
      memberBasePointAt m T x ∈ maskA m (memberHeadAt m T x) (memberBasePointAt m T x) ∧
      (∀ i : ℕ,IsInvDomain (k+1)
        (geoTransformAlong (wholeMemberAt m T x) (head (memberTailAt m T x) i))) ∧
      IsInvDomain (k+1) (geoTransformAlong (wholeMemberAt m T x) (memberTailAt m T x)) ∧
      geoTransformAlong (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
        (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x) =
        MarkedIdealBiholomorphism.MarkedIdeal.pullback
          (Subtype.val : HironakaOriginalFrozenRecursiveLower.patchAt m T x → Y)
          (geoTransformAlong (wholeMemberAt m T x) (memberTailAt m T x)) := by
  obtain ⟨s,hs⟩ : ∃ s : ℕ,level m T x=s+1 := ⟨level m T x-1,by omega⟩
  have hB := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+2) (invFamily hn (k+1))
    m h hmax hn T hc
  have hxbar : x ∈ (geoTransformAlong (barMarked m) T).cosupp := by rwa [hB.2.2]
  obtain ⟨hreg,_⟩ := StepOneValueMasked.stepRegime_and_mem_cosupp_head m h.isWellFormed T hB.1 hxbar hsp
  have hlevel : level m (memberHeadAt m T x) (memberBasePointAt m T x)=s+1 := hreg.1.trans hs
  obtain ⟨hH,hQ⟩ := (isGeoTestTower_iff_head_tail (barMarked m) T
    (HironakaOriginalFrozenRecursiveLower.runAt m T x)).mp hB.1
  have hmask := (HironakaOriginalFrozenRecursiveLower.actual_lower_domain_and_cosupport_dictionary
    hn m h hmax T hc x hx hsp).1
  have hmaskA : memberBasePointAt m T x ∈ maskA m (memberHeadAt m T x) (memberBasePointAt m T x) := by
    change memberBasePointAt m T x ∈ lowerMask m (level m T x)
      (memberHeadAt m T x) (memberBasePointAt m T x) at hmask
    rw [hs] at hmask
    exact hmask
  refine ⟨s,hs,hmaskA,?_,?_,?_⟩
  · intro i
    have hprefix := (isGeoTestTower_iff_head_tail
      (geoTransformAlong (barMarked m) (memberHeadAt m T x)) (memberTailAt m T x) i).mp hQ |>.1
    have hd := (memberLowerExtension_tail_domain_and_mask_identity hn m h
      (memberHeadAt m T x) hH (memberBasePointAt m T x) hlevel
        (head (memberTailAt m T x) i) hprefix).1
    rw [show k+2-1=k+1 by omega] at hd
    exact hd
  · have hd := (memberLowerExtension_tail_domain_and_mask_identity hn m h
      (memberHeadAt m T x) hH (memberBasePointAt m T x) hlevel (memberTailAt m T x) hQ).1
    rw [show k+2-1=k+1 by omega] at hd
    exact hd
  · exact positive_member_mask_transform hn m h (memberHeadAt m T x) hH (memberBasePointAt m T x)
      (memberTailAt m T x) hQ (level m T x) hreg.1 hpos

/-- Actual whole nonmonomial ideal coherence at every computed ORIGINAL member prefix. -/
theorem isCoherent_actual_whole_member_prefix_nonmonomial_ideal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (hpos : 1 ≤ level m T x) (i : ℕ) :
    (nmPart (geoTransformAlong (wholeMemberAt m T x) (head (memberTailAt m T x) i))).IsCoherent := by
  obtain ⟨_,_,_,hD,_,_⟩ := actual_whole_member_history_and_mask hn m h hmax T hc x hx hsp hpos
  have hd := hD i
  exact isCoherent_nonmonomialPartAlong hn hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isSNCDivisor hd.isWellFormed.isTransverse hd.isWellFormed.isCoherent hd.isNonzeroAlongAt

/-- The SAME original whole member prefix's order equations on its true final manifold. -/
def wholeMemberPrefixOrderLocus (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) (i q : ℕ) : Set Y :=
  (tail (memberTailAt m T x) i).proj ⁻¹'
    ordGe (geoTransformAlong (wholeMemberAt m T x) (head (memberTailAt m T x) i)) q

/-- Actual original member controlled history gives genuine GLOBAL coherent order equations in ALLk. -/
theorem isComplexAnalyticSubset_actual_whole_member_prefix_order_locus (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (hpos : 1 ≤ level m T x) (i q : ℕ) :
    IsComplexAnalyticSubset (n := n) (wholeMemberPrefixOrderLocus m T x i q) := by
  obtain ⟨_,_,_,hD,_,_⟩ := actual_whole_member_history_and_mask hn m h hmax T hc x hx hsp hpos
  have hd := hD i
  have hcoh := isCoherent_actual_whole_member_prefix_nonmonomial_ideal hn m h hmax T hc x hx hsp hpos i
  apply AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail (memberTailAt m T x) i).contMDiff_proj
  cases q with
  | zero =>
    change IsComplexAnalyticSubset (n := n) (cosupport n _ _ 0)
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hd.isWellFormed.isClosedSubmanifold_N
  | succ q =>
    exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hcoh
      hd.isWellFormed.isClosedSubmanifold_N (Nat.succ_pos q)

/-- The SAME literal constructed lower first entry equals the actual unmasked whole member order. -/
theorem literal_lower_first_eq_whole_member_order (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (hpos : 1 ≤ level m T x) (z : HironakaOriginalFrozenRecursiveLower.patchAt m T x) :
    (ofLex ((invFamily hn (k+1)).inv (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
      (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x) z)).1 =
      nmOrd (geoTransformAlong (wholeMemberAt m T x) (memberTailAt m T x)) (z : Y) := by
  obtain ⟨_,_,_,_,hd,heq⟩ := actual_whole_member_history_and_mask hn m h hmax T hc x hx hsp hpos
  change nmOrd (geoTransformAlong (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
    (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x)) z = _
  rw [heq]
  exact NonmonomialOrderLocal.nmOrd_pullback_val hn hd.isWellFormed hd.isNonzeroAlongAt _ z

/-- Every literal masked lower first threshold is EXACTLY a whole genuine member-order trace. -/
theorem literal_lower_first_superlevel_eq_whole_member_trace (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (hpos : 1 ≤ level m T x) (q : ℕ) :
    {z : HironakaOriginalFrozenRecursiveLower.patchAt m T x |
      z ∈ (geoTransformAlong (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
        (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x)).N ∧
        q ≤ (ofLex ((invFamily hn (k+1)).inv (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
          (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x) z)).1} =
    (Subtype.val : HironakaOriginalFrozenRecursiveLower.patchAt m T x → Y) ⁻¹'
      ordGe (geoTransformAlong (wholeMemberAt m T x) (memberTailAt m T x)) q := by
  obtain ⟨_,_,_,_,hd,heq⟩ := actual_whole_member_history_and_mask hn m h hmax T hc x hx hsp hpos
  ext z
  rw [mem_ofPred_eq,literal_lower_first_eq_whole_member_order hn m h hmax T hc x hx hsp hpos z]
  have hcar : z ∈ (geoTransformAlong (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
        (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x)).N ↔
      (z : Y) ∈ (geoTransformAlong (wholeMemberAt m T x) (memberTailAt m T x)).N := by rw [heq]; rfl
  rw [hcar]
  constructor
  · rintro ⟨hz,hq⟩
    exact (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt hz q).mpr hq
  · intro hz
    have hzN := ordGe_subset_N _ q hz
    exact ⟨hzN,(mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt hzN q).mp hz⟩

/-- True actual globally analytic whole order loci present the SAME literal masked lower first threshold. -/
theorem isComplexAnalyticSubset_literal_lower_first_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (hpos : 1 ≤ level m T x) (q : ℕ) :
    IsComplexAnalyticSubset (n := n)
    {z : HironakaOriginalFrozenRecursiveLower.patchAt m T x |
      z ∈ (geoTransformAlong (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
        (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x)).N ∧
        q ≤ (ofLex ((invFamily hn (k+1)).inv (HironakaOriginalFrozenRecursiveLower.lowerAt m T x)
          (HironakaOriginalFrozenRecursiveLower.lowerTailAt m T x) z)).1} := by
  rw [literal_lower_first_superlevel_eq_whole_member_trace hn m h hmax T hc x hx hsp hpos q]
  apply AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val
  obtain ⟨_,_,_,_,hd,_⟩ := actual_whole_member_history_and_mask hn m h hmax T hc x hx hsp hpos
  have hcoh := isCoherent_nonmonomialPartAlong hn hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isSNCDivisor hd.isWellFormed.isTransverse hd.isWellFormed.isCoherent hd.isNonzeroAlongAt
  cases q with
  | zero =>
    change IsComplexAnalyticSubset (n := n) (cosupport n _ _ 0)
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hd.isWellFormed.isClosedSubmanifold_N
  | succ q =>
    exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hcoh
      hd.isWellFormed.isClosedSubmanifold_N (Nat.succ_pos q)

/-- ONLY original full positive inputs supply the entire genuine member-prefix analytic consumer. -/
theorem isComplexAnalyticSubset_original_companion_whole_member_prefix_order (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+2)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp)
    (hq : 1 ≤ HironakaOriginalFrozenCompanionPresentation.orderAt m T x)
    (hsp : ¬ IsSpecial (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
      (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)
      (HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq))
    (hpos : 1 ≤ level (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
      (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)
      (HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq)) (i q : ℕ) :
    IsComplexAnalyticSubset (n := n)
      (wholeMemberPrefixOrderLocus (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
        (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)
        (HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq) i q) := by
  let p := HironakaOriginalFrozenRecursiveLower.companionReferencePoint (k := k+1) hn m h T hc x hx hq
  obtain ⟨_,hK,hmax,hcanK,hdict⟩ :=
    HironakaOriginalFrozenCompanionPresentation.actual_frozen_companion_domain_and_cosupport (k := k+1) hn m h T hc x hx hq
  have hp : p ∈ (geoTransformAlong (HironakaOriginalFrozenCompanionPresentation.companionAt m T x)
    (HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x)).cosupp := (hdict p).mpr ⟨hx,rfl⟩
  exact isComplexAnalyticSubset_actual_whole_member_prefix_order_locus hn _ hK hmax _ hcanK p hp hsp hpos i q

end
end Hironaka.HironakaOriginalWholeMemberLowerAnalytic
