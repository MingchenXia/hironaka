/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberCompanionPositiveSpecialLoci
import Hironaka.Resolution.HironakaGeneralTwoCompanionCurveLoci

/-!
# Literal positive masked member companion values

Whole actual companion domains and open marked identities internally produce
special predicates and component-own discrete nonspecial exceptions. The
canonical value belongs to the original masked lower ideal; no whole member
candidate canonicality or maximum-order certificate is assumed.
Zero-order contact and whole General3/global G3 remain open.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberCompanionMaskedPositiveValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneMemberLowerOrderPredicates HironakaStepOneMemberCompanionHistoryExtension
  HironakaStepOneMemberCompanionPositiveSpecialLoci HironakaCoherentTransformExtension
  InvDomainMemberRestriction NonmonomialOrderLocal AnalyticDimensionBasics GlobalComponents
  HironakaCurveAnalyticPredicates NormalCrossings HomogenizedIdealAlong StepOneValue
  StepOneLowerDomain StepOneRegime NonmonomialOrderRegime InvDomainCompanion
  CompanionRebase CompanionReductionAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  CodimOnePartCanonical CodimOneSupportAlong MemberInterLocusAlong BoundaryCount GeneralValue
  BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail CanonicalCentres
  HironakaGeneralTwoCompanionCurveLoci HironakaDimensionTwoStepOneAnalyticSuperlevels
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem member_prefix_companion_entire_restrict_facts (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (U : Opens V) (q : ℕ) (hq : 1 ≤ q) :
    let C := memberPrefixCompanion m S H q
    let CU : MarkedIdeal n (CMfd.of (n := n) U) := companionOf n (MarkedIdeal.pullback (Subtype.val : U → V)
      (geoTransformAlong (memberRemainderMarked m S) H)) q
    ∀ p : openPreimage R U,
      (p ∈ (geoTransformAlong (barMarked CU) (restrict U R)).cosupp ↔
        (p : Y) ∈ (geoTransformAlong (barMarked C) R).cosupp) ∧
      level CU (restrict U R) p = level C R (p : Y) ∧
      (IsSpecial CU (restrict U R) p ↔ IsSpecial C R (p : Y)) := by
  dsimp only
  let I := geoTransformAlong (memberRemainderMarked m S) H
  let C := memberPrefixCompanion m S H q
  let CU : MarkedIdeal n (CMfd.of (n := n) U) := companionOf n (MarkedIdeal.pullback (Subtype.val : U → V) I) q
  let J := geoTransformAlong (barMarked C) R
  let W := openPreimage R U
  have hdI := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS H hH
  have hJ := (member_prefix_companion_entire_domains hn m h S hS H hH R hR q hq).2
  have hid := (member_prefix_companion_entire_open_identity hn m h S hS H hH R hR U q hq).2
  change geoTransformAlong (barMarked CU) (restrict U R) =
    MarkedIdeal.pullback (Subtype.val : W → Y) J at hid
  have hinit : CU = MarkedIdeal.pullback (Subtype.val : U → V) C :=
    (pullback_val_companionOf hn hdI.isWellFormed hdI.isNonzeroAlongAt U q).symm
  have hlen : CU.E.length = C.E.length := by
    rw [hinit]
    exact List.length_map _
  have hF : origMembers CU (restrict U R) =
      (origMembers C R).map ((Subtype.val : W → Y) ⁻¹' ·) := by
    unfold origMembers
    rw [hid, hlen]
    exact List.map_take.symm
  have hhol : ∀ y g, J.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hJ.isWellFormed.isCoherent hg
  have hcs : (MarkedIdeal.pullback (Subtype.val : W → Y) J).cosupp =
      (Subtype.val : W → Y) ⁻¹' J.cosupp := cosupp_pullback_val J hhol W
  have hc : CodimOneSupportAlong.codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : W → Y) J).N
      (MarkedIdeal.pullback (Subtype.val : W → Y) J).ideal (MarkedIdeal.pullback (Subtype.val : W → Y) J).d =
      (Subtype.val : W → Y) ⁻¹' CodimOneSupportAlong.codimOnePartAlong J.N J.ideal J.d :=
    codimOnePartAlong_pullback_val W hhol J.d
  intro p
  have hlev : level CU (restrict U R) p = level C R (p : Y) := by
    unfold level
    rw [hF]
    exact boundaryCount_map_preimage _ _ p
  have hm : p ∈ memberInterLocus (MarkedIdeal.pullback (Subtype.val : W → Y) J).N
      ((origMembers C R).map ((Subtype.val : W → Y) ⁻¹' ·))
      (MarkedIdeal.pullback (Subtype.val : W → Y) J).cosupp ↔
      (p : Y) ∈ memberInterLocus J.N (origMembers C R) J.cosupp := by
    rw [hcs]
    exact mem_memberInterLocus_preimage_iff Subtype.val
      (W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p) _ _ _
  refine ⟨?_, hlev, ?_⟩
  · rw [hid, hcs]
    rfl
  · unfold IsSpecial
    rw [hlev, hF, hid, hc]
    exact or_congr Iff.rfl (and_congr_right fun _ => hm)

theorem member_prefix_compAt_restrict_facts (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (q : ℕ) (hq : 1 ≤ q) :
    let U := NonmonomialOrderTail.ordMask (geoTransformAlong (memberRemainderMarked m S) H) q
    ∀ p : openPreimage R U,
      (p ∈ (geoTransformAlong (barMarked (compAt (memberRemainderMarked m S) q H))
        (restrict U R)).cosupp ↔
        (p : Y) ∈ (geoTransformAlong (memberPrefixCoefficientCompanion m S H q) R).cosupp) ∧
      level (compAt (memberRemainderMarked m S) q H) (restrict U R) p =
        level (memberPrefixCompanion m S H q) R (p : Y) ∧
      (IsSpecial (compAt (memberRemainderMarked m S) q H) (restrict U R) p ↔
        IsSpecial (memberPrefixCompanion m S H q) R (p : Y)) :=
  member_prefix_companion_entire_restrict_facts hn m h S hS H hH R hR _ q hq

theorem exists_analytic_dimzero_member_companion_nonspecial_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧
      E ⊆ (geoTransformAlong (memberPrefixCoefficientCompanion m S H q) R).cosupp ∧
      ∀ z ∈ (geoTransformAlong (memberPrefixCoefficientCompanion m S H q) R).cosupp \ E,
        IsSpecial (memberPrefixCompanion m S H q) R z :=
  exists_analytic_dimzero_stage_special_exception hn
    (member_prefix_companion_entire_domains hn m h S hS H hH R hR q hq).2
    (origMembers (memberPrefixCompanion m S H q) R) (fun _ hh => List.mem_of_mem_take hh)

private theorem memberCompanionPositiveHistory_mono (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) (Z E F : Set Y)
    (h : memberCompanionPositiveHistory m S T Z E) (hEF : E ⊆ F) :
    memberCompanionPositiveHistory m S T Z F := by
  intro B hB
  obtain ⟨q, hatt, hmin, hord, hrun, hpos⟩ := h B hB
  have hm : B \ F ⊆ B \ E := fun x hx => ⟨hx.1, fun he => hx.2 (hEF he)⟩
  exact ⟨q, hatt, hmin, fun x hx => hord x (hm hx),
    fun x hx y hy => hrun x (hm hx) y (hm hy),
    fun hq x hx y hy => hpos hq x (hm hx) y (hm hy)⟩

theorem exists_analytic_dimzero_member_companion_special_history (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hsub : Z ⊆ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      memberCompanionPositiveHistory m S T Z E ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ q : ℕ,
        (∃ x ∈ B, nmOrd (geoTransformAlong (memberRemainderMarked m S) T) x = q) →
        (∀ x ∈ B, q ≤ nmOrd (geoTransformAlong (memberRemainderMarked m S) T) x) →
        1 ≤ q → ∀ i : Fin (T.length+1), ∀ z ∈ B \ E,
          z ∈ (geoTransformAlong (memberPrefixCoefficientCompanion m S (head T i) q) (tail T i)).cosupp →
          IsSpecial (memberPrefixCompanion m S (head T i) q) (tail T i) z := by
  classical
  obtain ⟨Eo, hEo, hdEo, hEoZ, hhist⟩ := exists_analytic_dimzero_member_companion_positive_history
    hn m h S hS T hT hZ hdim hsub
  choose qB hmin using (fun B : globalComponents (n := n) Z => hhist B.1 B.2)
  have hi : ∀ i : Fin (T.length+1), ∀ B : globalComponents (n := n) Z,
      ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ (B : Set Y) ∧
        (1 ≤ qB B → ∀ z ∈ (B : Set Y) \ E,
          z ∈ (geoTransformAlong (memberPrefixCoefficientCompanion m S (head T i) (qB B)) (tail T i)).cosupp →
          IsSpecial (memberPrefixCompanion m S (head T i) (qB B)) (tail T i) z) := by
    intro i B
    by_cases hq : 1 ≤ qB B
    · obtain ⟨Et, hEt, hdEt, hEtC, hsp⟩ := exists_analytic_dimzero_member_companion_nonspecial_exception
        hn m h S hS (head T i) ((isGeoTestTower_iff_head_tail m T i).mp hT).1
        (tail T i) ((isGeoTestTower_iff_head_tail m T i).mp hT).2 (qB B) hq
      have hBa := (isComplexAnalyticallyIrreducible_of_mem_globalComponents hZ B.2).1
      refine ⟨(B : Set Y) ∩ Et, hBa.inter hEt,
        DimensionMonotone.DimLE.anti hEt inter_subset_right hdEt, inter_subset_left, ?_⟩
      intro _ z hz hzc
      exact hsp z ⟨hzc, fun hh => hz.2 ⟨hz.1, hh⟩⟩
    · exact ⟨∅, by simp, by intro z k hz; exact hz.2.1.elim,
        empty_subset _, fun hh => (hq hh).elim⟩
  choose e he using hi
  have hlf : ∀ i, LocallyFinite (e i) := fun i =>
    (locallyFinite_globalComponents hZ).subset (fun B => (he i B).2.2.1)
  let Ei : Fin (T.length+1) → Set Y := fun i => ⋃ B : globalComponents (n := n) Z, e i B
  have hEi : ∀ i, IsComplexAnalyticSubset (n := n) (Ei i) ∧ DimLE (n := n) (Ei i) 0 :=
    fun i => analytic_dimzero_iUnion_of_locallyFinite (e i) (hlf i)
      (fun B => (he i B).1) (fun B => (he i B).2.1)
  let Es := ⋃ i, Ei i
  obtain ⟨hEs, hdEs⟩ := analytic_dimzero_iUnion_of_locallyFinite Ei (locallyFinite_of_finite Ei)
    (fun i => (hEi i).1) (fun i => (hEi i).2)
  have hEsZ : Es ⊆ Z := by
    intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    change z ∈ ⋃ B : globalComponents (n := n) Z, e i B at hzi
    obtain ⟨B, hzB⟩ := mem_iUnion.mp hzi
    exact subset_of_mem_globalComponents hZ B.2 ((he i B).2.2.1 hzB)
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEo hdEo hEs hdEs
  refine ⟨Eo ∪ Es, hE, hdE, union_subset hEoZ hEsZ,
    memberCompanionPositiveHistory_mono m S T Z Eo (Eo ∪ Es) hhist subset_union_left, ?_⟩
  intro B hB q hatt hminq hq i z hz hzc
  let b : globalComponents (n := n) Z := ⟨B,hB⟩
  have heq : q = qB b := by
    obtain ⟨x, hx, hxo⟩ := hatt
    obtain ⟨y, hy, hyo⟩ := (hmin b).1
    apply Nat.le_antisymm
    · exact hyo ▸ hminq y hy
    · exact hxo ▸ (hmin b).2.1 x hx
  subst q
  apply (he i b).2.2.2 hq z ⟨hz.1, ?_⟩ hzc
  intro hze
  exact hz.2 (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨b,hze⟩⟩))

private def CoherentAlong (J : MarkedIdeal n X) : ∀ {V : CMfd.{u} n}, BlowupTower X V → Prop
  | _, .refl => J.ideal.IsCoherent
  | _, T@(.step R _ _ _) => CoherentAlong J R ∧ (geoTransformAlong J T).ideal.IsCoherent

private theorem coherentAlong_last (J : MarkedIdeal n X) :
    ∀ {V : CMfd.{u} n} (T : BlowupTower X V), CoherentAlong J T → (geoTransformAlong J T).ideal.IsCoherent
  | _, .refl, h => h
  | _, .step _ _ _ _, h => h.2

private theorem coherentAlong_restrict (J : MarkedIdeal n X) (U : Opens X) :
    ∀ {V : CMfd.{u} n} (T : BlowupTower X V), CoherentAlong J T →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T U → V) (geoTransformAlong J T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, h => by
    have hc := coherentAlong_last J T h.1
    have ih := coherentAlong_restrict J U T h.1
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T)).geoTransform
      ((Subtype.val : openPreimage T U → _) ⁻¹' C) _ = _
    rw [ih]
    exact geoTransform_pullback_val hc hπ h.2 (openPreimage T U) _

private theorem coherentAlong_iso {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (J : MarkedIdeal n X)
    {V' V : CMfd.{u} n} {T' : BlowupTower X' V'} {T : BlowupTower X V}
    {χ : V' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V}
    (hiso : IsTowerIso Φ T' T χ) : CoherentAlong J T →
    geoTransformAlong (MarkedIdeal.pullback Φ J) T' = MarkedIdeal.pullback χ (geoTransformAlong J T) ∧
      CoherentAlong (MarkedIdeal.pullback Φ J) T' := by
  induction hiso with
  | refl =>
    intro hc
    exact ⟨rfl, GermIdealPullbackCalculus.isCoherent_pullback Φ.contMDiff hc⟩
  | @step V' V W' W T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hc
    have hbefore := coherentAlong_last J T hc.1
    obtain ⟨hprev, hprevcoh⟩ := ih hc.1
    have hfun : π' = χ.symm ∘ (π ∘ χ₁) := funext fun p => by simp [hcomm]
    have hg : geoTransformAlong (MarkedIdeal.pullback Φ J) (.step T' C' π' hπ') =
        MarkedIdeal.pullback χ₁ (geoTransformAlong J (.step T C π hπ)) := by
      subst hC hfun
      change (geoTransformAlong (MarkedIdeal.pullback Φ J) T').geoTransform
        (χ ⁻¹' C) (χ.symm ∘ (π ∘ χ₁)) = MarkedIdeal.pullback χ₁ ((geoTransformAlong J T).geoTransform C π)
      rw [hprev, MarkedIdeal.geoTransform_pullback χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply
        χ.symm_apply_apply _ hbefore C (hπ.contMDiff.comp χ₁.contMDiff)]
      exact BlowupBiholomorphismLift.geoTransform_comp_diffeo χ₁ _ hbefore C
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1) hπ.contMDiff hc.2
    refine ⟨hg, hprevcoh, ?_⟩
    rw [hg]
    exact GermIdealPullbackCalculus.isCoherent_pullback χ₁.contMDiff hc.2

private theorem member_companion_restrict_coherentAlong (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (U : Opens V) (q : ℕ) (hq : 1 ≤ q) :
    ∀ {W : CMfd.{u} n} (R : BlowupTower V W), IsGeoTestTower (geoTransformAlong m H) R →
      CoherentAlong
        (barMarked (X := CMfd.of (n := n) U)
          (companionOf n (MarkedIdeal.pullback (Subtype.val : U → V)
            (geoTransformAlong (memberRemainderMarked m S) H)) q)) (restrict U R) := by
  intro W R
  induction R with
  | refl =>
    intro hR
    have hid := (member_prefix_companion_entire_open_identity hn m h S hS H hH .refl hR U q hq).2
    have hd := (member_prefix_companion_entire_domains hn m h S hS H hH .refl hR q hq).2
    change (geoTransformAlong (barMarked (X := CMfd.of (n := n) U)
      (companionOf n (MarkedIdeal.pullback (Subtype.val : U → V)
        (geoTransformAlong (memberRemainderMarked m S) H)) q)) (restrict U .refl)).ideal.IsCoherent
    rw [hid]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hd.isWellFormed.isCoherent
  | step R C π hπ ih =>
    intro hR
    have hid := (member_prefix_companion_entire_open_identity hn m h S hS H hH (.step R C π hπ) hR U q hq).2
    have hd := (member_prefix_companion_entire_domains hn m h S hS H hH (.step R C π hπ) hR q hq).2
    refine ⟨ih hR.1, ?_⟩
    change (geoTransformAlong _ (restrict U (.step R C π hπ))).ideal.IsCoherent
    rw [hid]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hd.isWellFormed.isCoherent

private theorem coherentAlong_open_facts (C : MarkedIdeal n X) (hwf : C.IsWellFormed)
    (hd : 1 ≤ C.d) (T : BlowupTower X Y) (hc : CoherentAlong (barMarked C) T) (U : Opens X)
    (p : openPreimage T U) :
    (p ∈ (geoTransformAlong (barMarked (MarkedIdeal.pullback (Subtype.val : U → X) C)) (restrict U T)).cosupp ↔
      (p : Y) ∈ (geoTransformAlong (barMarked C) T).cosupp) ∧
    level (MarkedIdeal.pullback (Subtype.val : U → X) C) (restrict U T) p = level C T (p : Y) ∧
    (IsSpecial (MarkedIdeal.pullback (Subtype.val : U → X) C) (restrict U T) p ↔ IsSpecial C T (p : Y)) := by
  let CU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) C
  let J := geoTransformAlong (barMarked C) T
  let W := openPreimage T U
  have hbar : barMarked CU = MarkedIdeal.pullback (Subtype.val : U → X) (barMarked C) :=
    ContactStageKept.barMarked_pullback_val U hwf.isCoherent hwf.isClosedSubmanifold_N hd
  have hid : geoTransformAlong (barMarked CU) (restrict U T) =
      MarkedIdeal.pullback (Subtype.val : W → Y) J := by
    rw [hbar]
    exact coherentAlong_restrict (barMarked C) U T hc
  have hlen : CU.E.length = C.E.length := List.length_map _
  have hF : origMembers CU (restrict U T) = (origMembers C T).map ((Subtype.val : W → Y) ⁻¹' ·) := by
    unfold origMembers
    rw [hid, hlen]
    exact List.map_take.symm
  have hhol : ∀ y g, J.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (coherentAlong_last (barMarked C) T hc) hg
  have hcs := cosupp_pullback_val J hhol W
  have hcpart : codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : W → Y) J).N
      (MarkedIdeal.pullback (Subtype.val : W → Y) J).ideal (MarkedIdeal.pullback (Subtype.val : W → Y) J).d =
      (Subtype.val : W → Y) ⁻¹' codimOnePartAlong J.N J.ideal J.d := codimOnePartAlong_pullback_val W hhol J.d
  have hl : level CU (restrict U T) p = level C T (p : Y) := by
    unfold level
    rw [hF]
    exact boundaryCount_map_preimage _ _ p
  have hm : p ∈ memberInterLocus (MarkedIdeal.pullback (Subtype.val : W → Y) J).N
      ((origMembers C T).map ((Subtype.val : W → Y) ⁻¹' ·))
      (MarkedIdeal.pullback (Subtype.val : W → Y) J).cosupp ↔
      (p : Y) ∈ memberInterLocus J.N (origMembers C T) J.cosupp := by
    rw [hcs]
    exact mem_memberInterLocus_preimage_iff Subtype.val
      (W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p) _ _ _
  refine ⟨?_, hl, ?_⟩
  · rw [hid, hcs]; rfl
  unfold IsSpecial
  rw [hl, hF, hid, hcpart]
  exact or_congr Iff.rfl (and_congr_right fun _ => hm)

private theorem coherentAlong_iso_facts {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (C : MarkedIdeal n X) (hwf : C.IsWellFormed) (hd : 1 ≤ C.d)
    {V' : CMfd.{u} n} {T' : BlowupTower X' V'} {T : BlowupTower X Y}
    {χ : V' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hc : CoherentAlong (barMarked C) T) :
    CoherentAlong (barMarked (MarkedIdeal.pullback Φ C)) T' ∧
      ∀ p, (p ∈ (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ C)) T').cosupp ↔
        χ p ∈ (geoTransformAlong (barMarked C) T).cosupp) ∧
        level (MarkedIdeal.pullback Φ C) T' p = level C T (χ p) ∧
        (IsSpecial (MarkedIdeal.pullback Φ C) T' p ↔ IsSpecial C T (χ p)) := by
  have hbar : barMarked (MarkedIdeal.pullback Φ C) = MarkedIdeal.pullback Φ (barMarked C) :=
    ContactStageKept.barMarked_pullback Φ hwf.isCoherent hwf.isClosedSubmanifold_N hd
  obtain ⟨hg, hc'⟩ := coherentAlong_iso Φ (barMarked C) hiso hc
  have hid : geoTransformAlong (barMarked (MarkedIdeal.pullback Φ C)) T' =
      MarkedIdeal.pullback χ (geoTransformAlong (barMarked C) T) := by rw [hbar]; exact hg
  have hF : origMembers (MarkedIdeal.pullback Φ C) T' = (origMembers C T).map ((χ : V' → Y) ⁻¹' ·) := by
    unfold origMembers
    rw [hid]
    change List.take ((C.E.map ((Φ : X' → X) ⁻¹' ·)).length)
      ((geoTransformAlong (barMarked C) T).E.map ((χ : V' → Y) ⁻¹' ·)) = _
    rw [List.length_map]
    exact List.map_take.symm
  refine ⟨by rw [hbar]; exact hc', ?_⟩
  intro p
  let J := geoTransformAlong (barMarked C) T
  have hhol : ∀ y g, J.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (coherentAlong_last (barMarked C) T hc) hg
  have hcs : (MarkedIdeal.pullback χ J).cosupp = χ ⁻¹' J.cosupp :=
    MarkedIdealTowerTransport.cosupp_pullback_eq (coherentAlong_last (barMarked C) T hc)
  have hcp := codimOnePartAlong_pullback χ (N := J.N) hhol J.d
  have hm := memberInterLocus_preimage (χ : V' → Y) (fun z => χ.toHomeomorph.map_nhds_eq z)
    J.N (origMembers C T) J.cosupp
  have hl : level (MarkedIdeal.pullback Φ C) T' p = level C T (χ p) := by
    unfold level
    rw [hF]
    exact boundaryCount_map_preimage _ _ p
  refine ⟨?_, hl, ?_⟩
  · rw [hid, hcs]; rfl
  unfold IsSpecial
  rw [hl, hF, hid]
  refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
  · rw [show codimOnePartAlong (MarkedIdeal.pullback χ J).N (MarkedIdeal.pullback χ J).ideal
      (MarkedIdeal.pullback χ J).d = _ from hcp]
    rfl
  · change p ∈ memberInterLocus ((χ : V' → Y) ⁻¹' J.N)
      ((origMembers C T).map ((χ : V' → Y) ⁻¹' ·)) (MarkedIdeal.pullback χ J).cosupp ↔ _
    rw [hcs, hm]
    rfl

private theorem member_masked_literal_compAt_facts (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (U : Opens X)
    (hTU : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S)) (restrict U T))
    (q : ℕ) (hq : 1 ≤ q) (i : ℕ) :
    let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S)
    let H := head (restrict U T) i
    let R := tail (restrict U T) i
    let W := NonmonomialOrderTail.ordMask (geoTransformAlong L H) q
    ∀ p : openPreimage R W,
      (p ∈ (geoTransformAlong (barMarked (compAt L q H)) (restrict W R)).cosupp ↔
        ((p : openPreimage T U) : Y) ∈
          (geoTransformAlong (memberPrefixCoefficientCompanion m S (head T i) q) (tail T i)).cosupp) ∧
      level (compAt L q H) (restrict W R) p =
        level (memberPrefixCompanion m S (head T i) q) (tail T i) ((p : openPreimage T U) : Y) ∧
      (IsSpecial (compAt L q H) (restrict W R) p ↔
        IsSpecial (memberPrefixCompanion m S (head T i) q) (tail T i) ((p : openPreimage T U) : Y)) := by
  dsimp only
  let I := memberRemainderMarked m S
  let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) I
  let TU := restrict U T
  let HU := head TU i
  let RU := tail TU i
  let Ui := openPreimage (head T i) U
  let IR := geoTransformAlong L (restrict U (head T i))
  let IA := geoTransformAlong L HU
  let CR := companionOf n IR q
  let CA := companionOf n IA q
  let W := NonmonomialOrderTail.ordMask IA q
  have hdI := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS .refl (by trivial)
  have hdL : IsInvDomain 2 L := InvDomainTowerAlong.isInvDomain_pullback_val U hdI
  obtain ⟨χ₀, h₀, h₁⟩ := exists_isTowerIso_split_restrict U T i
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) L = L :=
    ContactCanonicalAlong.pullback_id _ hdL.isWellFormed.isCoherent
  have hHA : IsGeoTestTower L HU := ((isGeoTestTower_iff_head_tail L TU i).mp hTU).1
  have hHR : IsGeoTestTower L (restrict U (head T i)) := by
    apply (IsTowerIso.isGeoTestTower_iff _ hdL.isWellFormed.isClosedSubmanifold_N hdL.isWellFormed.isCoherent h₀).mp
    rwa [hpb]
  have hdIR : IsInvDomain 2 IR := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdL _ hHR
  have hdIA : IsInvDomain 2 IA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdL _ hHA
  have hdCR : IsInvDomain 2 CR := isInvDomain_companionAlong hn hdIR hq
  have hdCA : IsInvDomain 2 CA := isInvDomain_companionAlong hn hdIA hq
  have hIA : IA = MarkedIdeal.pullback χ₀ IR := by
    have hh := IsTowerIso.geoTransformAlong_eq _ hdL.isWellFormed.isClosedSubmanifold_N hdL.isWellFormed.isCoherent h₀ hHR
    rwa [hpb] at hh
  have hCA : CA = MarkedIdeal.pullback χ₀ CR := by
    dsimp only [CA]
    rw [hIA]
    exact (pullback_diffeo_companionOf hn χ₀ hdIR.isWellFormed hdIR.isNonzeroAlongAt q).symm
  have hsplit := (isGeoTestTower_iff_head_tail m T i).mp hT
  have hIR : IR = MarkedIdeal.pullback (Subtype.val : Ui → (split T i).1) (geoTransformAlong I (head T i)) :=
    geoTransformAlong_restrict_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS U (head T i) hsplit.1
  have hCR : CR = companionOf n (MarkedIdeal.pullback (Subtype.val : Ui → (split T i).1)
      (geoTransformAlong I (head T i))) q := by dsimp only [CR]; rw [hIR]
  have hcR : CoherentAlong (barMarked CR) (restrict Ui (tail T i)) := by
    rw [hCR]
    exact member_companion_restrict_coherentAlong hn m h S hS (head T i) hsplit.1 Ui q hq (tail T i) hsplit.2
  obtain ⟨hcA, hisof⟩ := coherentAlong_iso_facts χ₀ CR hdCR.isWellFormed hdCR.one_le_d h₁ hcR
  rw [← hCA] at hcA hisof
  have hcomp : compAt L q HU = MarkedIdeal.pullback (Subtype.val : W → (split TU i).1) CA :=
    (pullback_val_companionOf hn hdIA.isWellFormed hdIA.isNonzeroAlongAt W q).symm
  intro p
  have hf := coherentAlong_open_facts CA hdCA.isWellFormed hdCA.one_le_d RU hcA W p
  have hi := hisof (p : openPreimage T U)
  have hw := member_prefix_companion_entire_restrict_facts hn m h S hS (head T i) hsplit.1
    (tail T i) hsplit.2 Ui q hq ((opensCongr (n := n) (openPreimage_head_tail U T i)) (p : openPreimage T U))
  rw [← hCR] at hw
  rw [hcomp]
  exact ⟨hf.1.trans (hi.1.trans hw.1), hf.2.1.trans (hi.2.1.trans hw.2.1),
    hf.2.2.trans (hi.2.2.trans hw.2.2)⟩

private theorem split_zero {V : CMfd.{u} n} (T : BlowupTower X V) :
    split T 0 = ⟨V, T, .refl⟩ := by cases T <;> rfl

def memberMaskedPositiveValues (hn : 0 < n) (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) (U : Opens X) (Z E : Set Y) : Prop :=
  let I := memberRemainderMarked m S
  let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) I
  ∀ B ∈ globalComponents (n := n) Z, ∀ q : ℕ,
        (∃ x ∈ B, nmOrd (geoTransformAlong I T) x = q) →
        (∀ x ∈ B, q ≤ nmOrd (geoTransformAlong I T) x) → 1 ≤ q →
        (∀ z : openPreimage T U, (z : Y) ∈ B \ E → z ∈ (geoTransformAlong L (restrict U T)).cosupp →
          let r := regimeRun (OrdRegime I q) T (z : Y)
          (invFamily hn 2).inv L (restrict U T) z =
            toLex (q, toLex (Sum.inr ((toLex (level (memberPrefixCompanion m S (head T r) q) (tail T r) (z : Y),
              (⊤ : WithTop (ValTy 1))) : ℕ ×ₗ WithTop (ValTy 1)) : WithTop (ℕ ×ₗ WithTop (ValTy 1)))))) ∧
        ∀ z : openPreimage T U, (z : Y) ∈ B \ E → z ∈ (geoTransformAlong L (restrict U T)).cosupp →
          ∀ w : openPreimage T U, (w : Y) ∈ B \ E → w ∈ (geoTransformAlong L (restrict U T)).cosupp →
          (invFamily hn 2).inv L (restrict U T) z = (invFamily hn 2).inv L (restrict U T) w ∧
            ∀ β : ValTy 2, (β ≤ (invFamily hn 2).inv L (restrict U T) z ↔
              β ≤ (invFamily hn 2).inv L (restrict U T) w)

theorem exists_analytic_dimzero_member_masked_positive_values (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (U : Opens X)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S))
      ((invFamily hn 2).inv (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S))) (restrict U T))
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hsub : Z ⊆ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      memberCompanionPositiveHistory m S T Z E ∧
      memberMaskedPositiveValues hn m S T U Z E := by
  dsimp only [memberMaskedPositiveValues]
  let I := memberRemainderMarked m S
  let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) I
  let TU := restrict U T
  have hdI := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS .refl (by trivial)
  have hdL : IsInvDomain 2 L := InvDomainTowerAlong.isInvDomain_pullback_val U hdI
  have hTU := (invFamily hn 2).isInvValue.isGeoTestTower_of_isCanonical hdL TU hcan
  have hdIT := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS T hT
  have hmaskEq := geoTransformAlong_restrict_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS U T hT
  obtain ⟨E, hE, hdE, hEZ, hhist, hspecial⟩ := exists_analytic_dimzero_member_companion_special_history
    hn m h S hS T hT hZ hdim hsub
  refine ⟨E, hE, hdE, hEZ, hhist, ?_⟩
  intro B hB q hatt hmin hq
  obtain ⟨q', hatt', hmin', hord, hruns, hcounts⟩ := hhist B hB
  have hqq : q' = q := by
    obtain ⟨x, hx, hxo⟩ := hatt
    obtain ⟨y, hy, hyo⟩ := hatt'
    exact Nat.le_antisymm (hxo ▸ hmin' x hx) (hyo ▸ hmin y hy)
  subst q'
  let R := invFamily hn 1
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM R J S z
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := 2) R hn
  have hcanG : IsCanonical L (genInv lower L) TU := hcan
  have hD := GeneralCanonicalTail.hasGenLowerData_of_isCanonical lower hM hn hdL TU hTU hcanG
  have hval : ∀ z : openPreimage T U, (z : Y) ∈ B \ E → z ∈ (geoTransformAlong L TU).cosupp →
      let r := regimeRun (OrdRegime I q) T (z : Y)
      (invFamily hn 2).inv L TU z =
        toLex (q, toLex (Sum.inr ((toLex (level (memberPrefixCompanion m S (head T r) q) (tail T r) (z : Y),
          (⊤ : WithTop (ValTy 1))) : ℕ ×ₗ WithTop (ValTy 1)) : WithTop (ℕ ×ₗ WithTop (ValTy 1))))) := by
    intro z hzB hzcs
    dsimp only
    have hzq : nmOrd (geoTransformAlong L TU) z = q := by
      rw [hmaskEq]
      exact (nmOrd_pullback_val hn hdIT.isWellFormed hdIT.isNonzeroAlongAt _ z).trans (hord z hzB)
    have hr : regimeRun (OrdRegime L q) TU z = regimeRun (OrdRegime I q) T (z : Y) :=
      regimeRun_memberRemainder_restrict hn m h S hS U T hT q z
    let r := regimeRun (OrdRegime I q) T (z : Y)
    let rf : Fin (T.length+1) := ⟨r, Nat.lt_succ_of_le (regimeRun_le_length _ T (z : Y))⟩
    have hD' : GenLowerData lower 2 L q (head TU r) (tail TU r) z := by
      exact Eq.mp (congrArg (fun i : ℕ => GenLowerData lower 2 L q (head TU i) (tail TU i) z) hr)
        (hD z hzcs q hzq hq)
    obtain ⟨hmask, hK, hmax, hcanK, hcosK⟩ := hD' 
    let p : openPreimage (tail TU r) (NonmonomialOrderTail.ordMask (geoTransformAlong L (head TU r)) q) := ⟨z,hmask⟩
    have hpbar : p ∈ (geoTransformAlong (barMarked (compAt L q (head TU r)))
        (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong L (head TU r)) q) (tail TU r))).cosupp := by
      rw [(Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 2) R (compAt L q (head TU r))
        hK hmax hn _ hcanK).2.2]
      exact hcosK
    have hf := member_masked_literal_compAt_facts hn m h S hS T hT U hTU q hq r p
    have hspW := hspecial B hB q hatt hmin hq rf (z : Y) hzB (hf.1.mp hpbar)
    have hsp := hf.2.2.mpr hspW
    have hlower : Seq.StepOneValueMasked.stepOneInvM R (compAt L q (head TU r))
        (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong L (head TU r)) q) (tail TU r)) p =
        toLex (level (memberPrefixCompanion m S (head T r) q) (tail T r) (z : Y),
          (⊤ : WithTop (ValTy 1))) :=
      (Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R _ _ _ hsp).trans
      (congrArg (fun a : ℕ => toLex (a, (⊤ : WithTop (ValTy 1)))) hf.2.1)
    change genInv lower L TU z = _
    rw [genInv_of_nmOrd_ne_zero lower L TU hzq (by omega), hr, genLowerValue_eq_of_mem lower L hmask]
    let embed : (ℕ ×ₗ WithTop (ValTy 1)) → ValTy 2 := fun v =>
      toLex (q, toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy 1)))))
    exact congrArg embed hlower
  refine ⟨hval, ?_⟩
  intro z hzB hzcs w hwB hwcs
  have hr := hruns (z : Y) hzB (w : Y) hwB q
  let r := regimeRun (OrdRegime I q) T (z : Y)
  let rf : Fin (T.length+1) := ⟨r, Nat.lt_succ_of_le (regimeRun_le_length _ T (z : Y))⟩
  have hcount := ((hcounts hq (z : Y) hzB (w : Y) hwB rf).1 (0 : Fin (T.length+1))).1
  simp only [Fin.val_zero, head, tail] at hcount
  rw [split_zero] at hcount
  change level (memberPrefixCompanion m S (head T r) q) (tail T r) (z : Y) =
    level (memberPrefixCompanion m S (head T r) q) (tail T r) (w : Y) at hcount
  have heq : (invFamily hn 2).inv L TU z = (invFamily hn 2).inv L TU w := by
    rw [hval z hzB hzcs, hval w hwB hwcs, ← hr]
    exact congrArg (fun a : ℕ => toLex (q, toLex (Sum.inr ((toLex (a, (⊤ : WithTop (ValTy 1))) :
      ℕ ×ₗ WithTop (ValTy 1)) : WithTop (ℕ ×ₗ WithTop (ValTy 1)))))) hcount
  exact ⟨heq, fun β => by rw [heq]⟩

private theorem positive_actual_lower_isCanonical (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcanK : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hnsp : ¬ IsSpecial K R p)
    (s : ℕ) (hs : level K R p = s+1) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    IsCanonical (lowerMarked K (s+1) H p₀)
      ((invFamily hn 2).inv (lowerMarked K (s+1) H p₀)) (restrict (maskA K H p₀) Q) := by
  dsimp only
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  obtain ⟨_, _, hcanL, _⟩ := HironakaDimensionThreeStepOneLowerAnalyticLoci.actual_lower_domain_and_cosupport_dictionary
    hn K hK hmax R hcanK p hp hnsp
  change IsCanonical (StepOneValueMasked.lowerMarkedM K (level K R p) H p₀)
    ((invFamily hn 2).inv (StepOneValueMasked.lowerMarkedM K (level K R p) H p₀))
    (restrict (StepOneValue.lowerMask K (level K R p) H p₀) Q) at hcanL
  exact Eq.mp (congrArg (fun a : ℕ =>
    IsCanonical (StepOneValueMasked.lowerMarkedM K a H p₀)
      ((invFamily hn 2).inv (StepOneValueMasked.lowerMarkedM K a H p₀))
      (restrict (StepOneValue.lowerMask K a H p₀) Q)) hs) hcanL

open HironakaGeneralThreeNonspecialAnalyticLoci

theorem exists_actual_general_three_member_masked_positive_values (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hpos : 1 ≤ level (companionAt m T x) (companionTailAt m T x) p) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let J₀ := geoTransformAlong (barMarked K) H
    let S := membersThrough J₀.E (origMembers K H) p₀
    let I := memberRemainderMarked J₀ S
    let U := maskA K H p₀
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ U ∧
      ∃ A E : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) A ∧ DimLE (n := n) A 1 ∧
        A ⊆ (geoTransformAlong I Q).N ∧ p ∈ A ∧
        IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ A ∧
        memberCompanionPositiveHistory J₀ S Q A E ∧
        MarkedIdeal.pullback (Subtype.val : U → (split R r).1) I = lowerMarked K (s+1) H p₀ ∧
        memberMaskedPositiveValues hn J₀ S Q U A E := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let J₀ := geoTransformAlong (barMarked K) H
  let S := membersThrough J₀.E (origMembers K H) p₀
  let I := memberRemainderMarked J₀ S
  let U := maskA K H p₀
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcanK
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  obtain ⟨s, hs, hmask, _, A, hA, hdA, hsubA, hpA⟩ := exists_actual_companion_member_history_curve
    hn m h T hcan x hx hq p hp hnsp hpos
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hnsp).1
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  have hdJ₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_barMarked K hK) H hhead
  have hE₀ : ∀ W ∈ origMembers K H, W ∈ J₀.E := fun W hW => List.mem_of_mem_take hW
  have hS : S.Nonempty := membersThrough_nonempty hE₀ (by change 1 ≤ level K H p₀; rw [hl]; omega)
  have hLinit : MarkedIdeal.pullback (Subtype.val : U → (split R r).1) I = lowerMarked K (s+1) H p₀ :=
    pullback_memberLowerExtension_eq_lowerMarked_succ hn K hK.isWellFormed H hhead p₀ hl
  have hcanU : IsCanonical (MarkedIdeal.pullback (Subtype.val : U → (split R r).1) I)
      ((invFamily hn 2).inv (MarkedIdeal.pullback (Subtype.val : U → (split R r).1) I)) (restrict U Q) := by
    rw [hLinit]
    exact positive_actual_lower_isCanonical hn K hK hmax R hcanK p hp hnsp s hs
  obtain ⟨E, hE, hdE, hEA, hhist, hvalues⟩ := exists_analytic_dimzero_member_masked_positive_values
    hn J₀ hdJ₀ S hS Q htail U hcanU hA hdA hsubA
  exact ⟨s, hs, hmask, A, E, hA, hdA, hsubA, hpA, hE, hdE, hEA, hhist, hLinit, hvalues⟩

end
end Hironaka.HironakaStepOneMemberCompanionMaskedPositiveValues
