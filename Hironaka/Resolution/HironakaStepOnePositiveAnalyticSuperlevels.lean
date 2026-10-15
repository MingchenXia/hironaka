/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberAcrossMaskValues
import Hironaka.Resolution.HironakaGeneralTwoAnalyticSuperlevels

/-! # Entire ambient positive-first-entry superlevels of actual Step1

Actual canonical bridges, genuine finite top predicates and true across-mask
values produce one analytic dimension-zero curve exception for ALL positive
thresholds. Actual USC closedness fills genuine locally finite components;
the real analytic top baseline gives the ENTIRE ambient superlevel. The
original invFamily3 consumer internally constructs the same true companion,
canonical Step1 tail and analytic curve. No caller values/closedness certificate.
Original Step1 first-entry-zero contact, whole General3 and global G3 remain OPEN.
Blueprint: hironaka-step-one-positive-analytic-superlevels-extension.tex.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOnePositiveAnalyticSuperlevels
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  StepOneValue StepOneLowerDomain StepOneRegime HomogenizedIdealAlong
  GlobalComponents AnalyticDimensionBasics CodimOneSupportAlong
  HironakaStepOneMemberAcrossMaskValues HironakaStepOneMemberHeadIncidence
  HironakaStepOneCurveHistoryPredicates HironakaCurveAnalyticPredicates
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  HironakaGeneralTwoAnalyticSuperlevels CanonicalCentres
  HironakaGeneralThreeNonspecialAnalyticLoci HironakaDimensionThreeStepOneCurveEnvelope
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem stepOneInvM_superlevel_iff_top_of_isSpecial (hn : 0 < n)
    (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) (hsp : IsSpecial K R p)
    (s : ℕ) (β : WithTop (ValTy 2)) :
    toLex (s, β) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p ↔
      toLex (s, (⊤ : WithTop (ValTy 2))) ≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p := by
  classical
  simp [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL,
    hsp, Prod.Lex.toLex_le_toLex]

private theorem level_le_original_boundary_length (K : MarkedIdeal n X)
    (R : BlowupTower X Y) (p : Y) : level K R p ≤ K.E.length := by
  classical
  change (Finset.univ.filter (fun i : Fin (origMembers K R).length => p ∈ (origMembers K R).get i)).card ≤ _
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  exact List.length_take_le _ _

private theorem not_positive_threshold_of_level_zero (hn : 0 < n)
    (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y)
    (hl : level K R p = 0) (s : ℕ) (hs : 1 ≤ s) (β : WithTop (ValTy 2)) :
    ¬ toLex (s, β) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p := by
  intro hv
  have hfst := Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hn 2) K
    (StepOneValueMasked.lowerMarkedM K) R p
  change (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p)).1 = level K R p at hfst
  rcases (Prod.Lex.le_iff.mp hv) with h | ⟨h, _⟩
  · change s < (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p)).1 at h
    rw [hfst, hl] at h
    omega
  · change s = (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p)).1 at h
    rw [hfst, hl] at h
    omega

theorem exists_analytic_dimzero_positive_stepOne_threshold_dictionary (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 1)
    (hZA : Z ⊆ (geoTransformAlong K R).cosupp) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ p ∈ B \ E, ∀ q ∈ B \ E,
        ∀ s : ℕ, 1 ≤ s → ∀ β : WithTop (ValTy 2),
          (toLex (s, β) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p ↔
            toLex (s, β) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R q) := by
  classical
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have hZbar : Z ⊆ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hZA
  obtain ⟨Ev, hEv, hdEv, hEvZ, hv⟩ := exists_analytic_dimzero_across_mask_values hn K hK hmax R hcan hZ hdZ hZA
  obtain ⟨Eh, hEh, hdEh, hEhZ, _, hh⟩ := exists_analytic_dimzero_head_incidence_history_exception
    hn K hK.isWellFormed hK.one_le_d hmax R hb.1 hZ hdZ hZbar
  let P : Fin (K.E.length+1) → Set Y := fun i =>
    {p | p ∈ (geoTransformAlong (barMarked K) R).cosupp ∧
      toLex (i.val, (⊤ : WithTop (ValTy 2))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p}
  have hP : ∀ i, IsComplexAnalyticSubset (n := n) (P i) := fun i =>
    isComplexAnalyticSubset_stepOneInvM_top_superlevel (invFamily hn 2) hn K hK.isWellFormed hK.one_le_d hmax R hb.1 i.val
  obtain ⟨Et, hEt, hdEt, hEtZ, ht⟩ := exists_analytic_dimzero_predicate_exception hZ hdZ P hP
  obtain ⟨hEvh, hdEvh⟩ := analytic_dimzero_union hEv hdEv hEh hdEh
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEvh hdEvh hEt hdEt
  refine ⟨(Ev ∪ Eh) ∪ Et, hE, hdE, union_subset (union_subset hEvZ hEhZ) hEtZ, ?_⟩
  intro B hB p hp q hq s hs β
  have hpEv : p ∈ B \ Ev := ⟨hp.1, fun h => hp.2 (Or.inl (Or.inl h))⟩
  have hqEv : q ∈ B \ Ev := ⟨hq.1, fun h => hq.2 (Or.inl (Or.inl h))⟩
  have hpEh : p ∈ B \ Eh := ⟨hp.1, fun h => hp.2 (Or.inl (Or.inr h))⟩
  have hqEh : q ∈ B \ Eh := ⟨hq.1, fun h => hq.2 (Or.inl (Or.inr h))⟩
  have hpEt : p ∈ B \ Et := ⟨hp.1, fun h => hp.2 (Or.inr h)⟩
  have hqEt : q ∈ B \ Et := ⟨hq.1, fun h => hq.2 (Or.inr h)⟩
  have hl := (hh B hB p hpEh q hqEh).1
  have hpbar := hZbar (subset_of_mem_globalComponents hZ hB hp.1)
  have hqbar := hZbar (subset_of_mem_globalComponents hZ hB hq.1)
  let i : Fin (K.E.length+1) := ⟨level K R p, by have h := level_le_original_boundary_length K R p; omega⟩
  have htop : p ∈ P i ↔ q ∈ P i := (ht B hB p hpEt i).trans (ht B hB q hqEt i).symm
  have hspecial : IsSpecial K R p ↔ IsSpecial K R q := by
    have htp := stepOneInvM_top_threshold_iff (invFamily hn 2) hn K hK.isWellFormed hK.one_le_d hmax R hb.1 hpbar (level K R p)
    have htq := stepOneInvM_top_threshold_iff (invFamily hn 2) hn K hK.isWellFormed hK.one_le_d hmax R hb.1 hqbar (level K R p)
    change (p ∈ (geoTransformAlong (barMarked K) R).cosupp ∧
      toLex (level K R p, (⊤ : WithTop (ValTy 2))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p) ↔
      (q ∈ (geoTransformAlong (barMarked K) R).cosupp ∧
      toLex (level K R p, (⊤ : WithTop (ValTy 2))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R q) at htop
    constructor
    · intro hsp
      have hvq := (htop.mp ⟨hpbar, htp.mpr (Or.inr ⟨rfl, hsp⟩)⟩).2
      rcases htq.mp hvq with hlt | ⟨_, hspq⟩
      · omega
      · exact hspq
    · intro hsp
      have hvp := (htop.mpr ⟨hqbar, htq.mpr (Or.inr ⟨hl, hsp⟩)⟩).2
      rcases htp.mp hvp with hlt | ⟨_, hspp⟩
      · exact False.elim ((lt_irrefl _ hlt))
      · exact hspp
  by_cases hpSpecial : IsSpecial K R p
  · have hqSpecial := hspecial.mp hpSpecial
    have heq : Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p =
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R q := by
      simp [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL, hpSpecial, hqSpecial, hl]
    rw [heq]
  · have hqSpecial : ¬ IsSpecial K R q := fun h => hpSpecial (hspecial.mpr h)
    by_cases hpos : 1 ≤ level K R p
    · have hqpos : 1 ≤ level K R q := hl ▸ hpos
      rw [(hv B hB p hpEv q hqEv hpSpecial hqSpecial hpos hqpos).2.1]
    · have hp0 : level K R p = 0 := by omega
      have hq0 : level K R q = 0 := hl ▸ hp0
      exact iff_of_false (not_positive_threshold_of_level_zero hn K R p hp0 s hs β)
        (not_positive_threshold_of_level_zero hn K R q hq0 s hs β)

theorem isComplexAnalyticSubset_positive_stepOne_superlevel (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 1)
    (hZA : Z ⊆ (geoTransformAlong K R).cosupp)
    (henvelope : ∀ p ∈ (geoTransformAlong K R).cosupp, ¬ IsSpecial K R p → p ∈ Z)
    (s : ℕ) (hs : 1 ≤ s) (β : WithTop (ValTy 2)) :
    IsComplexAnalyticSubset (n := n) {p | p ∈ (geoTransformAlong K R).cosupp ∧
      toLex (s, β) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p} := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hK R hb.2.1
  have hCS := isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hUSC := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := 3) (invFamily hn 2) hn).usc K hK hmax R hcan
  let L : Set Y := {p | p ∈ (geoTransformAlong K R).cosupp ∧
    toLex (s, β) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p}
  have hL : IsClosed L := ResolutionInvariantOrder.IsInvUSCOn.isClosed_superlevel hUSC hCS.isClosed _
  obtain ⟨E, hE, hdE, _, hdict⟩ := exists_analytic_dimzero_positive_stepOne_threshold_dictionary hn K hK hmax R hcan hZ hdZ hZA
  have hLZ : IsComplexAnalyticSubset (n := n) (L ∩ Z) := by
    apply isComplexAnalyticSubset_of_component_dictionary hZ (hL.inter hZ.isClosed) inter_subset_right hE hdE
    intro B hB p hp q hq
    have hpZ := subset_of_mem_globalComponents hZ hB hp.1
    have hqZ := subset_of_mem_globalComponents hZ hB hq.1
    exact ⟨fun hpL => ⟨⟨hZA hqZ, (hdict B hB p hp q hq s hs β).mp hpL.1.2⟩, hqZ⟩,
      fun hqL => ⟨⟨hZA hpZ, (hdict B hB p hp q hq s hs β).mpr hqL.1.2⟩, hpZ⟩⟩
  let A : Set Y := {p | p ∈ (geoTransformAlong K R).cosupp ∧
    toLex (s, (⊤ : WithTop (ValTy 2))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p}
  have hA : IsComplexAnalyticSubset (n := n) A := by
    simpa only [hb.2.2] using isComplexAnalyticSubset_stepOneInvM_top_superlevel
      (invFamily hn 2) hn K hK.isWellFormed hK.one_le_d hmax R hb.1 s
  have hthreshold : toLex (s, β) ≤ toLex (s, (⊤ : WithTop (ValTy 2))) :=
    Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, le_top⟩)
  have heq : L = A ∪ (L ∩ Z) := by
    ext p
    constructor
    · intro hp
      by_cases hpZ : p ∈ Z
      · exact Or.inr ⟨hp, hpZ⟩
      · have hsp : IsSpecial K R p := by
          by_contra h
          exact hpZ (henvelope p hp.1 h)
        exact Or.inl ⟨hp.1, (stepOneInvM_superlevel_iff_top_of_isSpecial hn K R p hsp s β).mp hp.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1, hthreshold.trans hp.2⟩
      · exact hp.1
  change IsComplexAnalyticSubset (n := n) L
  rw [heq]
  exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hA hLZ

theorem isComplexAnalyticSubset_actual_general_three_companion_positive_stepOne_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (s : ℕ) (hs : 1 ≤ s) (β : WithTop (ValTy 2)) :
    IsComplexAnalyticSubset (n := n)
      {p : patchAt m T x | p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp ∧
        toLex (s, β) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2)
          (companionAt m T x) (companionTailAt m T x) p} := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  obtain ⟨Z, hZ, hdZ, hZA, hnsp⟩ := exists_actual_companion_dimone_nonspecial_envelope hn m h T hcan x hx hq
  exact isComplexAnalyticSubset_positive_stepOne_superlevel
    (X := CMfd.of (n := n) (maskAt m T x)) (Y := CMfd.of (n := n) (patchAt m T x))
    hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK hZ hdZ hZA hnsp s hs β

end
end Hironaka.HironakaStepOnePositiveAnalyticSuperlevels
