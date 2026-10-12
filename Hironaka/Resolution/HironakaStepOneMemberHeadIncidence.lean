/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberLowerExtension

/-! # Actual all-head incidence and whole positive-member mask agreement

True finite dependent head/member predicates are analytic under the real
barMarked test tower. Genuine locally finite curve components internally
produce a dimension-zero exception freezing all actual incidences, whole
mask Opens, entire member extensions and literal positive lower marked records.
The original constructed General3 consumer supplies the actual companion,
canonical tail and genuine curve internally; no compatibility certificate.
Original level-zero contact, deeper cross-mask gluing and whole G3 remain OPEN.
Blueprint: hironaka-step-one-member-head-incidence-extension.tex.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberHeadIncidence
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  StepOneValue StepOneLowerDomain InvDomainMemberRestriction HomogenizedIdealAlong
  HironakaStepOneMemberLowerExtension HironakaStepOneCurveHistoryPredicates
  HironakaCurveAnalyticPredicates HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaGeneralThreeNonspecialAnalyticLoci HironakaDimensionThreeStepOneCurveEnvelope
  GlobalComponents AnalyticDimensionBasics CanonicalCentres MarkedIdealBiholomorphism StepOneRegime
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

def headMemberPredicate (m : MarkedIdeal n X) (T : BlowupTower X Y) (r : ℕ)
    (j : Fin (origMembers m (head T r)).length) : Set Y :=
  (tail T r).proj ⁻¹' (origMembers m (head T r)).get j

theorem isComplexAnalyticSubset_headMemberPredicate (hn : 0 < n)
    (m : MarkedIdeal n X) (hw : m.IsWellFormed) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) (r : ℕ)
    (j : Fin (origMembers m (head T r)).length) :
    IsComplexAnalyticSubset (n := n) (headMemberPredicate m T r j) := by
  have hh := ((isGeoTestTower_iff_head_tail (barMarked m) T r).mp hT).1
  have hwH := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked m hw) (head T r) hh
  have hm : (origMembers m (head T r)).get j ∈ (geoTransformAlong (barMarked m) (head T r)).E :=
    List.mem_of_mem_take (List.get_mem _ j)
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  apply AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail T r).contMDiff_proj
  rw [← hi]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    (MonomialPart.isClosedSubmanifold_get hn hwH.isSNCDivisor i)

def headIncidenceAligned (m : MarkedIdeal n X) (T : BlowupTower X Y) (p q : Y) : Prop :=
  ∀ r : Fin (T.length+1),
    let H := head T r
    let p₀ := (tail T r).proj p
    let q₀ := (tail T r).proj q
    (∀ W ∈ origMembers m H, p₀ ∈ W ↔ q₀ ∈ W) ∧
      level m H p₀ = level m H q₀ ∧
      membersThrough (geoTransformAlong (barMarked m) H).E (origMembers m H) p₀ =
        membersThrough (geoTransformAlong (barMarked m) H).E (origMembers m H) q₀ ∧
      maskA m H p₀ = maskA m H q₀ ∧
      memberLowerExtension m H p₀ = memberLowerExtension m H q₀ ∧
      ∀ s : ℕ, HEq (lowerMarked m (s+1) H p₀) (lowerMarked m (s+1) H q₀)

private theorem level_eq_of_incidence (m : MarkedIdeal n X) (T : BlowupTower X Y) (p q : Y)
    (hc : ∀ W ∈ origMembers m T, p ∈ W ↔ q ∈ W) : level m T p = level m T q := by
  classical
  unfold level BoundaryCount.boundaryCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hc _ (List.get_mem _ i)

private theorem maskA_eq_of_incidence (m : MarkedIdeal n X) (T : BlowupTower X Y) (p q : Y)
    (hc : ∀ W ∈ origMembers m T, p ∈ W ↔ q ∈ W)
    (hl : level m T p = level m T q) : maskA m T p = maskA m T q := by
  apply TopologicalSpace.Opens.ext
  change interior {z | _} = interior {z | _}
  congr 1
  ext z
  simp only [mem_ofPred_eq, hl]
  constructor
  · rintro ⟨h, hns⟩
    exact ⟨fun W hW hzW => (hc W hW).mp (h W hW hzW), hns⟩
  · rintro ⟨h, hns⟩
    exact ⟨fun W hW hzW => (hc W hW).mpr (h W hW hzW), hns⟩

private theorem pullback_memberRestrict_heq (J : MarkedIdeal n Y)
    (U V : Opens Y) (S R : Finset (Fin J.E.length)) (hU : U = V) (hS : S = R) :
    HEq (MarkedIdeal.pullback (Subtype.val : U → Y) (memberRestrict J S))
      (MarkedIdeal.pullback (Subtype.val : V → Y) (memberRestrict J R)) := by
  subst V
  subst R
  rfl

private theorem whole_alignment_of_incidence (m : MarkedIdeal n X) (T : BlowupTower X Y)
    (p q : Y) (hc : ∀ r : Fin (T.length+1), ∀ W ∈ origMembers m (head T r),
      (tail T r).proj p ∈ W ↔ (tail T r).proj q ∈ W) : headIncidenceAligned m T p q := by
  intro r
  dsimp only
  have hl := level_eq_of_incidence m (head T r) _ _ (hc r)
  have hS : membersThrough (geoTransformAlong (barMarked m) (head T r)).E
      (origMembers m (head T r)) ((tail T r).proj p) =
      membersThrough (geoTransformAlong (barMarked m) (head T r)).E
      (origMembers m (head T r)) ((tail T r).proj q) := by
    ext i
    rw [mem_membersThrough, mem_membersThrough]
    constructor
    · rintro ⟨hi, hp⟩
      exact ⟨hi, (hc r _ hi).mp hp⟩
    · rintro ⟨hi, hq⟩
      exact ⟨hi, (hc r _ hi).mpr hq⟩
  have hU := maskA_eq_of_incidence m (head T r) _ _ (hc r) hl
  refine ⟨hc r, hl, hS, hU, ?_, ?_⟩
  · unfold memberLowerExtension
    rw [hS]
  intro s
  exact pullback_memberRestrict_heq (geoTransformAlong (barMarked m) (head T r)) _ _ _ _ hU hS

theorem exists_analytic_dimzero_head_incidence_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (hw : m.IsWellFormed) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) {Z : Set Y}
    (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 1) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ p ∈ B \ E, ∀ q ∈ B \ E,
        headIncidenceAligned m T p q := by
  classical
  let I := (r : Fin (T.length+1)) × Fin (origMembers m (head T r)).length
  let P : I → Set Y := fun i => headMemberPredicate m T i.1 i.2
  obtain ⟨E, hE, hdE, hEZ, hdict⟩ := exists_analytic_dimzero_predicate_exception hZ hdZ P
    (fun i => isComplexAnalyticSubset_headMemberPredicate hn m hw T hT i.1 i.2)
  refine ⟨E, hE, hdE, hEZ, ?_⟩
  intro B hB p hp q hq
  apply whole_alignment_of_incidence
  intro r W hW
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hW
  exact (hdict B hB p hp ⟨r,j⟩).trans (hdict B hB q hq ⟨r,j⟩).symm

theorem exists_analytic_dimzero_head_incidence_history_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (hw : m.IsWellFormed) (hd : 1 ≤ m.d)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) {Z : Set Y}
    (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 1)
    (hZA : Z ⊆ (geoTransformAlong (barMarked m) T).cosupp) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      (∀ p ∈ Z \ E, RegularAtDim (n := n) Z p 1) ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ p ∈ B \ E, ∀ q ∈ B \ E,
        level m T p = level m T q ∧
        regimeRun (stepRegime m (level m T p)) T p = regimeRun (stepRegime m (level m T q)) T q ∧
        headIncidenceAligned m T p q := by
  obtain ⟨S, hS, hdS, hSZ, hreg, hrun⟩ :=
    exists_analytic_dimzero_stepOne_history_exception hn m hw hd hmax T hT Z hZ hdZ hZA
  obtain ⟨Q, hQ, hdQ, hQZ, hinc⟩ := exists_analytic_dimzero_head_incidence_exception hn m hw T hT hZ hdZ
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hS hdS hQ hdQ
  refine ⟨S ∪ Q, hE, hdE, union_subset hSZ hQZ, ?_, ?_⟩
  · intro p hp
    exact hreg p ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  intro B hB p hp q hq
  obtain ⟨hl, hr⟩ := hrun B hB p ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
    q ⟨hq.1, fun h => hq.2 (Or.inl h)⟩
  exact ⟨hl, hr, hinc B hB p ⟨hp.1, fun h => hp.2 (Or.inr h)⟩
    q ⟨hq.1, fun h => hq.2 (Or.inr h)⟩⟩

theorem exists_actual_general_three_companion_head_incidence (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    ∃ Z : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) Z ∧
      DimLE (n := n) Z 1 ∧ Z ⊆ (geoTransformAlong K R).cosupp ∧
      (∀ p ∈ (geoTransformAlong K R).cosupp, ¬ IsSpecial K R p → p ∈ Z) ∧
      ∃ E : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) E ∧
        DimLE (n := n) E 0 ∧ E ⊆ Z ∧
        (∀ p ∈ Z \ E, RegularAtDim (n := n) Z p 1) ∧
        ∀ B ∈ globalComponents (n := n) Z, ∀ p ∈ B \ E, ∀ q ∈ B \ E,
          level K R p = level K R q ∧
          regimeRun (stepRegime K (level K R p)) R p = regimeRun (stepRegime K (level K R q)) R q ∧
          headIncidenceAligned K R p q := by
  dsimp only
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK
  obtain ⟨Z, hZ, hdZ, hZA, hnsp⟩ := exists_actual_companion_dimone_nonspecial_envelope hn m h T hcan x hx hq
  have hZbar : Z ⊆ (geoTransformAlong (barMarked (companionAt m T x)) (companionTailAt m T x)).cosupp := by
    rw [hb.2.2]
    exact hZA
  obtain ⟨E, hE, hdE, hEZ, hreg, hdict⟩ :=
    exists_analytic_dimzero_head_incidence_history_exception
      (X := CMfd.of (n := n) (maskAt m T x)) (Y := CMfd.of (n := n) (patchAt m T x))
      hn (companionAt m T x) hK.isWellFormed hK.one_le_d hmax
      (companionTailAt m T x) hb.1 hZ hdZ hZbar
  exact ⟨Z, hZ, hdZ, hZA, hnsp, E, hE, hdE, hEZ, hreg, hdict⟩

end
end Hironaka.HironakaStepOneMemberHeadIncidence
