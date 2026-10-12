/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberCompanionHistoryExtension

/-!
# Actual positive-level member companion analytic loci and history

Actual coherent current cosupport and SNC/transverse geometry produce positive
special and all original-member count predicates for entire true companion
controlled transforms, without whole maximal order or candidate canonicality.
Each genuine curve component supplies its actually attained endpoint natural
order. A true locally finite union of proper analytic component intersections
produces one zero-dimensional exception freezing that component-own positive
companion's full finite count/special history and positive-level regime runs.
The original constructed General3 data internally produce the actual curve,
member family and whole original masked companion/coefficient dictionary.
Level-zero contact, deeper lower value descent and whole General3/G3 stay open.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberCompanionPositiveSpecialLoci
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneMemberLowerOrderPredicates HironakaStepOneMemberCompanionHistoryExtension
  HironakaCoherentTransformExtension InvDomainMemberRestriction NonmonomialOrderLocal
  AnalyticDimensionBasics GlobalComponents HironakaCurveAnalyticPredicates
  NormalCrossings HomogenizedIdealAlong StepOneValue StepOneLowerDomain
  StepOneRegime NonmonomialOrderRegime InvDomainCompanion CompanionRebase CompanionReductionAlong
  HironakaBoundaryCountAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  MemberInterLocusAlong BoundaryCount CodimOneSupportAlong MarkedIdealBiholomorphism
  HironakaDimensionTwoStepOneAnalyticSuperlevels
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

def positiveSpecialLocus (J : MarkedIdeal n X) (T : BlowupTower X Y) (s : ℕ) : Set Y :=
  {z | s ≤ level J T z ∧ IsSpecial J T z}

theorem positiveSpecialLocus_eq_memberInterLocus_inter (J : MarkedIdeal n X)
    (T : BlowupTower X Y) (s : ℕ) (hs : 1 ≤ s) :
    positiveSpecialLocus J T s =
      memberInterLocus (geoTransformAlong (barMarked J) T).N (origMembers J T)
        (geoTransformAlong (barMarked J) T).cosupp ∩ {z | s ≤ level J T z} := by
  ext z
  change (s ≤ level J T z ∧ _) ↔ (_ ∧ s ≤ level J T z)
  constructor
  · rintro ⟨hle, (⟨hz, _⟩ | ⟨_, hl⟩)⟩
    · omega
    · exact ⟨hl, hle⟩
  · rintro ⟨hl, hle⟩
    exact ⟨hle, Or.inr ⟨hs.trans hle, hl⟩⟩

theorem isComplexAnalyticSubset_level_superlevel_of_current_wf (hn : 0 < n)
    (J : MarkedIdeal n X) (T : BlowupTower X Y)
    (h : (geoTransformAlong (barMarked J) T).IsWellFormed) (s : ℕ) :
    IsComplexAnalyticSubset (n := n) {z | s ≤ level J T z} := by
  have hE : IsSNCDivisor n (origMembers J T) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist h.isSNCDivisor
      (List.take_sublist J.E.length (geoTransformAlong (barMarked J) T).E)
  apply isComplexAnalyticSubset_boundaryCount_superlevel (origMembers J T) _ s
  intro H hH
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hH
  have hinter := isClosedSubmanifold_memberInter hn hE {i}
  have heq : memberInter (origMembers J T) {i} = H := by
    ext z
    simp only [memberInter, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
    rw [hi]
  rw [heq] at hinter
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hinter

theorem isComplexAnalyticSubset_positiveSpecialLocus_of_current_domain (hn : 0 < n)
    {k : ℕ} (J : MarkedIdeal n X) (T : BlowupTower X Y)
    (h : IsInvDomain k (geoTransformAlong (barMarked J) T)) (s : ℕ) (hs : 1 ≤ s) :
    IsComplexAnalyticSubset (n := n) (positiveSpecialLocus J T s) := by
  have hA := isComplexAnalyticSubset_cosupport_along h.isWellFormed.isCoherent
    h.isWellFormed.isClosedSubmanifold_N h.one_le_d
  have hE : IsSNCDivisor n (origMembers J T) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist h.isWellFormed.isSNCDivisor
      (List.take_sublist J.E.length (geoTransformAlong (barMarked J) T).E)
  have htr : IsTransverse n (geoTransformAlong (barMarked J) T).N (origMembers J T) :=
    NormalCrossingsComparison.isTransverse_of_forall_mem h.isWellFormed.isTransverse
      (fun H hH => List.take_subset J.E.length _ hH)
  rw [positiveSpecialLocus_eq_memberInterLocus_inter J T s hs]
  exact (isComplexAnalyticSubset_memberInterLocus hn _ h.isWellFormed.isClosedSubmanifold_N
    (origMembers J T) hE htr hA (geoTransformAlong (barMarked J) T).cosupp_subset_N).inter
      (isComplexAnalyticSubset_level_superlevel_of_current_wf hn J T h.isWellFormed s)

theorem isComplexAnalyticSubset_memberCompanion_positiveSpecialLocus (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (q : ℕ) (hq : 1 ≤ q) (s : ℕ) (hs : 1 ≤ s) :
    IsComplexAnalyticSubset (n := n) (positiveSpecialLocus (memberPrefixCompanion m S H q) R s) :=
  isComplexAnalyticSubset_positiveSpecialLocus_of_current_domain hn _ R
    (member_prefix_companion_entire_domains hn m h S hS H hH R hR q hq).2 s hs

theorem isComplexAnalyticSubset_memberCompanion_level_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (q : ℕ) (hq : 1 ≤ q) (s : ℕ) :
    IsComplexAnalyticSubset (n := n) {z | s ≤ level (memberPrefixCompanion m S H q) R z} :=
  isComplexAnalyticSubset_level_superlevel_of_current_wf hn _ R
    (member_prefix_companion_entire_domains hn m h S hS H hH R hR q hq).2.isWellFormed s

theorem memberCompanion_level_eq_member_prefix_level
    (m : MarkedIdeal n X) (S : Finset (Fin m.E.length)) {V : CMfd.{u} n}
    (H : BlowupTower X V) (R : BlowupTower V Y) (q : ℕ) (z : Y) :
    level (memberPrefixCompanion m S H q) R z =
      level (geoTransformAlong (memberRemainderMarked m S) H) R z := by
  have hE : (memberPrefixCompanion m S H q).E =
      (geoTransformAlong (memberRemainderMarked m S) H).E := by
    simp only [memberPrefixCompanion, companionOf, companionAlong_E]
  unfold level
  rw [origMembers_eq, origMembers_eq, hE]

def memberCompanionSpecialHistoryPredicate (m : MarkedIdeal n X) (S : Finset (Fin m.E.length))
    (T : BlowupTower X Y) (i j q : ℕ) : Set Y :=
  (tail (tail T i) j).proj ⁻¹'
    positiveSpecialLocus (memberPrefixCompanion m S (head T i) q) (head (tail T i) j) 1

def memberCompanionCountHistoryPredicate (m : MarkedIdeal n X) (S : Finset (Fin m.E.length))
    (T : BlowupTower X Y) (i j s : ℕ) : Set Y :=
  (tail (tail T i) j).proj ⁻¹'
    {z | s ≤ level (memberPrefixCompanion m S (head T i) 1) (head (tail T i) j) z}

private theorem test_member_second_prefix (m : MarkedIdeal n X) (T : BlowupTower X Y)
    (hT : IsGeoTestTower m T) (i j : ℕ) :
    IsGeoTestTower (geoTransformAlong m (head T i)) (head (tail T i) j) :=
  ((isGeoTestTower_iff_head_tail _ (tail T i) j).mp ((isGeoTestTower_iff_head_tail m T i).mp hT).2).1

theorem isComplexAnalyticSubset_memberCompanionSpecialHistoryPredicate (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (i j q : ℕ) (hq : 1 ≤ q) :
    IsComplexAnalyticSubset (n := n) (memberCompanionSpecialHistoryPredicate m S T i j q) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail (tail T i) j).contMDiff_proj
    (isComplexAnalyticSubset_memberCompanion_positiveSpecialLocus hn m h S hS _
      ((isGeoTestTower_iff_head_tail m T i).mp hT).1 _ (test_member_second_prefix m T hT i j) q hq 1 le_rfl)

theorem isComplexAnalyticSubset_memberCompanionCountHistoryPredicate (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (i j s : ℕ) :
    IsComplexAnalyticSubset (n := n) (memberCompanionCountHistoryPredicate m S T i j s) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail (tail T i) j).contMDiff_proj
    (isComplexAnalyticSubset_memberCompanion_level_superlevel hn m h S hS _
      ((isGeoTestTower_iff_head_tail m T i).mp hT).1 _ (test_member_second_prefix m T hT i j) 1 le_rfl s)

private theorem level_le_initial_boundary_length (J : MarkedIdeal n X)
    (T : BlowupTower X Y) (z : Y) : level J T z ≤ J.E.length := by
  classical
  unfold level
  rw [origMembers_eq, boundaryCount_map]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

def memberCompanionPositiveHistory (m : MarkedIdeal n X) (S : Finset (Fin m.E.length))
    (T : BlowupTower X Y) (Z E : Set Y) : Prop :=
  ∀ B ∈ globalComponents (n := n) Z, ∃ q : ℕ,
    (∃ x ∈ B, nmOrd (geoTransformAlong (memberRemainderMarked m S) T) x = q) ∧
    (∀ x ∈ B, q ≤ nmOrd (geoTransformAlong (memberRemainderMarked m S) T) x) ∧
    (∀ x ∈ B \ E, nmOrd (geoTransformAlong (memberRemainderMarked m S) T) x = q) ∧
    (∀ x ∈ B \ E, ∀ y ∈ B \ E, ∀ r,
      regimeRun (OrdRegime (memberRemainderMarked m S) r) T x =
        regimeRun (OrdRegime (memberRemainderMarked m S) r) T y) ∧
    (1 ≤ q → ∀ x ∈ B \ E, ∀ y ∈ B \ E, ∀ i : Fin (T.length+1),
      (∀ j : Fin (T.length+1),
        let C := memberPrefixCompanion m S (head T i) q
        let R := head (tail T i) j
        let g := (tail (tail T i) j).proj
        level C R (g x) = level C R (g y) ∧
        (g x ∈ positiveSpecialLocus C R 1 ↔ g y ∈ positiveSpecialLocus C R 1)) ∧
      ∀ s : ℕ, 1 ≤ s →
        regimeRun (stepRegime (memberPrefixCompanion m S (head T i) q) s) (tail T i) x =
          regimeRun (stepRegime (memberPrefixCompanion m S (head T i) q) s) (tail T i) y)

private theorem exists_component_own_predicate_exception {ι : Type*} [Fintype ι]
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (P : globalComponents (n := n) Z → ι → Set Y)
    (hP : ∀ B i, IsComplexAnalyticSubset (n := n) (P B i)) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B : globalComponents (n := n) Z, ∀ x ∈ (B : Set Y) \ E, ∀ i,
        x ∈ P B i ↔ (B : Set Y) ⊆ P B i := by
  classical
  let e : ι → globalComponents (n := n) Z → Set Y := fun i B =>
    if (B : Set Y) ⊆ P B i then ∅ else (B : Set Y) ∩ P B i
  have he : ∀ i B, IsComplexAnalyticSubset (n := n) (e i B) ∧ DimLE (n := n) (e i B) 0 := by
    intro i B
    dsimp only [e]
    split_ifs with hsub
    · exact ⟨by simp, by intro z k hz; exact hz.2.1.elim⟩
    · exact analytic_dimzero_inter_globalComponent_of_not_subset hZ hdim B.2 (hP B i) hsub
  have hlf : ∀ i, LocallyFinite (e i) := by
    intro i
    apply (locallyFinite_globalComponents hZ).subset
    intro B z hz
    dsimp only [e] at hz
    split_ifs at hz
    · exact hz.elim
    · exact hz.1
  let Ei : ι → Set Y := fun i => ⋃ B : globalComponents (n := n) Z, e i B
  have hEi : ∀ i, IsComplexAnalyticSubset (n := n) (Ei i) ∧ DimLE (n := n) (Ei i) 0 :=
    fun i => analytic_dimzero_iUnion_of_locallyFinite (e i) (hlf i) (fun B => (he i B).1) (fun B => (he i B).2)
  let E := ⋃ i, Ei i
  obtain ⟨hE, hdE⟩ := analytic_dimzero_iUnion_of_locallyFinite Ei (locallyFinite_of_finite Ei)
    (fun i => (hEi i).1) (fun i => (hEi i).2)
  refine ⟨E, hE, hdE, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    change z ∈ ⋃ B : globalComponents (n := n) Z, e i B at hzi
    obtain ⟨B, hze⟩ := mem_iUnion.mp hzi
    apply subset_of_mem_globalComponents hZ B.2
    dsimp only [e] at hze
    split_ifs at hze
    · exact hze.elim
    · exact hze.1
  · intro B x hx i
    refine ⟨?_, fun h => h hx.1⟩
    intro hxP
    by_contra hnot
    apply hx.2
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨B, by dsimp only [e]; rw [if_neg hnot]; exact ⟨hx.1, hxP⟩⟩⟩

theorem exists_analytic_dimzero_member_companion_positive_history (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hsub : Z ⊆ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      memberCompanionPositiveHistory m S T Z E := by
  classical
  have hd := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS T hT
  obtain ⟨Eo, hEo, hdEo, hEoZ, hm⟩ := exists_analytic_dimzero_pulled_nmOrd_exception hn _ hd
    (id : Y → Y) contMDiff_id hZ hdim hsub
  choose qB hmin using (fun B : globalComponents (n := n) Z => hm B.1 B.2)
  let L := T.length+1
  let ι : Type := (Fin L × Fin L) ⊕
    (Σ i : Fin L, Fin L × Fin ((geoTransformAlong (memberRemainderMarked m S) (head T i)).E.length+1))
  let P : globalComponents (n := n) Z → ι → Set Y := fun B a =>
    if 1 ≤ qB B then
      Sum.elim
        (fun ij => memberCompanionSpecialHistoryPredicate m S T ij.1 ij.2 (qB B))
        (fun ijr => memberCompanionCountHistoryPredicate m S T ijr.1 ijr.2.1 ijr.2.2) a
    else ∅
  have hP : ∀ B a, IsComplexAnalyticSubset (n := n) (P B a) := by
    intro B a
    dsimp only [P]
    split_ifs with hq
    · cases a with
      | inl ij => exact isComplexAnalyticSubset_memberCompanionSpecialHistoryPredicate hn m h S hS T hT _ _ _ hq
      | inr ijr => exact isComplexAnalyticSubset_memberCompanionCountHistoryPredicate hn m h S hS T hT _ _ _
    · simp
  obtain ⟨Ep, hEp, hdEp, hEpZ, hp⟩ := exists_component_own_predicate_exception hZ hdim P hP
  obtain ⟨Er, hEr, hdEr, hErZ, hr⟩ := exists_analytic_dimzero_member_all_order_run_history hn m h S hS T hT hZ hdim hsub
  obtain ⟨hEop, hdEop⟩ := analytic_dimzero_union hEo hdEo hEp hdEp
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEop hdEop hEr hdEr
  refine ⟨(Eo ∪ Ep) ∪ Er, hE, hdE, union_subset (union_subset hEoZ hEpZ) hErZ, ?_⟩
  intro B hB
  let b : globalComponents (n := n) Z := ⟨B,hB⟩
  refine ⟨qB b, (hmin b).1, (hmin b).2.1, ?_, ?_, ?_⟩
  · intro x hx
    exact (hmin b).2.2.1 x ⟨hx.1, fun hh => hx.2 (Or.inl (Or.inl hh))⟩
  · intro x hx y hy r
    exact (hr B hB x ⟨hx.1, fun hh => hx.2 (Or.inr hh)⟩
      y ⟨hy.1, fun hh => hy.2 (Or.inr hh)⟩).1 r
  · intro hq x hx y hy i
    have hxp : x ∈ B \ Ep := ⟨hx.1, fun hh => hx.2 (Or.inl (Or.inr hh))⟩
    have hyp : y ∈ B \ Ep := ⟨hy.1, fun hh => hy.2 (Or.inl (Or.inr hh))⟩
    have hdict : ∀ a : ι, x ∈ P b a ↔ y ∈ P b a :=
      fun a => (hp b x hxp a).trans (hp b y hyp a).symm
    have hpref : ∀ j : Fin L,
        let C := memberPrefixCompanion m S (head T i) (qB b)
        let R := head (tail T i) j
        let g := (tail (tail T i) j).proj
        level C R (g x) = level C R (g y) ∧
          (g x ∈ positiveSpecialLocus C R 1 ↔ g y ∈ positiveSpecialLocus C R 1) := by
      intro j
      dsimp only
      let C₁ := memberPrefixCompanion m S (head T i) 1
      let R := head (tail T i) j
      let g := (tail (tail T i) j).proj
      let k := (geoTransformAlong (memberRemainderMarked m S) (head T i)).E.length
      have hCE : C₁.E.length = k := by
        simp only [C₁, k, memberPrefixCompanion, companionOf, companionAlong_E]
      have hxbound : level C₁ R (g x) ≤ k := by
        rw [← hCE]
        exact level_le_initial_boundary_length C₁ R (g x)
      have hybound : level C₁ R (g y) ≤ k := by
        rw [← hCE]
        exact level_le_initial_boundary_length C₁ R (g y)
      have hcounts : ∀ r : ℕ, r ≤ k → (r ≤ level C₁ R (g x) ↔ r ≤ level C₁ R (g y)) := by
        intro r hle
        have hh := hdict (Sum.inr ⟨i, j, ⟨r, by omega⟩⟩)
        simpa only [P, if_pos hq, Sum.elim_inr, memberCompanionCountHistoryPredicate, mem_preimage, mem_ofPred_eq] using hh
      have hcount : level C₁ R (g x) = level C₁ R (g y) :=
        Nat.le_antisymm ((hcounts _ hxbound).mp le_rfl) ((hcounts _ hybound).mpr le_rfl)
      constructor
      · rw [memberCompanion_level_eq_member_prefix_level, memberCompanion_level_eq_member_prefix_level]
        simpa only [C₁, memberCompanion_level_eq_member_prefix_level] using hcount
      · have hh := hdict (Sum.inl (i,j))
        simpa only [P, if_pos hq, Sum.elim_inl, memberCompanionSpecialHistoryPredicate, mem_preimage] using hh
    refine ⟨hpref, ?_⟩
    intro s hs
    apply regimeRun_eq_of_head_predicates
    intro r hrlen
    have hlen : r < L := by
      rw [length_tail] at hrlen
      dsimp only [L]
      omega
    let j : Fin L := ⟨r,hlen⟩
    have hh := hpref j
    dsimp only at hh
    change (level _ _ _ = s ∧ ¬ IsSpecial _ _ _) ↔ (level _ _ _ = s ∧ ¬ IsSpecial _ _ _)
    constructor
    · rintro ⟨hxs, hxn⟩
      have hys := hh.1.symm.trans hxs
      refine ⟨hys, ?_⟩
      intro hysp
      have hyP : (tail (tail T i) r).proj y ∈ positiveSpecialLocus
          (memberPrefixCompanion m S (head T i) (qB b)) (head (tail T i) r) 1 :=
        ⟨by rw [hys]; exact hs, hysp⟩
      exact hxn ((hh.2.mpr hyP).2)
    · rintro ⟨hys, hyn⟩
      have hxs := hh.1.trans hys
      refine ⟨hxs, ?_⟩
      intro hxsp
      have hxP : (tail (tail T i) r).proj x ∈ positiveSpecialLocus
          (memberPrefixCompanion m S (head T i) (qB b)) (head (tail T i) r) 1 :=
        ⟨by rw [hxs]; exact hs, hxsp⟩
      exact hyn ((hh.2.mp hxP).2)

open HironakaGeneralThreeNonspecialAnalyticLoci
open Hironaka.ResolutionInvariantSpec (IsCanonical)

theorem exists_actual_general_three_member_companion_positive_history (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((CanonicalCentres.invFamily hn 3).inv m) T)
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
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ maskA K H p₀ ∧
      ∃ A E : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) A ∧
        DimLE (n := n) A 1 ∧ A ⊆ (geoTransformAlong (memberRemainderMarked J₀ S) Q).N ∧ p ∈ A ∧
        IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ A ∧
        memberCompanionPositiveHistory J₀ S Q A E ∧
        ∀ i q : ℕ, 1 ≤ q →
          let C := memberPrefixCompanion J₀ S (head Q i) q
          let B := memberPrefixCoefficientCompanion J₀ S (head Q i) q
          let U := openPreimage (head Q i) (maskA K H p₀)
          let L := geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict (maskA K H p₀) (head Q i))
          IsInvDomain 2 (geoTransformAlong C (tail Q i)) ∧
            IsInvDomain 2 (geoTransformAlong B (tail Q i)) ∧
            geoTransformAlong (companionOf n L q) (restrict U (tail Q i)) =
              MarkedIdeal.pullback (Subtype.val : openPreimage (tail Q i) U → CMfd.of (n := n) (patchAt m T x))
                (geoTransformAlong C (tail Q i)) ∧
            geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (companionOf n L q)) (restrict U (tail Q i)) =
              MarkedIdeal.pullback (Subtype.val : openPreimage (tail Q i) U → CMfd.of (n := n) (patchAt m T x))
                (geoTransformAlong B (tail Q i)) := by
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
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (CanonicalCentres.invFamily hn 2) K hK hmax hn R hcanK
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  obtain ⟨s, hs, hmask, _, A, hA, hdA, hsubA, hpA⟩ := exists_actual_companion_member_history_curve hn m h T hcan x hx hq p hp hnsp hpos
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hnsp).1
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  have hdJ₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_barMarked K hK) H hhead
  have hE₀ : ∀ W ∈ origMembers K H, W ∈ J₀.E := fun W hW => List.mem_of_mem_take hW
  have hS : S.Nonempty := membersThrough_nonempty hE₀ (by change 1 ≤ level K H p₀; rw [hl]; omega)
  obtain ⟨E, hE, hdE, hEA, hhist⟩ := exists_analytic_dimzero_member_companion_positive_history hn J₀ hdJ₀ S hS Q htail hA hdA hsubA
  exact ⟨s, hs, hmask, A, E, hA, hdA, hsubA, hpA, hE, hdE, hEA, hhist,
    fun i q hq => member_lower_prefix_companion_dictionary hn K hK H hhead p₀ hl Q htail i q hq⟩

end
end Hironaka.HironakaStepOneMemberCompanionPositiveSpecialLoci
