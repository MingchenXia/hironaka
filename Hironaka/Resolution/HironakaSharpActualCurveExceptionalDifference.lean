/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualChronologicalAmbientTrace

/-! The literal original-member I/J germ difference (BM97 tau_D), independently
of FIRST Z, full sharp Sigma and any proposed termination invariant. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveExceptionalDifference
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualChronologicalAmbientTrace HironakaSharpActualCurveExceptionalResidualUnit
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualOriginalControlledHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpActualFirstGoodLowerDimension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  NormalCrossings NormalCrossingsComparison MonomialPartAlong DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower IdealWeightPowers InvertibleIdealQuotient
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual whole normalized residual membership off EVERY boundary member. -/
theorem actual_normalized_nonmonomial_off_family_iff {N : Set Y} {F : List (Set Y)}
    (I : GermIdeal n Y) {x : Y} (hx : x ∉ ⋃ H ∈ F,H) (g : Y → ℂ) :
    (nonmonomialPartAlong n N (restrictOn n N I) F).mem x g ↔
      (restrictOn n N I).mem x g := by
  have h1 : (monomialPartAlong n N (restrictOn n N I) F).mem x (1 : Y → ℂ) := by
    refine ⟨holomorphicAt_const 1,?_⟩
    intro i _hiN hiD
    exact (hx (mem_iUnion₂.mpr ⟨F.get i,List.get_mem F i,hiD⟩)).elim
  constructor
  · intro hg
    have hr : (restrictOn n N (restrictOn n N I)).mem x g := by
      simpa only [Pi.one_apply,one_mul] using hg.2 (1 : Y → ℂ) h1
    exact ⟨hr.1,IsInSpanOnAt.trans (fun a ha => ha.2) hr.2⟩
  · intro hg
    refine ⟨hg.1,fun a ha => ?_⟩
    have hp := restrictOn_mul_left ha.1 hg
    exact ⟨hp.1,IsInSpanAt.restrict (isInSpanAt_self hp hp.1)⟩

/-- A genuine relative finite span tests the actual closed member, not a
chosen generator or a proposed support dictionary. -/
theorem actual_normalized_vanishing_unit_iff {N H : Set Y} (hH : IsClosed H)
    {x : Y} (hx : x ∈ N) :
    (restrictOn n N (vanishingIdeal (n := n) H)).mem x (1 : Y → ℂ) ↔ x ∉ H := by
  constructor
  · rintro ⟨_hh,r,s,a,hs,_ha,heq⟩ hxH
    have hEq := heq.self_of_nhds hx
    have hzero : ∀ i : Fin r,s i x=0 := fun i => (hs i).2.self_of_nhds hxH
    have hsum : (∑ i : Fin r,a i x*s i x)=0 := by simp only [hzero,mul_zero,Finset.sum_const_zero]
    exact one_ne_zero (hEq.trans hsum)
  · intro hxH
    have h1 : (vanishingIdeal (n := n) H).mem x (1 : Y → ℂ) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hH.isOpen_compl.mem_nhds hxH] with y hy hyH
      exact (hy hyH).elim
    exact ⟨holomorphicAt_const 1,IsInSpanAt.restrict (isInSpanAt_self h1 (holomorphicAt_const 1))⟩

/-- Actual ORIGINAL positions with unequal full ambient-trace/chronological
ideal germ predicates. No distinct-trace quotient or exceptional index count. -/
def actualAmbientDifferencePositions (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (x : Y) : Finset (Fin E.length) :=
  Finset.univ.filter fun i => ¬∀ g,
    (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
      (vanishingIdeal (n := n) (strictAlong T (E.get i)))).mem x g ↔
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem x g

def actualTauD (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (x : Y) : ℕ :=
  (actualAmbientDifferencePositions W E T x).card

def actualAmbientExceptionalDifference (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) : Set Y :=
  {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧ 0 < actualTauD W E T x}

private theorem actual_coherent_unit_mem_iff {I : GermIdeal n Y} (hI : I.IsCoherent)
    {x : Y} (h1 : I.mem x (1 : Y → ℂ)) (g : Y → ℂ) :
    I.mem x g ↔ HolomorphicAt n g x := by
  refine ⟨fun hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg,fun hg => ?_⟩
  exact HomogenizedIdeal.mem_of_isInSpanAt hI
    (isInSpanAt_of_eq_mul h1 hg hg (Eventually.of_forall fun _ => by simp))

/-- ONLY original curve inputs identify EACH full actual ideal-germ
difference with real exceptional and real ambient strict membership. -/
theorem original_curve_actual_member_germ_difference_iff (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) (i : Fin E.length) :
    i ∈ actualAmbientDifferencePositions W E T x ↔
      x ∈ (⋃ H ∈ (geoTransformAlong (geometricTemplate W []) T).E,H) ∧
        x ∈ strictAlong T (E.get i) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let H := strictAlong T (E.get i)
  let I := restrictOn n A.N (vanishingIdeal (n := n) H)
  let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let M := originalMemberProductMarked W E 1
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  obtain ⟨hcI,_hnzI,_hcD,_hnzD,_hmD,hNm,_hFactor⟩ :=
    original_curve_history_true_ambient_member_factor_dictionary hn hW hE hdense hr T hT i
  change nonmonomialPartAlong n A.N I A.E=J at hNm
  have hcJ : J.IsCoherent := (original_members_actual_finite_chronological_geometry hn hW hE hdense i T hGeom).2.2.2.1.isCoherent
  have hDisc := original_domain_one_test_actual_discrete_centres M hInit T hT
  have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
  have hDenseI : W ⊆ closure (W \ E.get i) := by
    apply Subset.trans hdense
    apply closure_mono
    exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
  have hHT := (actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDisc).1
  have hClosedH : IsClosed H := (MonomialPart.isClosedSubmanifold_get hn hHT (0 : Fin [H].length)).1
  simp only [actualAmbientDifferencePositions,Finset.mem_filter,Finset.mem_univ,true_and]
  change (¬∀ g,I.mem x g ↔ J.mem x g) ↔ x ∈ (⋃ D ∈ A.E,D) ∧ x ∈ H
  by_cases hxF : x ∈ ⋃ D ∈ A.E,D
  · have hJ1 : J.mem x (1 : Y → ℂ) :=
      (original_curve_exceptional_residual_units_and_defect_disjoint hn hW hE hdense hr T hGeom x hx hxF).1 i
    constructor
    · intro hne
      refine ⟨hxF,?_⟩
      by_contra hxH
      have hI1 : I.mem x (1 : Y → ℂ) := (actual_normalized_vanishing_unit_iff hClosedH hx).mpr hxH
      exact hne (fun g => (actual_coherent_unit_mem_iff hcI hI1 g).trans
        (actual_coherent_unit_mem_iff hcJ hJ1 g).symm)
    · rintro ⟨_hxF,hxH⟩ hEq
      exact ((actual_normalized_vanishing_unit_iff hClosedH hx).mp ((hEq 1).mpr hJ1)) hxH
  · constructor
    · intro hne
      apply False.elim
      apply hne
      intro g
      rw [←hNm]
      exact (actual_normalized_nonmonomial_off_family_iff (vanishingIdeal (n := n) H) hxF g).symm
    · exact fun h => (hxF h.1).elim

/-- The true ORIGINAL-position set, without quotienting or dropping positions. -/
theorem original_curve_actual_difference_positions_eq (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) :
    actualAmbientDifferencePositions W E T x=
      if x ∈ (⋃ H ∈ (geoTransformAlong (geometricTemplate W []) T).E,H)
      then Finset.univ.filter (fun i : Fin E.length => x ∈ strictAlong T (E.get i)) else ∅ := by
  ext i
  rw [original_curve_actual_member_germ_difference_iff hn hW hE hdense hr T hT hx i]
  split <;> simp_all

/-- ENTIRE actual support of tau_D, including outside the carrier. -/
theorem original_curve_actual_exceptional_difference_eq (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    actualAmbientExceptionalDifference W E T=
      ((geoTransformAlong (geometricTemplate W []) T).N ∩
        (⋃ H ∈ (geoTransformAlong (geometricTemplate W []) T).E,H)) ∩
        (⋃ i : Fin E.length,strictAlong T (E.get i)) := by
  ext x
  constructor
  · rintro ⟨hx,hpos⟩
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hpos
    obtain ⟨hxF,hxH⟩ := (original_curve_actual_member_germ_difference_iff hn hW hE hdense hr T hT hx i).mp hi
    exact ⟨⟨hx,hxF⟩,mem_iUnion.mpr ⟨i,hxH⟩⟩
  · rintro ⟨⟨hx,hxF⟩,hxH⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxH
    exact ⟨hx,Finset.card_pos.mpr ⟨i,(original_curve_actual_member_germ_difference_iff
      hn hW hE hdense hr T hT hx i).mpr ⟨hxF,hi⟩⟩⟩

private theorem analytic_finset_union {ι : Type*} (t : Finset ι) (A : ι → Set Y)
    (hA : ∀ i ∈ t,IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t,A i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA i (Finset.mem_insert_self i t)) (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

private theorem analytic_finite_union {ι : Type*} [Fintype ι] (A : ι → Set Y)
    (hA : ∀ i,IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i,A i) := by
  simpa only [Finset.mem_univ,iUnion_true] using analytic_finset_union Finset.univ A (fun i _ => hA i)

private theorem actual_list_union_eq (F : List (Set Y)) :
    (⋃ H ∈ F,H)=⋃ j : Fin F.length,F.get j := by
  ext x
  constructor
  · intro hx
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hx
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hH
    exact mem_iUnion.mpr ⟨j,hxH⟩
  · intro hx
    obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨F.get j,List.get_mem F j,hxj⟩

/-- GENUINE analyticity and discreteness of the exact original-member
exceptional difference. No supplied bad-set or regularity certificate. -/
theorem original_curve_actual_exceptional_difference_analytic_discrete (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    IsComplexAnalyticSubset (n := n) (actualAmbientExceptionalDifference W E T) ∧
      IsDiscrete (actualAmbientExceptionalDifference W E T) := by
  let M := originalMemberProductMarked W E 1
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  have hDisc := original_domain_one_test_actual_discrete_centres M hInit T hT
  let A := geoTransformAlong (geometricTemplate W []) T
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  have hPure := actual_template_regular_dimension hW 1 hr T hGeom
  have hOriginal : ∀ i : Fin E.length,IsClosedSubmanifold n (strictAlong T (E.get i)) := by
    intro i
    have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
    have hDenseI : W ⊆ closure (W \ E.get i) := by
      apply Subset.trans hdense
      apply closure_mono
      exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
    have hHT := (actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDisc).1
    exact MonomialPart.isClosedSubmanifold_get hn hHT (0 : Fin [strictAlong T (E.get i)].length)
  have hExceptional : ∀ j : Fin A.E.length,IsClosedSubmanifold n (A.E.get j) :=
    fun j => MonomialPart.isClosedSubmanifold_get hn hwA.isSNCDivisor j
  have hEq := original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT
  have hAnalytic : IsComplexAnalyticSubset (n := n) (actualAmbientExceptionalDifference W E T) := by
    rw [hEq,actual_list_union_eq]
    exact ((AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hwA.isClosedSubmanifold_N).inter
      (analytic_finite_union (fun j : Fin A.E.length => A.E.get j)
        (fun j => AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (hExceptional j)))).inter
      (analytic_finite_union (fun i : Fin E.length => strictAlong T (E.get i))
        (fun i => AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (hOriginal i)))
  have hEachDiscrete : ∀ j : Fin A.E.length,IsDiscrete (A.N ∩ A.E.get j) := by
    intro j
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    obtain ⟨U,hU,hxU,hIso⟩ := exists_actual_curve_member_isolating_open hn hwA.isSNCDivisor hwA.isTransverse
      (hPure x hx.1) j hx.2
    refine ⟨U,hU,Subset.antisymm (fun y hy => hIso ⟨hy.2,hy.1⟩) ?_⟩
    intro y hy
    rw [mem_singleton_iff.mp hy]
    exact ⟨hxU,hx⟩
  have hWhole : IsDiscrete (⋃ j : Fin A.E.length,A.N ∩ A.E.get j) :=
    IsDiscrete.iUnion hEachDiscrete (fun j => hwA.isClosedSubmanifold_N.1.inter (hExceptional j).1)
  have hSub : actualAmbientExceptionalDifference W E T ⊆ ⋃ j : Fin A.E.length,A.N ∩ A.E.get j := by
    intro x hx
    have hx' := hEq ▸ hx
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hx'.1.2
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hH
    exact mem_iUnion.mpr ⟨j,hx'.1.1,hxH⟩
  refine ⟨hAnalytic,?_⟩
  rw [isDiscrete_iff_forall_mem_exists_isOpen] at hWhole ⊢
  intro x hx
  obtain ⟨U,hU,hIso⟩ := hWhole x (hSub hx)
  have hxU : x ∈ U := (hIso.symm ▸ (show x ∈ ({x} : Set Y) from by simp)).1
  refine ⟨U,hU,Subset.antisymm (fun y hy => hIso ▸ ⟨hy.1,hSub hy.2⟩) ?_⟩
  intro y hy
  rw [mem_singleton_iff.mp hy]
  exact ⟨hxU,hx⟩

end
end Hironaka.HironakaSharpActualCurveExceptionalDifference
