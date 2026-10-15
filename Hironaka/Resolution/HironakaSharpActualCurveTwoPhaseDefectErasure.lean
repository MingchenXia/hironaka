/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveFiniteAmbientDifferencePhase
import Hironaka.Resolution.HironakaSharpActualCurveFirstDefectErasure

/-! Actual FIRST-Z emptiness preservation and TWO real original curve phases.
True new distinct counts are constructed; no locus or driver certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveTwoPhaseDefectErasure
noncomputable section
open HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveFirstDefectErasure
  Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveWholeDefectCentre HironakaSharpActualCurveExceptionalResidualUnit
  HironakaSharpActualFirstGoodCurveBase HironakaSharpActualFirstGoodReducedTraces
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualOriginalDynamicStep
  HironakaSharpOriginalMemberProductDomain HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  HironakaCoherentTransformExtension RelativePrincipalizationSpan DivisorExponentAlong
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers
  NonmonomialOrderLocal RestrictedIdealExtension
open ResolutionInvariantDriver StepOneLowerDomain
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Real ANY original-admissible step preserves FIRST-Z emptiness, with
independently constructed NEW proper and genuine quotient-image counts. -/
theorem original_curve_first_defect_empty_preserved_step (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    (hEmpty : chronologicalDistinctDefect W E T=∅)
    {C : Set Y} (hC : (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C)
    {π : Z → Y} (hπ : IsBlowupAlong n C π) :
    chronologicalDistinctDefect W E (.step T C π hπ)=∅ := by
  let M := originalMemberProductMarked W E 1
  let T' := BlowupTower.step T C π hπ
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  have hT' : IsGeoTestTower M T' := ⟨hT,hC⟩
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  have hGeom' := actual_original_test_history_template M hInit.isWellFormed T' hT'
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwOld := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hGeom
  have hwNew := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T' hGeom'
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  by_cases hzC : π z ∈ C
  · have hzE : z ∈ ⋃ H ∈ (geoTransformAlong (geometricTemplate W []) T').E,H := by
      change z ∈ ⋃ H ∈ ((geoTransformAlong (geometricTemplate W []) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]),H
      exact mem_iUnion₂.mpr ⟨π ⁻¹' C,by simp,hzC⟩
    exact (original_curve_exceptional_residual_units_and_defect_disjoint hn hW hE hdense hr T' hGeom' z hz.1 hzE).2.2 hz
  · have hmaps := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage (C := C)
      hπ.contMDiff.continuous hwOld.isClosedSubmanifold_N.1
    have hzOld : π z ∈ (geoTransformAlong (geometricTemplate W []) T).N := hmaps hz.1
    have hxGood : π z ∉ chronologicalDistinctDefect W E T := by rw [hEmpty];simp
    have hOldLE := original_curve_first_good_order_le_one hn hW hE hdense hr T hGeom hzOld hxGood
    have hold := (original_product_nmOrd_eq_current hn hW hE hdense 1 T hT (π z)).trans
      (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hGeom (π z))
    have hnew := (original_product_nmOrd_eq_current hn hW hE hdense 1 T' hT' z).trans
      (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T' hGeom' z)
    have heq := nmOrd_geoTransform_of_notMem hn hDom hC hπ hzC
    change nmOrd (geoTransformAlong M T') z=nmOrd (geoTransformAlong M T) (π z) at heq
    have hNewLE : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T').N
        (chronologicalMemberProduct W E T') z ≤ 1 := by
      rw [←hnew,heq,hold]
      exact hOldLE
    let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal
    have hfam : ∀ i : Fin E.length,(F i).IsCoherent ∧
        (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T').N,
          IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T').N (F i) y) ∧
        ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T').N,∃ f : Z → ℂ,HolomorphicAt n f y ∧
          ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧
            IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T').N (·=f) y a := by
      intro i
      obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T' hGeom'
      rw [hNi] at hnzi hpri
      exact ⟨hwi.isCoherent,hnzi,hpri⟩
    rw [chronological_product_eq_actual_family_product W E T'] at hNewLE
    exact (actual_product_order_le_one_count_dictionary hwNew.isClosedSubmanifold_N
      (fun i => (hfam i).1) (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hz.1 hNewLE).2.2 hz


/-- Every real ORIGINAL test continuation preserves actual FIRST-Z emptiness. -/
theorem original_curve_first_defect_empty_preserved_tail (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hEmpty : chronologicalDistinctDefect W E P=∅) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),IsGeoTestTower (originalMemberProductMarked W E 1) (P.append S) →
      chronologicalDistinctDefect W E (P.append S)=∅
  | _,.refl,_ => hEmpty
  | _,.step S C π hπ,hT => by
    have hOld := original_curve_first_defect_empty_preserved_tail hn hW hE hdense hr P hEmpty S hT.1
    exact original_curve_first_defect_empty_preserved_step hn hW hE hdense hr (P.append S) hT.1 hOld hT.2 hπ


/-- ONLY original curve inputs and compact CURRENT cosupport construct the
SAME original actual FIRST-Z step then literal finite Delta erasure phase. -/
theorem exists_original_curve_two_actual_defect_erasure_phases (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (hK : IsCompact (geoTransformAlong (originalMemberProductMarked W E 1) P).cosupp) :
    ∃ (Y' : CMfd.{u} n) (π : Y' → Y) (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E P) π)
      (Z : CMfd.{u} n) (S : BlowupTower Y' Z),
      actualAmbientDifferenceSteps W E (BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ) S ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) ((BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ).append S) ∧
      chronologicalDistinctDefect W E ((BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ).append S)=∅ ∧
      HironakaSharpActualCurveExceptionalDifference.actualAmbientExceptionalDifference W E
        ((BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ).append S)=∅ ∧
      IsProperMap ((BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ).append S).proj ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1)
        ((BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ).append S)) ∧
      IsSNCDivisor n (geoTransformAlong (originalMemberProductMarked W E 1)
        ((BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ).append S)).E := by
  let M := originalMemberProductMarked W E 1
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit P hP
  obtain ⟨Y',π,hπ,hproper,_hHol,_hIso,hFirstTest,hFirstDom,_hFirstSNC,hFirstEmpty⟩ :=
    exists_original_curve_first_defect_erasing_step hn hW hE hdense hr P hP
  let P' := BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ
  have hC := (original_curve_whole_defect_admissible hn hW hE hdense hr P hP).1
  have hsub : (geoTransformAlong M P').cosupp ⊆ π ⁻¹' (geoTransformAlong M P).cosupp := by
    intro z hz
    have hz' : z ∈ (geoTransformAlong (geoTransformAlong M P)
        (.step .refl (chronologicalDistinctDefect W E P) π hπ)).cosupp := hz
    exact proj_mem_cosupp_of_mem_cosupp hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent
      (.step .refl (chronologicalDistinctDefect W E P) π hπ) ⟨trivial,hC⟩ hz'
  have hclosed := GiraudAlong.isClosed_cosupport_along hFirstDom.isWellFormed.isCoherent
    hFirstDom.isWellFormed.isClosedSubmanifold_N (geoTransformAlong M P').d
  have hK' : IsCompact (geoTransformAlong M P').cosupp :=
    (hproper.isCompact_preimage hK).of_isClosed_subset hclosed hsub
  obtain ⟨Z,S,hs,hFinalTest,hDelta,_hTailProper,hFinalDom,hSNC⟩ :=
    exists_original_curve_finite_ambient_difference_phase hn hW hE hdense hr P' hFirstTest hK'
  have hFirst := original_curve_first_defect_empty_preserved_tail hn hW hE hdense hr P' hFirstEmpty S hFinalTest
  exact ⟨Y',π,hπ,Z,S,hs,hFinalTest,hFirst,hDelta,HironakaLocalPrincipalization.isProperMap_proj _,hFinalDom,hSNC⟩

end
end Hironaka.HironakaSharpActualCurveTwoPhaseDefectErasure
