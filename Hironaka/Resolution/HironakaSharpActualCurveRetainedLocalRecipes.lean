/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveRecipeOpenRestriction

/-! Original local sharp endpoints retain their ACTUAL first blowup and
terminating literal-difference tail, with no caller compact window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveRetainedLocalRecipes
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveRecipeOpenRestriction HironakaSharpActualCurveLocalSharpEndpoints
  HironakaSharpActualCurveTwoPhaseDefectErasure HironakaSharpActualCurveWholeBoundaryTransversality
  HironakaSharpActualCurveTwoPhaseIsomorphism HironakaSharpActualCurveInitialGoodPreservation
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalDeepProductBlowup HironakaSharpOriginalMultiBoundaryBadLocus
  NormalCrossings NormalCrossingsInvariance MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  HomogenizedGlueingTower HironakaCoherentTransformExtension
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Start with the actual FIRST-Z blowup and literal terminating Delta tail;
prove sharp endpoint geometry for THOSE SAME real witnesses. -/
theorem exists_original_curve_retained_sharp_recipe (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (hK : IsCompact (originalMemberProductMarked W E 1).cosupp) :
    ∃ (Y : CMfd.{u} n) (π : Y → X)
      (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π)
      (Z : CMfd.{u} n) (S : BlowupTower Y Z),
      let P := BlowupTower.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ
      actualAmbientDifferenceSteps W E P S ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) (P.append S) ∧
      chronologicalDistinctDefect W E (P.append S)=∅ ∧
      actualAmbientExceptionalDifference W E (P.append S)=∅ ∧
      IsProperMap (P.append S).proj ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1) (P.append S)) ∧
      IsSNCDivisor n (E.map (strictAlong (P.append S)) ++
        (geoTransformAlong (geometricTemplate W []) (P.append S)).E) ∧
      IsTransverse n (geoTransformAlong (geometricTemplate W []) (P.append S)).N
        (E.map (strictAlong (P.append S)) ++ (geoTransformAlong (geometricTemplate W []) (P.append S)).E) ∧
      IsIsomorphismOver n (P.append S).proj (originalGoodLocus (n := n) W E) := by
  obtain ⟨Y,π,hπ,Z,S,hRecipe,hTest,hZ,hD,hProper,hDom,_hSNC⟩ :=
    exists_original_curve_two_actual_defect_erasure_phases hn hW hE hdense hr .refl trivial hK
  let P := BlowupTower.step .refl (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π hπ
  have hP : IsGeoTestTower (originalMemberProductMarked W E 1) P :=
    ((isGeoTestTower_append_iff _ P S).mp hTest).1
  have hIso := (actual_first_defect_then_difference_tail_isomorphism hn hW hE hdense hr hπ hP S hRecipe).2
  have hGood := original_curve_initial_good_subset_first_defect_complement hn hW hE hdense hr
  have hGoodIso : IsIsomorphismOver n (P.append S).proj (originalGoodLocus (n := n) W E) := by
    refine ⟨⟨fun y hy => hy,?_,?_⟩,?_⟩
    · intro y hy y' hy' heq
      exact hIso.1.2.1 (hGood hy) (hGood hy') heq
    · intro x hx
      obtain ⟨y,hy,heq⟩ := hIso.1.2.2 (hGood hx)
      exact ⟨y,by change (P.append S).proj y ∈ originalGoodLocus (n := n) W E;rw [heq];exact hx,heq⟩
    · exact disjoint_left.mpr fun y hy hexc => disjoint_left.mp hIso.2 (hGood hy) hexc
  exact ⟨Y,π,hπ,Z,S,hRecipe,hTest,hZ,hD,hProper,hDom,
    original_curve_whole_ambient_boundary_isSNC hn hW hE hdense hr _ hTest,
    original_curve_two_empty_defects_whole_boundary_transverse hn hW hE hdense hr _ hTest hZ hD,hGoodIso⟩

/-- ONLY original curve data/ANY point construct the actual compact open,
WHOLE initial pullback and retained real local two-phase sharp recipe. -/
theorem exists_original_curve_retained_local_recipe (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (x : X) :
    ∃ U : Opens X,x ∈ U ∧
      let WU := (Subtype.val : U → X) ⁻¹' W
      let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
      MarkedIdeal.pullback (Subtype.val : U → X) (originalMemberProductMarked W E 1)=
        originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1 ∧
      ∃ (Y : CMfd.{u} n) (π : Y → U)
        (hπ : IsBlowupAlong n (chronologicalDistinctDefect WU EU
          (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))) π)
        (Z : CMfd.{u} n) (S : BlowupTower Y Z),
        let P := BlowupTower.step .refl (chronologicalDistinctDefect WU EU
          (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))) π hπ
        actualAmbientDifferenceSteps WU EU P S ∧
        IsGeoTestTower (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1) (P.append S) ∧
        chronologicalDistinctDefect WU EU (P.append S)=∅ ∧
        actualAmbientExceptionalDifference WU EU (P.append S)=∅ ∧
        IsProperMap (P.append S).proj ∧
        IsInvDomain 1 (geoTransformAlong
          (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1) (P.append S)) ∧
        IsSNCDivisor n (EU.map (strictAlong (P.append S)) ++
          (geoTransformAlong (geometricTemplate WU []) (P.append S)).E) ∧
        IsTransverse n (geoTransformAlong (geometricTemplate WU []) (P.append S)).N
          (EU.map (strictAlong (P.append S)) ++ (geoTransformAlong (geometricTemplate WU []) (P.append S)).E) ∧
        IsIsomorphismOver n (P.append S).proj (originalGoodLocus (n := n) WU EU) := by
  let M := originalMemberProductMarked W E 1
  have hM : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun y hy => ⟨1,le_rfl,hr y hy⟩,le_rfl,
      fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy⟩
  obtain ⟨U,hxU,hK⟩ := exists_actual_curve_compact_cosupport_open M hM x
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  have hWhole : MarkedIdeal.pullback (Subtype.val : U → X) M=
      originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1 :=
    pullback_val_originalMemberProductMarked hn W hE 1 U
  have hDom := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hWU : IsClosedSubmanifold n WU := hDom.isWellFormed.isClosedSubmanifold_N
  have hEU : IsSNCDivisor n EU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hrU : ∀ y ∈ WU,RegularAtDim (n := n) WU y 1 :=
    fun y hy => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr y.val hy)
  have hdU : WU ⊆ closure (WU \ ⋃ H ∈ EU,H) := by
    intro y hy
    have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp [WU,EU]
  have hKU : IsCompact (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1).cosupp := by
    rw [←hWhole]
    exact hK
  exact ⟨U,hxU,hWhole,exists_original_curve_retained_sharp_recipe
    (X := CMfd.of (n := n) U) hn hWU hEU hdU hrU hKU⟩

end
end Hironaka.HironakaSharpActualCurveRetainedLocalRecipes
