/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveBiholomorphicRecipes
import Hironaka.Invariant.MaxLocusLocal

/-! Actual intersections and retained sharp curve histories; every empty
trace centre remains a genuine successor. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveOverlapMaps
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveBiholomorphicRecipes HironakaSharpActualCurveBaseBiholomorphism
  HironakaSharpActualCurveDefectRestriction HironakaSharpActualCurveRecipeOpenRestriction
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualCurveStageComparison
  HironakaSharpActualCurveWholeDefectCentre HironakaSharpActualCurveEmptyPadding
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalDeepProductBlowup MaxLocusLocal MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupRestrictOpen NormalCrossings NormalCrossingsInvariance
variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual identity-on-points biholomorphism between the two nested
presentations of the genuine intersection, with both true inverse laws. -/
def commonOpenBase (U V O : Opens X) (hOU : O≤U) (hOV : O≤V) :
    CMfd.of (n := n) (nestedOpens U O) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V O) :=
  (nestedOpensDiffeo (n := n) hOU).trans
    (nestedOpensDiffeo (n := n) hOV).symm

private theorem actual_original_open_inputs {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (U : Opens X) :
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    IsClosedSubmanifold n WU ∧ IsSNCDivisor n EU ∧
      WU ⊆ closure (WU \ ⋃ H ∈ EU,H) ∧ ∀ x ∈ WU,RegularAtDim (n := n) WU x 1 := by
  refine ⟨isClosedSubmanifold_preimage_val hW U,
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE,?_,
    fun x hx => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr x.val hx)⟩
  intro y hy
  have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
  erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
    continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

/-- Actual twice-restricted original carrier and EVERY ordered member give
ALL FOUR whole product fields over the genuine intersection base map. -/
theorem common_open_original_product_dictionary (hn : 0<n) (W : Set X)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (U V O : Opens X) (hOU : O≤U) (hOV : O≤V) (q : ℕ) :
    let AU := nestedOpens U O
    let AV := nestedOpens V O
    let WU := (Subtype.val : U → X) ⁻¹' W
    let WV := (Subtype.val : V → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
    (Subtype.val : AU → U) ⁻¹' WU=(commonOpenBase U V O hOU hOV) ⁻¹' ((Subtype.val : AV → V) ⁻¹' WV) ∧
    EU.map ((Subtype.val : AU → U) ⁻¹' ·)=
      (EV.map ((Subtype.val : AV → V) ⁻¹' ·)).map ((commonOpenBase U V O hOU hOV) ⁻¹' ·) ∧
    MarkedIdeal.pullback (commonOpenBase U V O hOU hOV)
      (originalMemberProductMarked (X := CMfd.of (n := n) AV)
        ((Subtype.val : AV → V) ⁻¹' WV) (EV.map ((Subtype.val : AV → V) ⁻¹' ·)) q)=
      originalMemberProductMarked (X := CMfd.of (n := n) AU)
        ((Subtype.val : AU → U) ⁻¹' WU) (EU.map ((Subtype.val : AU → U) ⁻¹' ·)) q := by
  let AU := nestedOpens U O
  let AV := nestedOpens V O
  have hCarrier : (Subtype.val : AU → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' W)=
      (commonOpenBase U V O hOU hOV) ⁻¹' ((Subtype.val : AV → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' W)) := rfl
  have hFamily : (E.map ((Subtype.val : U → X) ⁻¹' ·)).map ((Subtype.val : AU → U) ⁻¹' ·)=
      ((E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : AV → V) ⁻¹' ·)).map
        ((commonOpenBase U V O hOU hOV) ⁻¹' ·) := by
    simp only [List.map_map]
    rfl
  have hEV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE
  have hEAV := isSNCDivisor_map_preimage (pullsBackCoordinates_val AV) continuous_subtype_val hEV
  refine ⟨hCarrier,hFamily,?_⟩
  rw [pullback_biholo_originalMemberProductMarked hn (commonOpenBase U V O hOU hOV) _ hEAV q,←hCarrier,←hFamily]

/-- The actual trace centres of TWO independent local FIRST blowups match
on the real intersection BEFORE constructing the next biholomorphism. -/
theorem exists_actual_common_open_first_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (U V O : Opens X) (hOU : O≤U) (hOV : O≤V)
    {YU YV : CMfd.{u} n} {πU : YU → CMfd.of (n := n) U} {πV : YV → CMfd.of (n := n) V}
    (hπU : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))) πU)
    (hπV : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) V) (CMfd.of (n := n) V))) πV) :
    let AU := nestedOpens U O
    let AV := nestedOpens V O
    let PU := BlowupTower.step .refl _ πU hπU
    let PV := BlowupTower.step .refl _ πV hπV
    ∃ e : CMfd.of (n := n) (openPreimage PU AU) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage PV AV),
      IsTowerIso (commonOpenBase U V O hOU hOV) (restrict AU PU) (restrict AV PV) e := by
  let AU := nestedOpens U O
  let AV := nestedOpens V O
  let PU := BlowupTower.step .refl _ πU hπU
  let PV := BlowupTower.step .refl _ πV hπV
  obtain ⟨hWU,hEU,hdU,hrU⟩ := actual_original_open_inputs hW hE hdense hr U
  obtain ⟨hWV,hEV,hdV,hrV⟩ := actual_original_open_inputs hW hE hdense hr V
  obtain ⟨hWAV,hEAV,hdAV,hrAV⟩ := actual_original_open_inputs (X := CMfd.of (n := n) V) hWV hEV hdV hrV AV
  obtain ⟨hCarrier,hFamily,_hRecord⟩ := common_open_original_product_dictionary hn W hE U V O hOU hOV 1
  have hNat := original_curve_first_defect_biholo_isTowerIso hn (commonOpenBase U V O hOU hOV)
    hWAV hEAV hdAV hrAV (IsTowerIso.refl (Φ := commonOpenBase U V O hOU hOV)) trivial
  rw [←hCarrier,←hFamily] at hNat
  have hFU := original_curve_first_defect_restrict (X := CMfd.of (n := n) U) hn hWU hEU hdU hrU .refl trivial AU
  have hFV := original_curve_first_defect_restrict (X := CMfd.of (n := n) V) hn hWV hEV hdV hrV .refl trivial AV
  let CU := chronologicalDistinctDefect ((Subtype.val : U → X) ⁻¹' W)
    (E.map ((Subtype.val : U → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))
  let CV := chronologicalDistinctDefect ((Subtype.val : V → X) ⁻¹' W)
    (E.map ((Subtype.val : V → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) V) (CMfd.of (n := n) V))
  have hC : (commonOpenBase U V O hOU hOV) ⁻¹' ((Subtype.val : AV → V) ⁻¹' CV)=
      (Subtype.val : AU → U) ⁻¹' CU := by
    exact (congrArg (fun C : Set (CMfd.of (n := n) AV) => (commonOpenBase U V O hOU hOV) ⁻¹' C)
      hFV.symm).trans (hNat.symm.trans hFU)
  let pU : openPreimage PU AU → AU := fun z => ⟨πU z.val,z.property⟩
  let pV : openPreimage PV AV → AV := fun z => ⟨πV z.val,z.property⟩
  have hpU : IsBlowupAlong n ((Subtype.val : AU → U) ⁻¹' CU) pU :=
    isBlowupAlong_restrict hπU AU (AU.isOpen.preimage hπU.contMDiff.continuous)
  have hpV : IsBlowupAlong n ((Subtype.val : AV → V) ⁻¹' CV) pV :=
    isBlowupAlong_restrict hπV AV (AV.isOpen.preimage hπV.contMDiff.continuous)
  have hpU' : IsBlowupAlong n ((commonOpenBase U V O hOU hOV) ⁻¹' ((Subtype.val : AV → V) ⁻¹' CV)) pU := hC ▸ hpU
  obtain ⟨e,hcomm,_huniq⟩ := exists_unique_stage_blowup_comparison
    (Z' := CMfd.of (n := n) (openPreimage PU AU))
    (Z := CMfd.of (n := n) (openPreimage PV AV)) (commonOpenBase U V O hOU hOV) hpU' hpV
  exact ⟨e,IsTowerIso.step (IsTowerIso.refl (Φ := commonOpenBase U V O hOU hOV)) hpU hpV e hcomm hC⟩

/-- TWO actual retained local recipes yield a unique actual comparison on
the genuine intersection, without supplied intersection geometry or TEST. -/
theorem exists_unique_actual_common_open_recipe_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (U V O : Opens X) (hOU : O≤U) (hOV : O≤V)
    {YU YV ZU ZV : CMfd.{u} n} {πU : YU → CMfd.of (n := n) U} {πV : YV → CMfd.of (n := n) V}
    (hπU : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))) πU)
    (hπV : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) V) (CMfd.of (n := n) V))) πV)
    (SU : BlowupTower YU ZU) (SV : BlowupTower YV ZV)
    (hSU : actualAmbientDifferenceSteps ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (.step .refl _ πU hπU) SU)
    (hSV : actualAmbientDifferenceSteps ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) (.step .refl _ πV hπV) SV)
    (hDU : actualAmbientExceptionalDifference ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) ((BlowupTower.step .refl _ πU hπU).append SU)=∅)
    (hDV : actualAmbientExceptionalDifference ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) ((BlowupTower.step .refl _ πV hπV).append SV)=∅)
    (L : ℕ) (hLU : SU.length≤L) (hLV : SV.length≤L) :
    let AU := nestedOpens U O
    let AV := nestedOpens V O
    let PU := BlowupTower.step .refl _ πU hπU
    let PV := BlowupTower.step .refl _ πV hπV
    let TU := restrict (openPreimage PU AU) SU
    let TV := restrict (openPreimage PV AV) SV
    ∃! e : CMfd.of (n := n) (openPreimage SU (openPreimage PU AU)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage SV (openPreimage PV AV)),
      IsTowerIso (commonOpenBase U V O hOU hOV)
        ((restrict AU PU).append (TU.append (identityEmptyTail
          (CMfd.of (n := n) (openPreimage SU (openPreimage PU AU))) (L-SU.length))))
        ((restrict AV PV).append (TV.append (identityEmptyTail
          (CMfd.of (n := n) (openPreimage SV (openPreimage PV AV))) (L-SV.length)))) e := by
  let AU := nestedOpens U O
  let AV := nestedOpens V O
  let PU := BlowupTower.step .refl _ πU hπU
  let PV := BlowupTower.step .refl _ πV hπV
  obtain ⟨hWU,hEU,hdU,hrU⟩ := actual_original_open_inputs hW hE hdense hr U
  obtain ⟨hWV,hEV,hdV,hrV⟩ := actual_original_open_inputs hW hE hdense hr V
  obtain ⟨hWAV,hEAV,hdAV,hrAV⟩ := actual_original_open_inputs (X := CMfd.of (n := n) V) hWV hEV hdV hrV AV
  have hPU : IsGeoTestTower (originalMemberProductMarked ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) PU :=
    ⟨trivial,(original_curve_whole_defect_admissible (X := CMfd.of (n := n) U)
      hn hWU hEU hdU hrU .refl trivial).1⟩
  have hPV : IsGeoTestTower (originalMemberProductMarked ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) 1) PV :=
    ⟨trivial,(original_curve_whole_defect_admissible (X := CMfd.of (n := n) V)
      hn hWV hEV hdV hrV .refl trivial).1⟩
  have hRetU := original_curve_terminal_difference_recipe_restrict hn hWU hEU hdU hrU PU hPU SU hSU hDU AU
  have hRetV := original_curve_terminal_difference_recipe_restrict hn hWV hEV hdV hrV PV hPV SV hSV hDV AV
  have hTarget := isGeoTestTower_restrict AV hWV (isCoherent_originalMemberProduct hn hEV) PV hPV
  rw [pullback_val_originalMemberProductMarked (X := CMfd.of (n := n) V)
    hn ((Subtype.val : V → X) ⁻¹' W) hEV 1 AV] at hTarget
  obtain ⟨χ,hIso⟩ := exists_actual_common_open_first_comparison hn hW hE hdense hr U V O hOU hOV hπU hπV
  obtain ⟨hCarrier,hFamily,_hRecord⟩ := common_open_original_product_dictionary hn W hE U V O hOU hOV 1
  have hCompare := exists_unique_biholo_terminal_recipe_comparison hn (commonOpenBase U V O hOU hOV)
    hWAV hEAV hdAV hrAV hIso hTarget (restrict (openPreimage PU AU) SU) (restrict (openPreimage PV AV) SV)
  rw [←hCarrier,←hFamily] at hCompare
  simpa only [length_restrict] using hCompare hRetU.1 hRetV.1 hRetU.2.2.2 hRetV.2.2.2 L
    (by simpa only [length_restrict] using hLU) (by simpa only [length_restrict] using hLV)

/-- The literal actual pairwise intersection is chosen internally. -/
theorem exists_unique_actual_overlap_recipe_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (U V : Opens X)
    {YU YV ZU ZV : CMfd.{u} n} {πU : YU → CMfd.of (n := n) U} {πV : YV → CMfd.of (n := n) V}
    (hπU : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))) πU)
    (hπV : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) V) (CMfd.of (n := n) V))) πV)
    (SU : BlowupTower YU ZU) (SV : BlowupTower YV ZV)
    (hSU : actualAmbientDifferenceSteps ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (.step .refl _ πU hπU) SU)
    (hSV : actualAmbientDifferenceSteps ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) (.step .refl _ πV hπV) SV)
    (hDU : actualAmbientExceptionalDifference ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) ((BlowupTower.step .refl _ πU hπU).append SU)=∅)
    (hDV : actualAmbientExceptionalDifference ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) ((BlowupTower.step .refl _ πV hπV).append SV)=∅)
    (L : ℕ) (hLU : SU.length≤L) (hLV : SV.length≤L) :
    let AU := nestedOpens U (U⊓V)
    let AV := nestedOpens V (U⊓V)
    let PU := BlowupTower.step .refl _ πU hπU
    let PV := BlowupTower.step .refl _ πV hπV
    let TU := restrict (openPreimage PU AU) SU
    let TV := restrict (openPreimage PV AV) SV
    ∃! e : CMfd.of (n := n) (openPreimage SU (openPreimage PU AU)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage SV (openPreimage PV AV)),
      IsTowerIso (commonOpenBase U V (U⊓V) inf_le_left inf_le_right)
        ((restrict AU PU).append (TU.append (identityEmptyTail
          (CMfd.of (n := n) (openPreimage SU (openPreimage PU AU))) (L-SU.length))))
        ((restrict AV PV).append (TV.append (identityEmptyTail
          (CMfd.of (n := n) (openPreimage SV (openPreimage PV AV))) (L-SV.length)))) e :=
  exists_unique_actual_common_open_recipe_comparison hn hW hE hdense hr U V (U⊓V) inf_le_left inf_le_right
    hπU hπV SU SV hSU hSV hDU hDV L hLU hLV

end
end Hironaka.HironakaSharpActualCurveOverlapMaps
