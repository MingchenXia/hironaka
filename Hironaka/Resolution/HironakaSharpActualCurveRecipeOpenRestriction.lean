/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupTowerRestrictLengthExact
import Hironaka.Resolution.HironakaSharpActualCurveTerminalPaddingComparison

/-! Genuine original literal difference recipes restrict to actual base opens,
retaining every position and independently computed endpoint difference. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveRecipeOpenRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealRestrictOpen
  HironakaSharpActualCurveDefectRestriction HironakaSharpActualCurveStageComparison
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveExceptionalDifference
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalDeepProductBlowup
  NormalCrossings NormalCrossingsInvariance BlowupRestrictOpen
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem actual_original_curve_open_inputs {W : Set X} {E : List (Set X)}
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

/-- True restricted original TEST and actual append-restriction isomorphism
precede BOTH directions of the computed full-prefix Delta dictionary. -/
theorem original_curve_restricted_full_prefix_difference (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (S : BlowupTower Y Z)
    (hPS : IsGeoTestTower (originalMemberProductMarked W E 1) (P.append S)) (U : Opens X) :
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    IsGeoTestTower (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1)
      ((restrict U P).append (restrict (openPreimage P U) S)) ∧
    actualAmbientExceptionalDifference WU EU ((restrict U P).append (restrict (openPreimage P U) S))=
      (Subtype.val : openPreimage S (openPreimage P U) → Z) ⁻¹'
        actualAmbientExceptionalDifference W E (P.append S) := by
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let MU := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1
  obtain ⟨hWU,hEU,hdU,hrU⟩ := actual_original_curve_open_inputs hW hE hdense hr U
  have hcoh := isCoherent_originalMemberProduct hn hE
  have hcohU := isCoherent_originalMemberProduct hn hEU
  have hRestricted := isGeoTestTower_restrict U hW hcoh (P.append S) hPS
  rw [pullback_val_originalMemberProductMarked hn W hE 1 U] at hRestricted
  let χ := opensCongr (n := n) (openPreimage_append P S U).symm
  have hIso := isTowerIso_restrict_append U P S
  have hId : MarkedIdeal.pullback
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) MU=MU := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
    · simp [MarkedIdeal.pullback]
    · exact BlowupControlledTransform.pullback_id hcohU
  have hTests := IsTowerIso.isGeoTestTower_iff (𝔪 := MU) _ hWU hcohU hIso
  rw [hId] at hTests
  have hConcat := hTests.mp hRestricted
  have hDIso := original_curve_actual_difference_isTowerIso hn hWU hEU hdU hrU hIso hConcat
  have hDRestrict := original_curve_actual_difference_restrict hn hW hE hdense hr (P.append S) hPS U
  refine ⟨hConcat,?_⟩
  apply Set.preimage_injective.mpr χ.surjective
  exact hDIso.symm.trans hDRestrict

/-- Every original actual literal recipe restricts to the ACTUAL restricted
prefix and tail, retaining even centres whose open trace becomes empty. -/
theorem original_curve_difference_recipe_restrict (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P) (U : Opens X) :
    ∀ {V : CMfd.{u} n} (S : BlowupTower Y V),actualAmbientDifferenceSteps W E P S →
      actualAmbientDifferenceSteps ((Subtype.val : U → X) ⁻¹' W)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U P) (restrict (openPreimage P U) S) ∧
      (restrict (openPreimage P U) S).length=S.length
  | _,.refl,_ => ⟨trivial,rfl⟩
  | _,.step S C π hπ,hS => by
    obtain ⟨hRecipe,hLen⟩ := original_curve_difference_recipe_restrict hn hW hE hdense hr P hP U S hS.1
    have hTest := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hS.1
    have hDelta := (original_curve_restricted_full_prefix_difference hn hW hE hdense hr P S hTest U).2
    refine ⟨⟨hRecipe,?_⟩,length_restrict (openPreimage P U) (.step S C π hπ)⟩
    rw [hS.2]
    exact hDelta.symm

/-- Actual recipe, original TEST and true empty computed endpoint difference
are all supplied on EVERY genuine base open, with every step retained. -/
theorem original_curve_terminal_difference_recipe_restrict (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (S : BlowupTower Y Z) (hS : actualAmbientDifferenceSteps W E P S)
    (hD : actualAmbientExceptionalDifference W E (P.append S)=∅) (U : Opens X) :
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    actualAmbientDifferenceSteps WU EU (restrict U P) (restrict (openPreimage P U) S) ∧
    (restrict (openPreimage P U) S).length=S.length ∧
    IsGeoTestTower (originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1)
      ((restrict U P).append (restrict (openPreimage P U) S)) ∧
    actualAmbientExceptionalDifference WU EU ((restrict U P).append (restrict (openPreimage P U) S))=∅ := by
  have hRecipe := original_curve_difference_recipe_restrict hn hW hE hdense hr P hP U S hS
  have hTest := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hS
  have hWhole := original_curve_restricted_full_prefix_difference hn hW hE hdense hr P S hTest U
  refine ⟨hRecipe.1,hRecipe.2,hWhole.1,?_⟩
  rw [hWhole.2,hD,Set.preimage_empty]

end
end Hironaka.HironakaSharpActualCurveRecipeOpenRestriction
