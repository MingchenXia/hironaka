/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveBaseBiholomorphism

/-! Actual finite curve recipes over genuine base biholomorphisms, with
real empty padding at every common terminal cut. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveBiholomorphicRecipes
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveBaseBiholomorphism HironakaSharpActualCurveStageComparison
  HironakaSharpActualCurveFiniteRecipeComparison HironakaSharpActualCurveTerminalPaddingComparison
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveFiniteAmbientDifferencePhase
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualCurveWholeDefectCentre
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowerIsomorphism NormalCrossings
variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}

/-- Real target TEST is internally constructed before genuine Delta centre
naturality in each actual successor, over the SAME arbitrary base map. -/
theorem exists_actual_biholo_difference_recipe_comparison (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    {χ0 : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ P' P χ0)
    (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P) :
    ∀ {V' V : CMfd.{u} n} (S' : BlowupTower Y' V') (S : BlowupTower Y V),
      actualAmbientDifferenceSteps (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) P' S' →
      actualAmbientDifferenceSteps W E P S → S'.length=S.length →
      ∃ e : V' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V,
        IsTowerIso χ0 S' S e ∧ IsTowerIso Φ (P'.append S') (P.append S) e
  | _,_,.refl,.refl,_,_,_ => ⟨χ0,IsTowerIso.refl,hiso⟩
  | _,_,.refl,.step S C π hπ,_,_,hLen => by
    change 0=S.length+1 at hLen
    omega
  | _,_,.step S' C' π' hπ',.refl,_,_,hLen => by
    change S'.length+1=0 at hLen
    omega
  | _,_,.step S' C' π' hπ',.step S C π hπ,hS',hS,hLen => by
    obtain ⟨hS',hC'⟩ := hS'
    obtain ⟨hS,hC⟩ := hS
    have hShort : S'.length=S.length := by
      change S'.length+1=S.length+1 at hLen
      omega
    obtain ⟨χ,hTail,hFull⟩ := exists_actual_biholo_difference_recipe_comparison hn Φ hW hE hdense hr
      hiso hP S' S hS' hS hShort
    have hTest := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hS
    have hCentre := original_curve_difference_biholo_isTowerIso hn Φ hW hE hdense hr hFull hTest
    have hCeq : χ ⁻¹' C=C' := by rw [hC,hC'];exact hCentre.symm
    have hπ'' : IsBlowupAlong n (χ ⁻¹' C) π' := hCeq ▸ hπ'
    obtain ⟨e,hcomm,_huniq⟩ := exists_unique_stage_blowup_comparison χ hπ'' hπ
    have hNext := IsTowerIso.step hTail hπ' hπ e hcomm hCeq
    exact ⟨e,hNext,hiso.append hNext⟩

/-- Both true source inputs and source prefix TEST precede actual terminal
padding; every common cut gives unique actual full history comparison. -/
theorem exists_unique_biholo_terminal_recipe_comparison (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    {χ0 : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ P' P χ0)
    (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z)
    (hS' : actualAmbientDifferenceSteps (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) P' S')
    (hS : actualAmbientDifferenceSteps W E P S)
    (hD' : actualAmbientExceptionalDifference (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) (P'.append S')=∅)
    (hD : actualAmbientExceptionalDifference W E (P.append S)=∅)
    (L : ℕ) (hL' : S'.length≤L) (hL : S.length≤L) :
    ∃! e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso Φ (P'.append (S'.append (identityEmptyTail Z' (L-S'.length))))
        (P.append (S.append (identityEmptyTail Z (L-S.length)))) e := by
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  obtain ⟨hW',hE',hd',hr'⟩ := original_curve_biholo_inputs Φ hW hE hdense hr
  have hP' := (IsTowerIso.isGeoTestTower_iff Φ hW hwM.isCoherent hiso).mpr hP
  rw [pullback_biholo_originalMemberProductMarked hn Φ W hE 1] at hP'
  have hLeft := original_curve_terminal_recipe_padding hn hW' hE' hd' hr' P' hP' S' hS' hD' L hL'
  have hRight := original_curve_terminal_recipe_padding hn hW hE hdense hr P hP S hS hD L hL
  obtain ⟨e,_hTail,hFull⟩ := exists_actual_biholo_difference_recipe_comparison hn Φ hW hE hdense hr
    hiso hP (S'.append (identityEmptyTail Z' (L-S'.length)))
    (S.append (identityEmptyTail Z (L-S.length))) hLeft.2.1 hRight.2.1 (hLeft.1.trans hRight.1.symm)
  exact ⟨e,hFull,fun e' he' => actual_tower_comparison_unique he' hFull⟩

/-- Actual FIRST blowups are compared internally, then their actual
terminating literal tails compare uniquely at EVERY real common cut. -/
theorem exists_unique_biholo_two_phase_recipe_comparison (hn : 0<n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {π' : Y' → X'} {π : Y → X}
    (hπ' : IsBlowupAlong n (chronologicalDistinctDefect (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·))
      (.refl : BlowupTower X' X')) π')
    (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π)
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z)
    (hS' : actualAmbientDifferenceSteps (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) (.step .refl _ π' hπ') S')
    (hS : actualAmbientDifferenceSteps W E (.step .refl _ π hπ) S)
    (hD' : actualAmbientExceptionalDifference (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·))
      ((BlowupTower.step .refl _ π' hπ').append S')=∅)
    (hD : actualAmbientExceptionalDifference W E ((BlowupTower.step .refl _ π hπ).append S)=∅)
    (L : ℕ) (hL' : S'.length≤L) (hL : S.length≤L) :
    ∃! e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso Φ ((BlowupTower.step .refl _ π' hπ').append
        (S'.append (identityEmptyTail Z' (L-S'.length))))
        ((BlowupTower.step .refl _ π hπ).append (S.append (identityEmptyTail Z (L-S.length)))) e := by
  have hBase : IsGeoTestTower (originalMemberProductMarked W E 1) (.refl : BlowupTower X X) := trivial
  obtain ⟨χ,hFirst,_hcomm,_huniq⟩ := exists_original_curve_biholo_first_stage_comparison hn Φ hW hE hdense hr
    (IsTowerIso.refl (Φ := Φ)) hBase hπ' hπ
  have hP : IsGeoTestTower (originalMemberProductMarked W E 1) (BlowupTower.step .refl _ π hπ) :=
    ⟨hBase,(original_curve_whole_defect_admissible hn hW hE hdense hr .refl hBase).1⟩
  exact exists_unique_biholo_terminal_recipe_comparison hn Φ hW hE hdense hr hFirst hP S' S
    hS' hS hD' hD L hL' hL

end
end Hironaka.HironakaSharpActualCurveBiholomorphicRecipes
