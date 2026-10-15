/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveEmptyPadding

/-! Actual unequal terminal recipes are compared after genuine empty padding;
the terminal map is independent of the chosen common length. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveTerminalPaddingComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowerIsomorphism
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveExceptionalDifference
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  NormalCrossings
variable {n : ℕ} {X Y Y' Z Z' : CMfd.{u} n}

/-- The literal centre recipe splits through an ACTUAL tower concatenation,
without deleting any empty positions. -/
theorem actual_difference_recipe_append_iff (W : Set X) (E : List (Set X))
    (P : BlowupTower X Y) (S : BlowupTower Y Z) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower Z V),
      actualAmbientDifferenceSteps W E P (S.append R) ↔
        actualAmbientDifferenceSteps W E P S ∧ actualAmbientDifferenceSteps W E (P.append S) R
  | _,.refl => by simp only [BlowupTower.append_refl,actualAmbientDifferenceSteps,and_true]
  | _,.step R C π hπ => by
    change (actualAmbientDifferenceSteps W E P (S.append R) ∧
        C=actualAmbientExceptionalDifference W E (P.append (S.append R))) ↔
      actualAmbientDifferenceSteps W E P S ∧
        (actualAmbientDifferenceSteps W E (P.append S) R ∧
          C=actualAmbientExceptionalDifference W E ((P.append S).append R))
    rw [actual_difference_recipe_append_iff W E P S R,BlowupTower.append_assoc]
    tauto

/-- The genuine original recipe TEST is supplied BEFORE terminal actual
Delta gives its genuine larger-length padding recipe and true empty endpoint. -/
theorem original_curve_terminal_recipe_padding (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (S : BlowupTower Y Z) (hS : actualAmbientDifferenceSteps W E P S)
    (hD : actualAmbientExceptionalDifference W E (P.append S)=∅)
    (L : ℕ) (hL : S.length≤L) :
    (S.append (identityEmptyTail Z (L-S.length))).length=L ∧
    actualAmbientDifferenceSteps W E P (S.append (identityEmptyTail Z (L-S.length))) ∧
    actualAmbientExceptionalDifference W E
      (P.append (S.append (identityEmptyTail Z (L-S.length))))=∅ := by
  have hTest := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hS
  obtain ⟨hPad,hEmpty⟩ := original_curve_terminal_difference_padding hn hW hE hdense hr
    (P.append S) hTest hD (L-S.length)
  refine ⟨?_,(actual_difference_recipe_append_iff W E P S _).mpr ⟨hS,hPad⟩,?_⟩
  · rw [BlowupTower.length_append,identityEmptyTail_length]
    omega
  · simpa only [BlowupTower.append_assoc] using hEmpty

/-- Actual terminated literal recipes of unequal lengths have unique actual
full comparisons at EVERY common larger length. -/
theorem exists_unique_terminal_recipe_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {P' : BlowupTower X Y'} {P : BlowupTower X Y}
    {χ0 : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) P' P χ0)
    (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z)
    (hS' : actualAmbientDifferenceSteps W E P' S') (hS : actualAmbientDifferenceSteps W E P S)
    (hD' : actualAmbientExceptionalDifference W E (P'.append S')=∅)
    (hD : actualAmbientExceptionalDifference W E (P.append S)=∅)
    (L : ℕ) (hL' : S'.length≤L) (hL : S.length≤L) :
    ∃! e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (P'.append (S'.append (identityEmptyTail Z' (L-S'.length))))
        (P.append (S.append (identityEmptyTail Z (L-S.length)))) e := by
  let M := originalMemberProductMarked W E 1
  have hwM : M.IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hId : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M=M := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
    · simp [MarkedIdeal.pullback]
    · exact BlowupControlledTransform.pullback_id hwM.isCoherent
  have hP' := (IsTowerIso.isGeoTestTower_iff _ hW hwM.isCoherent hiso).mpr hP
  rw [hId] at hP'
  have hLeft := original_curve_terminal_recipe_padding hn hW hE hdense hr P' hP' S' hS' hD' L hL'
  have hRight := original_curve_terminal_recipe_padding hn hW hE hdense hr P hP S hS hD L hL
  obtain ⟨e,_hTail,hFull⟩ := exists_actual_difference_recipe_comparison hn hW hE hdense hr hiso hP
    (S'.append (identityEmptyTail Z' (L-S'.length))) (S.append (identityEmptyTail Z (L-S.length)))
    hLeft.2.1 hRight.2.1 (hLeft.1.trans hRight.1.symm)
  exact ⟨e,hFull,fun e' he' => actual_tower_comparison_unique he' hFull⟩

/-- Genuine empty-tail comparison extends an actual padded stagewise
isomorphism without changing its genuine terminal map. -/
theorem terminal_padding_comparison_extend {X' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    {S' : BlowupTower Y' Z'} {S : BlowupTower Y Z}
    {e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (L r : ℕ) (hL' : S'.length≤L) (hL : S.length≤L)
    (h : IsTowerIso Φ (P'.append (S'.append (identityEmptyTail Z' (L-S'.length))))
      (P.append (S.append (identityEmptyTail Z (L-S.length)))) e) :
    IsTowerIso Φ (P'.append (S'.append (identityEmptyTail Z' ((L+r)-S'.length))))
      (P.append (S.append (identityEmptyTail Z ((L+r)-S.length)))) e := by
  have hh := h.append (identityEmptyTail_isTowerIso e r)
  have hsub' : (L+r)-S'.length=(L-S'.length)+r := by omega
  have hsub : (L+r)-S.length=(L-S.length)+r := by omega
  simpa only [BlowupTower.append_assoc,←identityEmptyTail_append,←hsub',←hsub] using hh

/-- Extend to one TRUE common size and use actual fixed-tower uniqueness;
there is no removal or quotienting of the actual empty-step positions. -/
theorem terminal_padding_comparison_independent {X' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    {S' : BlowupTower Y' Z'} {S : BlowupTower Y Z}
    {e1 e2 : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (L K : ℕ) (hL' : S'.length≤L) (hL : S.length≤L)
    (hK' : S'.length≤K) (hK : S.length≤K)
    (h1 : IsTowerIso Φ (P'.append (S'.append (identityEmptyTail Z' (L-S'.length))))
      (P.append (S.append (identityEmptyTail Z (L-S.length)))) e1)
    (h2 : IsTowerIso Φ (P'.append (S'.append (identityEmptyTail Z' (K-S'.length))))
      (P.append (S.append (identityEmptyTail Z (K-S.length)))) e2) : e1=e2 := by
  have hh1 := terminal_padding_comparison_extend L K hL' hL h1
  have hh2 := terminal_padding_comparison_extend K L hK' hK h2
  rw [Nat.add_comm K L] at hh2
  exact actual_tower_comparison_unique hh1 hh2

end
end Hironaka.HironakaSharpActualCurveTerminalPaddingComparison
