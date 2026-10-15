/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStageComparison

/-! Actual finite equal-length sharp-curve recipes have unique stagewise
comparisons. Empty centres remain genuine successor steps. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveFiniteRecipeComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveStageComparison HironakaSharpActualCurveFiniteAmbientDifferencePhase
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualCurveWholeDefectCentre
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowerIsomorphism
variable {n : ℕ} {X Y Y' : CMfd.{u} n}

/-- Genuine stagewise isomorphisms of the SAME actual towers over a fixed
base map have one terminal map, by true one-step universal uniqueness. -/
theorem actual_tower_comparison_unique {X' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {e1 e2 : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h1 : IsTowerIso Φ T' T e1) (h2 : IsTowerIso Φ T' T e2) : e1=e2 := by
  induction h1 with
  | refl => exact (IsTowerIso.refl_inv h2).symm
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ e hcomm hC ih =>
    obtain ⟨ψ,hψ,hψcomm,_hψC⟩ := h2.step_inv
    have hEq := ih hψ
    subst ψ
    have hπ'' : IsBlowupAlong n (χ ⁻¹' C) π' := hC ▸ hπ'
    obtain ⟨d,_hd,huniq⟩ := exists_unique_stage_blowup_comparison χ hπ'' hπ
    have he := huniq e e.contMDiff hcomm
    have he2 := huniq e2 e2.contMDiff hψcomm
    apply Diffeomorph.ext
    intro z
    exact congrFun (he.trans he2.symm) z

/-- Actual literal-Delta recipes construct corresponding finite tail/full
histories; every previous original TEST is supplied before centre naturality. -/
theorem exists_actual_difference_recipe_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {P' : BlowupTower X Y'} {P : BlowupTower X Y}
    {χ0 : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) P' P χ0)
    (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P) :
    ∀ {Z' Z : CMfd.{u} n} (S' : BlowupTower Y' Z') (S : BlowupTower Y Z),
      actualAmbientDifferenceSteps W E P' S' → actualAmbientDifferenceSteps W E P S →
      S'.length=S.length →
      ∃ e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
        IsTowerIso χ0 S' S e ∧
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) (P'.append S') (P.append S) e
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
    obtain ⟨χ,hTail,hFull⟩ := exists_actual_difference_recipe_comparison hn hW hE hdense hr hiso hP S' S hS' hS hShort
    have hTest := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hS
    have hCentre := original_curve_actual_difference_isTowerIso hn hW hE hdense hr hFull hTest
    have hCeq : χ ⁻¹' C=C' := by rw [hC,hC'];exact hCentre.symm
    have hπ'' : IsBlowupAlong n (χ ⁻¹' C) π' := hCeq ▸ hπ'
    obtain ⟨e,hcomm,_huniq⟩ := exists_unique_stage_blowup_comparison χ hπ'' hπ
    have hNext := IsTowerIso.step hTail hπ' hπ e hcomm hCeq
    exact ⟨e,hNext,hiso.append hNext⟩

/-- TWO actual FIRST blowups and their actual literal-Delta tails internally
supply a unique actual full recipe comparison, without endpoint certificates. -/
theorem exists_unique_actual_two_phase_recipe_comparison (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    {π' : Y' → X} {π : Y → X}
    (hπ' : IsBlowupAlong n (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π')
    (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) π)
    {Z' Z : CMfd.{u} n} (S' : BlowupTower Y' Z') (S : BlowupTower Y Z)
    (hS' : actualAmbientDifferenceSteps W E (.step .refl _ π' hπ') S')
    (hS : actualAmbientDifferenceSteps W E (.step .refl _ π hπ) S)
    (hLen : S'.length=S.length) :
    ∃! e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        ((BlowupTower.step .refl _ π' hπ').append S') ((BlowupTower.step .refl _ π hπ).append S) e := by
  have hBase : IsGeoTestTower (originalMemberProductMarked W E 1) (.refl : BlowupTower X X) := trivial
  obtain ⟨χ,hFirst,_hcomm,_huniq⟩ := exists_original_curve_first_defect_stage_comparison hn hW hE hdense hr
    (IsTowerIso.refl (Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)) hBase hπ' hπ
  have hP : IsGeoTestTower (originalMemberProductMarked W E 1) (BlowupTower.step .refl _ π hπ) :=
    ⟨hBase,(original_curve_whole_defect_admissible hn hW hE hdense hr .refl hBase).1⟩
  obtain ⟨e,_hTail,hFull⟩ := exists_actual_difference_recipe_comparison hn hW hE hdense hr hFirst hP S' S hS' hS hLen
  exact ⟨e,hFull,fun e' he' => actual_tower_comparison_unique he' hFull⟩

end
end Hironaka.HironakaSharpActualCurveFiniteRecipeComparison
