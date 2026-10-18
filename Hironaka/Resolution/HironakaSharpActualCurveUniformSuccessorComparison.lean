/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveUniformPrefixSuccessors

/-! Genuine successor centres and arrows under the already chosen actual
stage maps. No centre correspondence or commuting square is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveUniformSuccessorComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixSuccessors
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveFiniteRecipeComparison
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- Ordinary OUTPUT of the genuine local successor construction. -/
structure UniformSuccessorData (T : BlowupTower X Y) (k : ℕ) where
  centre : Set (uniformPrefix T k).1
  map : (uniformPrefix T (k+1)).1 → (uniformPrefix T k).1
  blowup : IsBlowupAlong n centre map
  step_eq : (uniformPrefix T (k+1)).2=BlowupTower.step (uniformPrefix T k).2 centre map blowup

/-- Actual centre, map and literal step are constructed internally. -/
def actualUniformSuccessor (T : BlowupTower X Y) (k : ℕ) : UniformSuccessorData T k := by
  apply Classical.choice
  obtain ⟨C,π,hπ,hStep,_hProj⟩ := uniformPrefix_successor T k
  exact ⟨{ centre := C,map := π,blowup := hπ,step_eq := hStep }⟩

theorem actualUniformSuccessor_projection (T : BlowupTower X Y) (k : ℕ)
    (z : (uniformPrefix T (k+1)).1) :
    (uniformPrefix T (k+1)).2.proj z=
      (uniformPrefix T k).2.proj ((actualUniformSuccessor T k).map z) := by
  rw [(actualUniformSuccessor T k).step_eq]
  rfl

/-- True next-step inversion and whole previous-history uniqueness identify
centres and arrows under THESE already chosen stage maps. -/
theorem actualUniformSuccessor_compatible
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} (k : ℕ)
    {e₀ : (uniformPrefix T' k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T k).1}
    {e₁ : (uniformPrefix T' (k+1)).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (uniformPrefix T (k+1)).1}
    (h₀ : IsTowerIso Φ (uniformPrefix T' k).2 (uniformPrefix T k).2 e₀)
    (h₁ : IsTowerIso Φ (uniformPrefix T' (k+1)).2 (uniformPrefix T (k+1)).2 e₁) :
    (∀ z,(actualUniformSuccessor T k).map (e₁ z)=e₀ ((actualUniformSuccessor T' k).map z)) ∧
      e₀ ⁻¹' (actualUniformSuccessor T k).centre=(actualUniformSuccessor T' k).centre := by
  have hNext := h₁
  rw [(actualUniformSuccessor T' k).step_eq,(actualUniformSuccessor T k).step_eq] at hNext
  obtain ⟨e,hPrev,hSquare,hCentre⟩ := hNext.step_inv
  have hEq : e=e₀ := actual_tower_comparison_unique hPrev h₀
  exact ⟨by simpa only [hEq] using hSquare,by simpa only [hEq] using hCentre⟩

/-- A genuine padded terminal comparison internally supplies both stage maps,
then the entire actual next blowup square and centre correspondence. -/
theorem exists_uniformSuccessor_comparison_of_padded
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (T' : BlowupTower X' Y') (T : BlowupTower X Y) (r' r k : ℕ)
    {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ (T'.append (identityEmptyTail Y' r'))
      (T.append (identityEmptyTail Y r)) e) :
    ∃ (e₀ : (uniformPrefix T' k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T k).1)
      (e₁ : (uniformPrefix T' (k+1)).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        (uniformPrefix T (k+1)).1),
      IsTowerIso Φ (uniformPrefix T' k).2 (uniformPrefix T k).2 e₀ ∧
      IsTowerIso Φ (uniformPrefix T' (k+1)).2 (uniformPrefix T (k+1)).2 e₁ ∧
      (∀ z,(actualUniformSuccessor T k).map (e₁ z)=e₀ ((actualUniformSuccessor T' k).map z)) ∧
      e₀ ⁻¹' (actualUniformSuccessor T k).centre=(actualUniformSuccessor T' k).centre := by
  obtain ⟨e₀,h₀,_hUnique₀⟩ := exists_unique_uniformPrefix_of_padded_comparison T' T r' r k h
  obtain ⟨e₁,h₁,_hUnique₁⟩ := exists_unique_uniformPrefix_of_padded_comparison T' T r' r (k+1) h
  exact ⟨e₀,e₁,h₀,h₁,actualUniformSuccessor_compatible k h₀ h₁⟩

end
end Hironaka.HironakaSharpActualCurveUniformSuccessorComparison
