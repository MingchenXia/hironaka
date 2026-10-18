/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveTerminalPaddingComparison
import Hironaka.Resolution.HironakaSharpActualCurveStoppedStageTerminalRanges

/-! The SAME already chosen terminal comparison survives every genuine
common cut. Only equal auxiliary identity suffixes are canceled; original
history positions and all original empty steps are untouched. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveExactTerminalRepadding
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism BlowupTowerSplitIso
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveTerminalPaddingComparison
  HironakaSharpActualCurveStoppedStageTerminalRanges HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveUniformPrefixes
variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}

/-- Comparison statement only: all original positions of T' and T remain intact. -/
theorem isTowerIso_of_equal_identity_padding
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y} :
    ∀ r : ℕ,IsTowerIso Φ (T'.append (identityEmptyTail Y' r))
      (T.append (identityEmptyTail Y r)) e → IsTowerIso Φ T' T e
  | 0,h => h
  | r+1,h => by
    obtain ⟨a,hPrev,hSquare,_hCentre⟩ := h.step_inv
    have hSame : IsTowerIso Φ (T'.append (identityEmptyTail Y' r))
        (T.append (identityEmptyTail Y r)) e :=
      BlowupTowerSplitIso.IsTowerIso.congr_last hPrev (fun z => hSquare z)
    exact isTowerIso_of_equal_identity_padding r hSame

/-- Reuse e itself at ANY true common cut, not only a common larger extension. -/
theorem terminal_comparison_at_any_cut
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    {S' : BlowupTower Y' Z'} {S : BlowupTower Y Z}
    {e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (L K : ℕ) (hL' : S'.length≤L) (hL : S.length≤L)
    (hK' : S'.length≤K) (hK : S.length≤K)
    (h : IsTowerIso Φ (P'.append (S'.append (identityEmptyTail Z' (L-S'.length))))
      (P.append (S.append (identityEmptyTail Z (L-S.length)))) e) :
    IsTowerIso Φ (P'.append (S'.append (identityEmptyTail Z' (K-S'.length))))
      (P.append (S.append (identityEmptyTail Z (K-S.length)))) e := by
  have hLarge := terminal_padding_comparison_extend L K hL' hL h
  have hsub' : (L+K)-S'.length=(K-S'.length)+L := by omega
  have hsub : (L+K)-S.length=(K-S.length)+L := by omega
  have hLast : IsTowerIso Φ
      ((P'.append (S'.append (identityEmptyTail Z' (K-S'.length)))).append (identityEmptyTail Z' L))
      ((P.append (S.append (identityEmptyTail Z (K-S.length)))).append (identityEmptyTail Z L)) e := by
    simpa only [BlowupTower.append_assoc,←identityEmptyTail_append,←hsub',←hsub] using hLarge
  exact isTowerIso_of_equal_identity_padding L hLast

/-- The actual terminal map determines the genuine stopped-prefix comparison. -/
theorem stopped_comparison_of_padded
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (r' r k : ℕ) {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ (T'.append (identityEmptyTail Y' r')) (T.append (identityEmptyTail Y r)) e)
    (hk' : T'.length≤k) (hk : T.length≤k) :
    IsTowerIso Φ (uniformPrefix T' k).2 (uniformPrefix T k).2
      ((stoppedPrefixBiholomorphism T' k hk').trans (e.trans (stoppedPrefixBiholomorphism T k hk).symm)) := by
  let L := T'.length+r'
  have hLen := h.length_eq
  rw [BlowupTower.length_append,BlowupTower.length_append,
    identityEmptyTail_length,identityEmptyTail_length] at hLen
  have hsub' : L-T'.length=r' := by dsimp [L];omega
  have hsub : L-T.length=r := by dsimp [L];omega
  have hOrig : IsTowerIso Φ
      ((BlowupTower.refl : BlowupTower X' X').append (T'.append (identityEmptyTail Y' (L-T'.length))))
      ((BlowupTower.refl : BlowupTower X X).append (T.append (identityEmptyTail Y (L-T.length)))) e := by
    simpa only [BlowupTower.refl_append,hsub',hsub] using h
  have hAtK := terminal_comparison_at_any_cut L k (by dsimp [L];omega) (by dsimp [L];omega) hk' hk hOrig
  rw [BlowupTower.refl_append,BlowupTower.refl_append] at hAtK
  have hNew := (stoppedPrefixBiholomorphism_stagewise T' k hk').trans
    (hAtK.trans (stoppedPrefixBiholomorphism_stagewise T k hk).symm)
  exact BlowupTowerSplitIso.IsTowerIso.congr_base hNew (fun _ => rfl)

/-- Real full-history uniqueness preserves ANY already chosen actual stage map. -/
theorem stopped_chosen_comparison_terminal_square
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (r' r k : ℕ) {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ (T'.append (identityEmptyTail Y' r')) (T.append (identityEmptyTail Y r)) e)
    (hk' : T'.length≤k) (hk : T.length≤k)
    (ψ : (uniformPrefix T' k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T k).1)
    (hψ : IsTowerIso Φ (uniformPrefix T' k).2 (uniformPrefix T k).2 ψ)
    (z : (uniformPrefix T' k).1) :
    stoppedPrefixBiholomorphism T k hk (ψ z)=e (stoppedPrefixBiholomorphism T' k hk' z) := by
  have hEq := actual_tower_comparison_unique hψ (stopped_comparison_of_padded T' T r' r k h hk' hk)
  rw [hEq]
  exact Diffeomorph.apply_symm_apply _ _

end
end Hironaka.HironakaSharpActualCurveExactTerminalRepadding
