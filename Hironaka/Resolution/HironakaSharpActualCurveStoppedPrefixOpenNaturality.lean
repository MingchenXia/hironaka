/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveExactTerminalRepadding

/-! Actual whole-history open restriction identifies the SAME stopped
terminal points before global stage/terminal atlas compatibility. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStoppedPrefixOpenNaturality
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail BlowupTowerSplitIso
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixRestriction
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveComparisonRestriction
  HironakaSharpActualCurveStoppedStageTerminalRanges HironakaSharpActualCurveFiniteRecipeComparison
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem stoppedPrefix_open_terminal_square (T : BlowupTower X Y) (U : Opens X)
    (k : ℕ) (hk : T.length≤k)
    (e : (uniformPrefix (restrict U T) k).1
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U))
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (uniformPrefix (restrict U T) k).2 (restrict U (uniformPrefix T k).2) e)
    (z : (uniformPrefix (restrict U T) k).1) :
    stoppedPrefixBiholomorphism T k hk (e z).val=
      (stoppedPrefixBiholomorphism (restrict U T) k (by rw [length_restrict];exact hk) z).val := by
  let r := k-T.length
  have hStop := stoppedPrefixBiholomorphism_stagewise T k hk
  have hRaw := HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction hStop U
  have hRestricted := BlowupTowerSplitIso.IsTowerIso.congr_base hRaw
    (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) (fun _ => rfl)
  have hPad := (isTowerIso_restrict_append U T (identityEmptyTail Y r)).trans
    ((IsTowerIso.refl_self (restrict U T)).append
      (identityEmptyTail_open_restriction Y (openPreimage T U) r))
  have hComp := he.trans (hRestricted.trans hPad)
  have hComp' := BlowupTowerSplitIso.IsTowerIso.congr_base hComp
    (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) (fun _ => rfl)
  have hLocal := stoppedPrefixBiholomorphism_stagewise (restrict U T) k
    (by rw [length_restrict];exact hk)
  have hCount : k-(restrict U T).length=r := congrArg (k-·) (length_restrict U T)
  have hLocal' := (congrArg (fun j =>
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (uniformPrefix (restrict U T) k).2
      ((restrict U T).append (identityEmptyTail (CMfd.of (n := n) (openPreimage T U)) j))
      (stoppedPrefixBiholomorphism (restrict U T) k (by rw [length_restrict];exact hk))) hCount).mp hLocal
  have hEq := actual_tower_comparison_unique hComp' hLocal' 
  have hPoint := congrArg (fun d => (d z).val) hEq
  exact hPoint

/-- The real flattening and its whole terminal square are internally constructed. -/
theorem exists_unique_stoppedPrefix_open_restriction (T : BlowupTower X Y) (U : Opens X)
    (k : ℕ) (hk : T.length≤k) :
    ∃! e : (uniformPrefix (restrict U T) k).1
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (uniformPrefix (restrict U T) k).2 (restrict U (uniformPrefix T k).2) e ∧
      ∀ z,stoppedPrefixBiholomorphism T k hk (e z).val=
        (stoppedPrefixBiholomorphism (restrict U T) k (by rw [length_restrict];exact hk) z).val := by
  obtain ⟨e,he,hUnique⟩ := exists_unique_uniformPrefix_open_restriction T U k
  exact ⟨e,⟨he,stoppedPrefix_open_terminal_square T U k hk e he⟩,
    fun e' he' => hUnique e' he'.1⟩

end
end Hironaka.HironakaSharpActualCurveStoppedPrefixOpenNaturality
