/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.TowerIsoBaseCongrExact
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction

/-! Genuine padded-history restriction precedes equality with direct
comparisons. Empty trace centres and genuine padding positions are retained. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurvePaddedComparisonRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveComparisonRestriction HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveTerminalPaddingComparison
variable {n : ℕ} {X Y Z X' Y' Z' : CMfd.{u} n}


/-- Actual append restrictions and genuine empty-tail restriction supply the
WHOLE padded-history flattening, identity on underlying terminal points. -/
theorem exists_padded_history_open_flattening
    (P : BlowupTower X Y) (S : BlowupTower Y Z) (L : ℕ) (U : Opens X) :
    ∃ e : CMfd.of (n := n) (openPreimage (paddedHistory P S L) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S (openPreimage P U)),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (paddedHistory P S L))
        (paddedHistory (restrict U P) (restrict (openPreimage P U) S) L) e ∧
      ∀ z,(e z : Z)=z.val := by
  let A := openPreimage P U
  let V := openPreimage S A
  let r := L-S.length
  let a := opensCongr (n := n) (openPreimage_append P (S.append (identityEmptyTail Z r)) U).symm
  let b := (opensCongr (n := n) (openPreimage_append S (identityEmptyTail Z r) A).symm).trans
    (identityEmptyRestriction Z V r)
  let e := a.trans b
  have hTail := (isTowerIso_restrict_append A S (identityEmptyTail Z r)).trans
    ((IsTowerIso.refl_self (restrict A S)).append (identityEmptyTail_open_restriction Z V r))
  have hTail' := BlowupTowerSplitIso.IsTowerIso.congr_base hTail
    (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) A) ∞) (fun _ => rfl)
  have hWhole := (isTowerIso_restrict_append U P (S.append (identityEmptyTail Z r))).trans
    ((IsTowerIso.refl_self (restrict U P)).append hTail')
  refine ⟨e,?_,fun _ => rfl⟩
  have h := BlowupTowerSplitIso.IsTowerIso.congr_base hWhole
    (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) (fun _ => rfl)
  have h' := BlowupTowerSplitIso.IsTowerIso.congr_last h (χ' := e)
    (fun _ => Subtype.ext rfl)
  dsimp only [paddedHistory]
  rw [length_restrict]
  exact h'


/-- Real full restriction and both independently constructed flattenings give
an actual comparison of the EXACT padded restricted histories. -/
theorem exists_padded_comparison_open_restriction
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    {S' : BlowupTower Y' Z'} {S : BlowupTower Y Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z} (L : ℕ)
    (h : IsTowerIso Φ (paddedHistory P' S' L) (paddedHistory P S L) χ) (U : Opens X) :
    ∃ e : CMfd.of (n := n) (openPreimage S' (openPreimage P' (preimageOpen Φ U)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S (openPreimage P U)),
      IsTowerIso (openRestriction Φ (preimageOpen Φ U) U rfl)
        (paddedHistory (restrict (preimageOpen Φ U) P')
          (restrict (openPreimage P' (preimageOpen Φ U)) S') L)
        (paddedHistory (restrict U P) (restrict (openPreimage P U) S) L) e ∧
      ∀ z,(e z : Z)=χ z.val := by
  obtain ⟨fs,hfs,hfsPoint⟩ := exists_padded_history_open_flattening P' S' L (preimageOpen Φ U)
  obtain ⟨ft,hft,hftPoint⟩ := exists_padded_history_open_flattening P S L U
  let er := openRestriction χ (openPreimage (paddedHistory P' S' L) (preimageOpen Φ U))
    (openPreimage (paddedHistory P S L) U) (openPreimage_eq_preimage h U)
  let e := fs.symm.trans (er.trans ft)
  have hR := HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction h U
  have hNew := (hfs.symm.trans hR).trans hft
  refine ⟨e,?_,?_⟩
  · exact BlowupTowerSplitIso.IsTowerIso.congr_base hNew (fun _ => rfl)
  · intro z
    have hInv : (fs.symm z : Z')=z.val := by
      calc
        (fs.symm z : Z')=(fs (fs.symm z) : Z') := (hfsPoint (fs.symm z)).symm
        _ = z.val := congrArg Subtype.val (fs.apply_symm_apply z)
    change (ft (er (fs.symm z)) : Z)=χ z.val
    rw [hftPoint]
    exact congrArg χ hInv

/-- EVERY actual direct comparison, even at a different true padding cut,
has the old terminal point map after genuine restriction and flattening. -/
theorem padded_comparison_open_restriction_direct
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    {S' : BlowupTower Y' Z'} {S : BlowupTower Y Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (L K : ℕ) (hL' : S'.length≤L) (hL : S.length≤L)
    (hK' : S'.length≤K) (hK : S.length≤K)
    (h : IsTowerIso Φ (paddedHistory P' S' L) (paddedHistory P S L) χ) (U : Opens X)
    (e : CMfd.of (n := n) (openPreimage S' (openPreimage P' (preimageOpen Φ U)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S (openPreimage P U)))
    (he : IsTowerIso (openRestriction Φ (preimageOpen Φ U) U rfl)
      (paddedHistory (restrict (preimageOpen Φ U) P')
        (restrict (openPreimage P' (preimageOpen Φ U)) S') K)
      (paddedHistory (restrict U P) (restrict (openPreimage P U) S) K) e) :
    ∀ z,(e z : Z)=χ z.val := by
  obtain ⟨eL,heL,hPoint⟩ := exists_padded_comparison_open_restriction L h U
  have hEq := terminal_padding_comparison_independent
    (P' := restrict (preimageOpen Φ U) P') (P := restrict U P)
    (S' := restrict (openPreimage P' (preimageOpen Φ U)) S')
    (S := restrict (openPreimage P U) S) L K
    (by simpa only [length_restrict] using hL') (by simpa only [length_restrict] using hL)
    (by simpa only [length_restrict] using hK') (by simpa only [length_restrict] using hK)
    heL he
  rw [←hEq]
  exact hPoint

end
end Hironaka.HironakaSharpActualCurvePaddedComparisonRestriction
