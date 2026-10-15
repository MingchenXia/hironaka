/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveOverlapMaps

/-! Actual common-open recipe comparisons satisfy a cocycle at arbitrary
real padding cuts; pairwise-map restriction compatibility is separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveCommonOpenCocycle
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveTerminalPaddingComparison
  HironakaSharpActualCurveFiniteRecipeComparison HironakaSharpActualCurveEmptyPadding
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualChronologicalDistinctDefect BlowupTowerTransforms BlowupTowerIsomorphism
  MaxLocusLocal NormalCrossings
variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual identity-on-points common-open base maps compose, including
all true inverse subtype laws. No base cocycle is supplied. -/
theorem commonOpenBase_trans (U V W O : Opens X) (hOU : O≤U) (hOV : O≤V) (hOW : O≤W) :
    (commonOpenBase U V O hOU hOV).trans (commonOpenBase V W O hOV hOW)=
      commonOpenBase U W O hOU hOW := by
  apply Diffeomorph.ext
  intro z
  rfl

/-- The actual full history padded by genuine identity empty-centre blowups. -/
def paddedHistory {Y Z : CMfd.{u} n} (P : BlowupTower X Y) (S : BlowupTower Y Z) (L : ℕ) :
    BlowupTower X Z :=
  P.append (S.append (identityEmptyTail Z (L-S.length)))

/-- Actual stagewise comparisons at three possibly different common cuts
have the SAME real cocycle after extending to one genuine common size. -/
theorem terminal_padding_comparison_cocycle
    {X1 X2 X3 Y1 Y2 Y3 Z1 Z2 Z3 : CMfd.{u} n}
    {Φ12 : X1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X2}
    {Φ23 : X2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X3}
    {P1 : BlowupTower X1 Y1} {P2 : BlowupTower X2 Y2} {P3 : BlowupTower X3 Y3}
    {S1 : BlowupTower Y1 Z1} {S2 : BlowupTower Y2 Z2} {S3 : BlowupTower Y3 Z3}
    {e12 : Z1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z2}
    {e23 : Z2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z3}
    {e13 : Z1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z3}
    (L12 L23 L13 : ℕ) (h12₁ : S1.length≤L12) (h12₂ : S2.length≤L12)
    (h23₂ : S2.length≤L23) (h23₃ : S3.length≤L23)
    (h13₁ : S1.length≤L13) (h13₃ : S3.length≤L13)
    (h12 : IsTowerIso Φ12 (paddedHistory P1 S1 L12) (paddedHistory P2 S2 L12) e12)
    (h23 : IsTowerIso Φ23 (paddedHistory P2 S2 L23) (paddedHistory P3 S3 L23) e23)
    (h13 : IsTowerIso (Φ12.trans Φ23) (paddedHistory P1 S1 L13) (paddedHistory P3 S3 L13) e13) :
    e12.trans e23=e13 := by
  let N := L12+L23+L13
  have hh12 := terminal_padding_comparison_extend (P' := P1) (P := P2) (S' := S1) (S := S2)
    L12 (L23+L13) h12₁ h12₂ h12
  have hh23 := terminal_padding_comparison_extend (P' := P2) (P := P3) (S' := S2) (S := S3)
    L23 (L12+L13) h23₂ h23₃ h23
  have hh13 := terminal_padding_comparison_extend (P' := P1) (P := P3) (S' := S1) (S := S3)
    L13 (L12+L23) h13₁ h13₃ h13
  have hN12 : L12+(L23+L13)=N := by omega
  have hN23 : L23+(L12+L13)=N := by omega
  have hN13 : L13+(L12+L23)=N := by omega
  rw [hN12] at hh12
  rw [hN23] at hh23
  rw [hN13] at hh13
  exact actual_tower_comparison_unique (hh12.trans hh23) hh13

/-- ONLY original geometry and THREE actual retained local recipes construct
all common-open comparisons BEFORE the real arbitrary-cut cocycle. -/
theorem exists_actual_common_open_recipe_cocycle (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (U1 U2 U3 O : Opens X)
    (hO1 : O≤U1) (hO2 : O≤U2) (hO3 : O≤U3)
    {Y1 Y2 Y3 Z1 Z2 Z3 : CMfd.{u} n}
    {π1 : Y1 → CMfd.of (n := n) U1} {π2 : Y2 → CMfd.of (n := n) U2} {π3 : Y3 → CMfd.of (n := n) U3}
    (hπ1 : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : U1 → X) ⁻¹' W)
      (E.map ((Subtype.val : U1 → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) U1) (CMfd.of (n := n) U1))) π1)
    (hπ2 : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : U2 → X) ⁻¹' W)
      (E.map ((Subtype.val : U2 → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) U2) (CMfd.of (n := n) U2))) π2)
    (hπ3 : IsBlowupAlong n (chronologicalDistinctDefect ((Subtype.val : U3 → X) ⁻¹' W)
      (E.map ((Subtype.val : U3 → X) ⁻¹' ·)) (.refl : BlowupTower (CMfd.of (n := n) U3) (CMfd.of (n := n) U3))) π3)
    (S1 : BlowupTower Y1 Z1) (S2 : BlowupTower Y2 Z2) (S3 : BlowupTower Y3 Z3)
    (hS1 : actualAmbientDifferenceSteps ((Subtype.val : U1 → X) ⁻¹' W)
      (E.map ((Subtype.val : U1 → X) ⁻¹' ·)) (.step .refl _ π1 hπ1) S1)
    (hS2 : actualAmbientDifferenceSteps ((Subtype.val : U2 → X) ⁻¹' W)
      (E.map ((Subtype.val : U2 → X) ⁻¹' ·)) (.step .refl _ π2 hπ2) S2)
    (hS3 : actualAmbientDifferenceSteps ((Subtype.val : U3 → X) ⁻¹' W)
      (E.map ((Subtype.val : U3 → X) ⁻¹' ·)) (.step .refl _ π3 hπ3) S3)
    (hD1 : actualAmbientExceptionalDifference ((Subtype.val : U1 → X) ⁻¹' W)
      (E.map ((Subtype.val : U1 → X) ⁻¹' ·)) ((BlowupTower.step .refl _ π1 hπ1).append S1)=∅)
    (hD2 : actualAmbientExceptionalDifference ((Subtype.val : U2 → X) ⁻¹' W)
      (E.map ((Subtype.val : U2 → X) ⁻¹' ·)) ((BlowupTower.step .refl _ π2 hπ2).append S2)=∅)
    (hD3 : actualAmbientExceptionalDifference ((Subtype.val : U3 → X) ⁻¹' W)
      (E.map ((Subtype.val : U3 → X) ⁻¹' ·)) ((BlowupTower.step .refl _ π3 hπ3).append S3)=∅)
    (L12 L23 L13 : ℕ) (h12₁ : S1.length≤L12) (h12₂ : S2.length≤L12)
    (h23₂ : S2.length≤L23) (h23₃ : S3.length≤L23)
    (h13₁ : S1.length≤L13) (h13₃ : S3.length≤L13) :
    let A1 := nestedOpens U1 O
    let A2 := nestedOpens U2 O
    let A3 := nestedOpens U3 O
    let P1 := BlowupTower.step .refl _ π1 hπ1
    let P2 := BlowupTower.step .refl _ π2 hπ2
    let P3 := BlowupTower.step .refl _ π3 hπ3
    let R1 := restrict A1 P1
    let R2 := restrict A2 P2
    let R3 := restrict A3 P3
    let T1 := restrict (openPreimage P1 A1) S1
    let T2 := restrict (openPreimage P2 A2) S2
    let T3 := restrict (openPreimage P3 A3) S3
    ∃ e12 : CMfd.of (n := n) (openPreimage S1 (openPreimage P1 A1)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage S2 (openPreimage P2 A2)),
    ∃ e23 : CMfd.of (n := n) (openPreimage S2 (openPreimage P2 A2)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage S3 (openPreimage P3 A3)),
    ∃ e13 : CMfd.of (n := n) (openPreimage S1 (openPreimage P1 A1)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage S3 (openPreimage P3 A3)),
      IsTowerIso (commonOpenBase U1 U2 O hO1 hO2)
        (paddedHistory R1 T1 L12) (paddedHistory R2 T2 L12) e12 ∧
      IsTowerIso (commonOpenBase U2 U3 O hO2 hO3)
        (paddedHistory R2 T2 L23) (paddedHistory R3 T3 L23) e23 ∧
      IsTowerIso (commonOpenBase U1 U3 O hO1 hO3)
        (paddedHistory R1 T1 L13) (paddedHistory R3 T3 L13) e13 ∧
      e12.trans e23=e13 := by
  let A1 := nestedOpens U1 O
  let A2 := nestedOpens U2 O
  let A3 := nestedOpens U3 O
  let P1 := BlowupTower.step .refl _ π1 hπ1
  let P2 := BlowupTower.step .refl _ π2 hπ2
  let P3 := BlowupTower.step .refl _ π3 hπ3
  obtain ⟨e12,h12,_hUnique12⟩ := exists_unique_actual_common_open_recipe_comparison
    hn hW hE hdense hr U1 U2 O hO1 hO2 hπ1 hπ2 S1 S2 hS1 hS2 hD1 hD2
    L12 h12₁ h12₂
  obtain ⟨e23,h23,_hUnique23⟩ := exists_unique_actual_common_open_recipe_comparison
    hn hW hE hdense hr U2 U3 O hO2 hO3 hπ2 hπ3 S2 S3 hS2 hS3 hD2 hD3
    L23 h23₂ h23₃
  obtain ⟨e13,h13,_hUnique13⟩ := exists_unique_actual_common_open_recipe_comparison
    hn hW hE hdense hr U1 U3 O hO1 hO3 hπ1 hπ3 S1 S3 hS1 hS3 hD1 hD3
    L13 h13₁ h13₃
  have h12' : IsTowerIso (commonOpenBase U1 U2 O hO1 hO2)
      (paddedHistory (restrict A1 P1) (restrict (openPreimage P1 A1) S1) L12)
      (paddedHistory (restrict A2 P2) (restrict (openPreimage P2 A2) S2) L12) e12 := by
    simpa only [paddedHistory,length_restrict] using h12
  have h23' : IsTowerIso (commonOpenBase U2 U3 O hO2 hO3)
      (paddedHistory (restrict A2 P2) (restrict (openPreimage P2 A2) S2) L23)
      (paddedHistory (restrict A3 P3) (restrict (openPreimage P3 A3) S3) L23) e23 := by
    simpa only [paddedHistory,length_restrict] using h23
  have h13' : IsTowerIso (commonOpenBase U1 U3 O hO1 hO3)
      (paddedHistory (restrict A1 P1) (restrict (openPreimage P1 A1) S1) L13)
      (paddedHistory (restrict A3 P3) (restrict (openPreimage P3 A3) S3) L13) e13 := by
    simpa only [paddedHistory,length_restrict] using h13
  have h13'' : IsTowerIso
      ((commonOpenBase U1 U2 O hO1 hO2).trans (commonOpenBase U2 U3 O hO2 hO3))
      (paddedHistory (restrict A1 P1) (restrict (openPreimage P1 A1) S1) L13)
      (paddedHistory (restrict A3 P3) (restrict (openPreimage P3 A3) S3) L13) e13 := by
    rw [commonOpenBase_trans]
    exact h13'
  refine ⟨e12,e23,e13,h12',h23',h13',?_⟩
  exact terminal_padding_comparison_cocycle
    (P1 := restrict A1 P1) (P2 := restrict A2 P2) (P3 := restrict A3 P3)
    (S1 := restrict (openPreimage P1 A1) S1) (S2 := restrict (openPreimage P2 A2) S2)
    (S3 := restrict (openPreimage P3 A3) S3) L12 L23 L13
    (by simpa only [length_restrict] using h12₁) (by simpa only [length_restrict] using h12₂)
    (by simpa only [length_restrict] using h23₂) (by simpa only [length_restrict] using h23₃)
    (by simpa only [length_restrict] using h13₁) (by simpa only [length_restrict] using h13₃)
    h12' h23' h13''

end
end Hironaka.HironakaSharpActualCurveCommonOpenCocycle
