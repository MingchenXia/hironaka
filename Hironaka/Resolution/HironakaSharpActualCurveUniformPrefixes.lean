/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveBiholomorphicRecipes
import Hironaka.Blowup.BlowupTowerSplitIso

/-! Uniform actual finite stages, preserving literal empty blowup positions.
Whole dependent endpoint/tower equality removes any auxiliary padding cut. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveUniformPrefixes
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerSplit BlowupTowerSplitIso
  BlowupTowerIsomorphism HironakaSharpActualCurveEmptyPadding
  HironakaSharpActualCurveFiniteRecipeComparison HironakaSharpActualCurveBiholomorphicRecipes
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualChronologicalDistinctDefect NormalCrossings
variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}

/-- The WHOLE endpoint/head tower pair, so dependent stages are retained. -/
def headPacket (T : BlowupTower X Y) (j : ℕ) : Σ V : CMfd.{u} n,BlowupTower X V :=
  ⟨(split T j).1,head T j⟩

private theorem headPacket_append_empty (T : BlowupTower X Y) (r j : ℕ) :
    headPacket (T.append (identityEmptyTail Y r)) (j+r)=headPacket T j := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih

/-- Actual first k stages, with real empty identity successors if necessary. -/
def uniformPrefix (T : BlowupTower X Y) (k : ℕ) : Σ V : CMfd.{u} n,BlowupTower X V :=
  headPacket (T.append (identityEmptyTail Y k)) T.length

theorem uniformPrefix_length (T : BlowupTower X Y) (k : ℕ) :
    (uniformPrefix T k).2.length=k := by
  change (head (T.append (identityEmptyTail Y k)) T.length).length=k
  rw [length_head,BlowupTower.length_append,identityEmptyTail_length]
  omega

/-- Appending actual empty steps does not change ANY uniform stage pair. -/
theorem uniformPrefix_append_empty (T : BlowupTower X Y) (r k : ℕ) :
    uniformPrefix (T.append (identityEmptyTail Y r)) k=uniformPrefix T k := by
  have hSwap : (T.append (identityEmptyTail Y r)).append (identityEmptyTail Y k)=
      (T.append (identityEmptyTail Y k)).append (identityEmptyTail Y r) := by
    rw [BlowupTower.append_assoc,BlowupTower.append_assoc,
      ←identityEmptyTail_append,←identityEmptyTail_append,Nat.add_comm r k]
  change headPacket ((T.append (identityEmptyTail Y r)).append (identityEmptyTail Y k))
    (T.append (identityEmptyTail Y r)).length=uniformPrefix T k
  rw [hSwap,BlowupTower.length_append,identityEmptyTail_length,headPacket_append_empty]
  rfl

/-- Actual full-stage isomorphisms give genuine comparisons of all k stages. -/
theorem uniformPrefix_comparison
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ T' T e) (k : ℕ) :
    ∃ ψ : (uniformPrefix T' k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T k).1,
      IsTowerIso Φ (uniformPrefix T' k).2 (uniformPrefix T k).2 ψ := by
  have hFull := h.append (identityEmptyTail_isTowerIso e k)
  obtain ⟨ψ,hHead,_hTail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hFull T.length
  have hLen := h.length_eq
  let P : (Σ V : CMfd.{u} n,BlowupTower X' V) → Prop := fun A =>
    ∃ ψ : A.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T k).1,
      IsTowerIso Φ A.2 (uniformPrefix T k).2 ψ
  have hPacket : headPacket (T'.append (identityEmptyTail Y' k)) T.length=uniformPrefix T' k :=
    congrArg (headPacket (T'.append (identityEmptyTail Y' k))) hLen.symm
  have hh : P (headPacket (T'.append (identityEmptyTail Y' k)) T.length) := ⟨ψ,hHead⟩
  exact (congrArg P hPacket).mp hh

/-- Prefix types are independent of both real padding lengths and cut choices. -/
theorem exists_unique_uniformPrefix_of_padded_comparison
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (T' : BlowupTower X' Y') (T : BlowupTower X Y) (r' r k : ℕ)
    {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ (T'.append (identityEmptyTail Y' r'))
      (T.append (identityEmptyTail Y r)) e) :
    ∃! ψ : (uniformPrefix T' k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T k).1,
      IsTowerIso Φ (uniformPrefix T' k).2 (uniformPrefix T k).2 ψ := by
  have hh := uniformPrefix_comparison h k
  rw [uniformPrefix_append_empty,uniformPrefix_append_empty] at hh
  obtain ⟨ψ,hψ⟩ := hh
  exact ⟨ψ,hψ,fun ψ' hψ' => actual_tower_comparison_unique hψ' hψ⟩

theorem uniformPrefix_comparison_cocycle
    {X1 X2 X3 Y1 Y2 Y3 : CMfd.{u} n}
    {Φ12 : X1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X2}
    {Φ23 : X2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X3}
    (T1 : BlowupTower X1 Y1) (T2 : BlowupTower X2 Y2) (T3 : BlowupTower X3 Y3) (k : ℕ)
    {e12 : (uniformPrefix T1 k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T2 k).1}
    {e23 : (uniformPrefix T2 k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T3 k).1}
    {e13 : (uniformPrefix T1 k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (uniformPrefix T3 k).1}
    (h12 : IsTowerIso Φ12 (uniformPrefix T1 k).2 (uniformPrefix T2 k).2 e12)
    (h23 : IsTowerIso Φ23 (uniformPrefix T2 k).2 (uniformPrefix T3 k).2 e23)
    (h13 : IsTowerIso (Φ12.trans Φ23) (uniformPrefix T1 k).2 (uniformPrefix T3 k).2 e13) :
    e12.trans e23=e13 :=
  actual_tower_comparison_unique (h12.trans h23) h13

/-- Original two-phase geometry supplies the real padded comparison internally. -/
theorem exists_unique_original_uniformPrefix_comparison (hn : 0<n)
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
    (k : ℕ) :
    ∃! ψ : (uniformPrefix ((BlowupTower.step .refl _ π' hπ').append S') k).1
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        (uniformPrefix ((BlowupTower.step .refl _ π hπ).append S) k).1,
      IsTowerIso Φ (uniformPrefix ((BlowupTower.step .refl _ π' hπ').append S') k).2
        (uniformPrefix ((BlowupTower.step .refl _ π hπ).append S) k).2 ψ := by
  let L := S'.length+S.length
  obtain ⟨e,hFull,_hUnique⟩ := exists_unique_biholo_two_phase_recipe_comparison hn Φ hW hE hdense hr
    hπ' hπ S' S hS' hS hD' hD L (by dsimp [L];omega) (by dsimp [L];omega)
  rw [←BlowupTower.append_assoc,←BlowupTower.append_assoc] at hFull
  exact exists_unique_uniformPrefix_of_padded_comparison
    ((BlowupTower.step .refl _ π' hπ').append S') ((BlowupTower.step .refl _ π hπ).append S)
    (L-S'.length) (L-S.length) k hFull

end
end Hironaka.HironakaSharpActualCurveUniformPrefixes
