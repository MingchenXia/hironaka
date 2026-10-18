/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveUniformSuccessorComparison

/-! Actual restricted successor blowups, exact original arrow readout and
compatibility under the derived genuine stage-atlas comparison maps. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveUniformSuccessorRestriction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupRestrictOpen MaxLocusLocal
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformSuccessorComparison
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveOverlapMaps
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

structure RestrictedUniformSuccessorData (T : BlowupTower X Y) (k : ℕ) (U : Opens X) where
  centre : Set (openPreimage (uniformPrefix T k).2 U)
  map : CMfd.of (n := n) (openPreimage (uniformPrefix T (k+1)).2 U) →
    CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U)
  blowup : IsBlowupAlong n centre map
  step_eq : restrict U (uniformPrefix T (k+1)).2=
    BlowupTower.step (restrict U (uniformPrefix T k).2) centre map blowup
  map_val : ∀ p,(map p).val=(actualUniformSuccessor T k).map p.val
  centre_eq : centre=(Subtype.val : openPreimage (uniformPrefix T k).2 U → (uniformPrefix T k).1)
    ⁻¹' (actualUniformSuccessor T k).centre

/-- True original blowup restriction is transported as an ENTIRE dependent proposition. -/
def actualRestrictedUniformSuccessor (T : BlowupTower X Y) (k : ℕ) (U : Opens X) :
    RestrictedUniformSuccessorData T k U := by
  apply Classical.choice
  let A := actualUniformSuccessor T k
  let P : BlowupTower X (uniformPrefix T (k+1)).1 → Prop := fun S =>
    ∃ (C : Set (openPreimage (uniformPrefix T k).2 U))
      (ρ : CMfd.of (n := n) (openPreimage S U) →
        CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U))
      (hρ : IsBlowupAlong n C ρ),
      restrict U S=BlowupTower.step (restrict U (uniformPrefix T k).2) C ρ hρ ∧
      (∀ p,(ρ p).val=A.map p.val) ∧
      C=(Subtype.val : openPreimage (uniformPrefix T k).2 U → (uniformPrefix T k).1) ⁻¹' A.centre
  have hLiteral : P (BlowupTower.step (uniformPrefix T k).2 A.centre A.map A.blowup) := by
    let V := openPreimage (uniformPrefix T k).2 U
    let ρ : CMfd.of (n := n) (openPreimage
        (BlowupTower.step (uniformPrefix T k).2 A.centre A.map A.blowup) U) → CMfd.of (n := n) V :=
      fun p => ⟨A.map p.val,p.property⟩
    have hρ : IsBlowupAlong n ((Subtype.val : V → (uniformPrefix T k).1) ⁻¹' A.centre) ρ :=
      isBlowupAlong_restrict A.blowup V (V.isOpen.preimage A.blowup.contMDiff.continuous)
    exact ⟨_,ρ,hρ,rfl,fun _ => rfl,rfl⟩
  have hOriginal : P (uniformPrefix T (k+1)).2 := (congrArg P A.step_eq).mpr hLiteral
  obtain ⟨C,ρ,hρ,hStep,hVal,hCentre⟩ := hOriginal
  exact ⟨{ centre := C,map := ρ,blowup := hρ,step_eq := hStep,map_val := hVal,centre_eq := hCentre }⟩

theorem actualRestrictedUniformSuccessor_compatible
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} (k : ℕ) (U' : Opens X') (U : Opens X)
    {Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U}
    {e₀ : CMfd.of (n := n) (openPreimage (uniformPrefix T' k).2 U')
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U)}
    {e₁ : CMfd.of (n := n) (openPreimage (uniformPrefix T' (k+1)).2 U')
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (uniformPrefix T (k+1)).2 U)}
    (h₀ : IsTowerIso Φ (restrict U' (uniformPrefix T' k).2) (restrict U (uniformPrefix T k).2) e₀)
    (h₁ : IsTowerIso Φ (restrict U' (uniformPrefix T' (k+1)).2)
      (restrict U (uniformPrefix T (k+1)).2) e₁) :
    (∀ z,(actualRestrictedUniformSuccessor T k U).map (e₁ z)=
      e₀ ((actualRestrictedUniformSuccessor T' k U').map z)) ∧
      e₀ ⁻¹' (actualRestrictedUniformSuccessor T k U).centre=
        (actualRestrictedUniformSuccessor T' k U').centre := by
  have hNext := h₁
  rw [(actualRestrictedUniformSuccessor T' k U').step_eq,
    (actualRestrictedUniformSuccessor T k U).step_eq] at hNext
  obtain ⟨e,hPrev,hSquare,hCentre⟩ := hNext.step_inv
  have hEq : e=e₀ := actual_tower_comparison_unique hPrev h₀
  exact ⟨by simpa only [hEq] using hSquare,by simpa only [hEq] using hCentre⟩

private theorem actual_uniformStage_stagewise {J : Type u} (A : ActualEndpointHistories X J)
    (k : ℕ) (i j : J) :
    IsTowerIso (commonOpenBase (A.openSet i) (A.openSet j) (A.openSet i⊓A.openSet j) inf_le_left inf_le_right)
      (restrict (nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j))
        (uniformPrefix ((A.prefixTower i).append (A.tail i)) k).2)
      (restrict (nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j))
        (uniformPrefix ((A.prefixTower j).append (A.tail j)) k).2)
      ((uniformStageHistories A k).comparison i j) :=
  (uniformStageHistories A k).stagewise i j

theorem uniformStage_successor_compatible {J : Type u} (A : ActualEndpointHistories X J)
    (k : ℕ) (i j : J) :
    let Ti := (A.prefixTower i).append (A.tail i)
    let Tj := (A.prefixTower j).append (A.tail j)
    let Ui := nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j)
    let Uj := nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j)
    let Ri := actualRestrictedUniformSuccessor Ti k Ui
    let Rj := actualRestrictedUniformSuccessor Tj k Uj
    let e₀ := (uniformStageHistories A k).comparison i j
    let e₁ := (uniformStageHistories A (k+1)).comparison i j
    (∀ z,Rj.map (e₁ z)=e₀ (Ri.map z)) ∧ e₀ ⁻¹' Rj.centre=Ri.centre := by
  dsimp only
  apply actualRestrictedUniformSuccessor_compatible
    (T' := (A.prefixTower i).append (A.tail i))
    (T := (A.prefixTower j).append (A.tail j)) k
    (nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j))
    (nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j))
    (Φ := commonOpenBase (A.openSet i) (A.openSet j) (A.openSet i⊓A.openSet j) inf_le_left inf_le_right)
    (e₀ := (uniformStageHistories A k).comparison i j)
    (e₁ := (uniformStageHistories A (k+1)).comparison i j)
  · exact actual_uniformStage_stagewise A k i j
  · exact actual_uniformStage_stagewise A (k+1) i j

end
end Hironaka.HironakaSharpActualCurveUniformSuccessorRestriction
