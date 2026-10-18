/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveCommonOpenCocycle

/-! Genuine restriction of actual stage comparisons and identity-empty
padding, with no deletion of empty centres. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveComparisonRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupRestrictOpen
  HironakaSharpActualCurveEmptyPadding
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- The genuine inverse image open under the actual biholomorphism. -/
def preimageOpen (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (U : Opens X) : Opens X' :=
  ⟨Φ ⁻¹' (U : Set X),U.isOpen.preimage Φ.continuous⟩

/-- Both holomorphic directions and actual inverse laws on the real matching
opens, retaining the actual underlying ambient map. -/
def openRestriction (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (U' : Opens X') (U : Opens X) (hU : (U' : Set X')=Φ ⁻¹' (U : Set X)) :
    CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U where
  toFun x := ⟨Φ x.val,by have hx := x.property; change x.val ∈ (U' : Set X') at hx; rw [hU] at hx;exact hx⟩
  invFun y := ⟨Φ.symm y.val,by change Φ.symm y.val ∈ (U' : Set X');rw [hU];change Φ (Φ.symm y.val) ∈ U;rw [Φ.apply_symm_apply];exact y.property⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x.val)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y.val)
  contMDiff_toFun := contMDiff_opens_mk (Φ.contMDiff.comp contMDiff_subtype_val)
    (fun x => by have hx := x.property;change x.val ∈ (U' : Set X') at hx;rw [hU] at hx;exact hx)
  contMDiff_invFun := contMDiff_opens_mk (Φ.symm.contMDiff.comp contMDiff_subtype_val)
    (fun y => by change Φ.symm y.val ∈ (U' : Set X');rw [hU];change Φ (Φ.symm y.val) ∈ U;rw [Φ.apply_symm_apply];exact y.property)

@[simp] theorem openRestriction_val
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (U' : Opens X') (U : Opens X) (hU : (U' : Set X')=Φ ⁻¹' (U : Set X)) (x : U') :
    (openRestriction Φ U' U hU x : X)=Φ (x : X') := rfl


/-- The actual full projection square identifies the two genuine terminal opens. -/
theorem openPreimage_eq_preimage {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ T' T χ) (U : Opens X) :
    (openPreimage T' (preimageOpen Φ U) : Set Y')=χ ⁻¹' (openPreimage T U : Set Y) := by
  ext p
  change Φ (T'.proj p) ∈ U ↔ T.proj (χ p) ∈ U
  rw [h.proj_comm p]

/-- Genuine stagewise restriction, with the exact old terminal map on underlying points.
Every original successor and every empty trace position remains present. -/
theorem IsTowerIso.open_restriction
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso Φ T' T χ) (U : Opens X) :
    IsTowerIso (openRestriction Φ (preimageOpen Φ U) U rfl)
      (restrict (preimageOpen Φ U) T') (restrict U T)
      (openRestriction χ (openPreimage T' (preimageOpen Φ U)) (openPreimage T U)
        (openPreimage_eq_preimage h U)) := by
  induction h with
  | refl => exact IsTowerIso.refl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    refine IsTowerIso.step ih _ _ _ (fun p => Subtype.ext (hcomm p.val)) ?_
    ext p
    change χ p.val ∈ C ↔ p.val ∈ C'
    change p.val ∈ χ ⁻¹' C ↔ p.val ∈ C'
    rw [hC]


/-- The actual empty-tail projection supplies its exact terminal open. -/
theorem identityEmptyTail_openPreimage (Y : CMfd.{u} n) (U : Opens Y) (r : ℕ) :
    (openPreimage (identityEmptyTail Y r) U : Set Y)=(U : Set Y) := by
  ext y
  change (identityEmptyTail Y r).proj y ∈ U ↔ y ∈ U
  rw [identityEmptyTail_proj]
  rfl

/-- The actual endpoint flattening of a restricted empty tail is identity on points. -/
def identityEmptyRestriction (Y : CMfd.{u} n) (U : Opens Y) (r : ℕ) :
    CMfd.of (n := n) (openPreimage (identityEmptyTail Y r) U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U :=
  openRestriction (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞)
    (openPreimage (identityEmptyTail Y r) U) U (identityEmptyTail_openPreimage Y U r)

/-- Restriction of genuine identity padding retains all r actual empty blowups,
with a real stagewise isomorphism to the r actual identity blowups on U. -/
theorem identityEmptyTail_open_restriction (Y : CMfd.{u} n) (U : Opens Y) (r : ℕ) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U (identityEmptyTail Y r)) (identityEmptyTail (CMfd.of (n := n) U) r)
      (identityEmptyRestriction Y U r) := by
  induction r with
  | zero => exact IsTowerIso.refl
  | succ r ih =>
    refine IsTowerIso.step ih _ _ (identityEmptyRestriction Y U (r+1))
      (fun _ => Subtype.ext rfl) ?_
    ext p
    change p.val ∈ (∅ : Set Y) ↔ p.val ∈ (∅ : Set Y)
    rfl

@[simp] theorem identityEmptyRestriction_val (Y : CMfd.{u} n) (U : Opens Y)
    (r : ℕ) (y : openPreimage (identityEmptyTail Y r) U) :
    (identityEmptyRestriction Y U r y : Y)=y.val := rfl

end
end Hironaka.HironakaSharpActualCurveComparisonRestriction
