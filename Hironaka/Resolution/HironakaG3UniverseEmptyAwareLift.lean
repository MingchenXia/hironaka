import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaG3UniverseLiftedTower
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseEmptyAwareLift
open Hironaka.BlowupSequences BlowupTowers HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower G3UniverseLiftedBlowup G3UniverseEmptyAwareCore
noncomputable section

def liftMap {n : ℕ} {X Y : CMfd.{0} n}
    (f : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) :
    liftCMfd.{u} X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y :=
  (liftDiffeomorph.{u} X).symm.trans (f.trans (liftDiffeomorph.{u} Y))

@[simp] theorem liftMap_trans {n : ℕ} {X Y Z : CMfd.{0} n}
    (f : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (g : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z) :
    liftMap (f.trans g) = (liftMap.{u} f).trans (liftMap.{u} g) := by
  ext p
  simp [liftMap]

@[simp] theorem liftMap_symm {n : ℕ} {X Y : CMfd.{0} n}
    (f : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) :
    liftMap f.symm = (liftMap.{u} f).symm := by
  ext p
  rfl

/-- Literal lifts preserve actual matched and one-sided empty steps. -/
theorem lift_emptyAware {n : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{0} n}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) :
    EmptyAwareTowerIso (liftMap.{u} Φ) (liftTower.{u} T₁) (liftTower.{u} T₂) (liftMap.{u} ψ) := by
  induction h with
  | refl => exact .refl
  | @step Q₁ Q₂ R₁ R₂ T₁ T₂ ψ h C₁ ρ₁ hρ₁ C₂ ρ₂ hρ₂ ψnew hComm hCentre ih =>
    refine .step ih (lifted_blowup hρ₁) (lifted_blowup hρ₂) (liftMap ψnew) ?_ ?_
    · intro p
      simp [liftMap, Function.comp_apply, hComm]
    · ext p
      change ψ ((liftDiffeomorph.{u} Q₁).symm p) ∈ C₂ ↔
        (liftDiffeomorph.{u} Q₁).symm p ∈ C₁
      exact Set.ext_iff.mp hCentre _
  | @leftEmpty Q₁ Q₂ R₁ T₁ T₂ ψ h ρ hρ φ hφ ih =>
    have hφ' : ∀ p, liftMap.{u} φ p = ((liftDiffeomorph.{u} Q₁) ∘ ρ ∘ (liftDiffeomorph.{u} R₁).symm) p := by
      intro p
      simp [liftMap, Function.comp_apply, hφ]
    have hh := EmptyAwareTowerIso.leftEmpty ih (lifted_blowup hρ) (liftMap φ) hφ'
    simpa only [liftTower, preimage_empty, liftMap_trans] using hh
  | @rightEmpty Q₁ Q₂ R₂ T₁ T₂ ψ h ρ hρ φ hφ ih =>
    have hφ' : ∀ p, liftMap.{u} φ p = ((liftDiffeomorph.{u} Q₂) ∘ ρ ∘ (liftDiffeomorph.{u} R₂).symm) p := by
      intro p
      simp [liftMap, Function.comp_apply, hφ]
    have hh := EmptyAwareTowerIso.rightEmpty ih (lifted_blowup hρ) (liftMap φ) hφ'
    simpa only [liftTower, preimage_empty, liftMap_trans, liftMap_symm] using hh
end
end Hironaka.G3UniverseEmptyAwareLift
