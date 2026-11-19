import Hironaka.Resolution.HironakaG3UniverseEmptyAwareLift
universe u
namespace Hironaka.G3UniverseEmptyAwareJoin
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism G3UniverseEmptyAwareCore
universe v

/-- Transport a supplied physical comparison across the actual isomorphism at each end. -/
theorem physical_comparison_between_isomorphic_towers {n : ℕ}
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : CMfd.{v} n}
    {α : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {β : X₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₃}
    {γ : X₄ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₃}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {T₃ : BlowupTower X₃ Y₃} {T₄ : BlowupTower X₄ Y₄}
    {χ₁ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    {χ₂ : Y₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₃}
    {χ₃ : Y₄ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₃}
    (h₁ : IsTowerIso α T₁ T₂ χ₁) (h₂ : EmptyAwareTowerIso β T₂ T₃ χ₂)
    (h₃ : IsTowerIso γ T₄ T₃ χ₃) :
    EmptyAwareTowerIso ((α.trans β).trans γ.symm) T₁ T₄ ((χ₁.trans χ₂).trans χ₃.symm) :=
  trans (trans (emptyAware_of_isTowerIso h₁) h₂) (symm (emptyAware_of_isTowerIso h₃))
end Hironaka.G3UniverseEmptyAwareJoin

namespace Hironaka.G3UniverseEmptyAwareJoin
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseEmptyAwareCore
  G3UniverseEmptyAwareLift

/-- A supplied small physical comparison joins two actual isomorphisms to its literal lift. -/
theorem physical_comparison_of_lifted_small {n : ℕ}
    {X₁ X₄ Y₁ Y₄ : CMfd.{u} n} {X₂ X₃ Y₂ Y₃ : CMfd.{0} n}
    {α : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} X₂}
    {β : X₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₃}
    {γ : X₄ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} X₃}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {T₃ : BlowupTower X₃ Y₃} {T₄ : BlowupTower X₄ Y₄}
    {χ₁ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y₂}
    {χ₂ : Y₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₃}
    {χ₃ : Y₄ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y₃}
    (h₁ : IsTowerIso α T₁ (liftTower.{u} T₂) χ₁) (h₂ : EmptyAwareTowerIso β T₂ T₃ χ₂)
    (h₃ : IsTowerIso γ T₄ (liftTower.{u} T₃) χ₃) :
    EmptyAwareTowerIso ((α.trans (liftMap.{u} β)).trans γ.symm) T₁ T₄
      ((χ₁.trans (liftMap.{u} χ₂)).trans χ₃.symm) :=
  physical_comparison_between_isomorphic_towers h₁ (lift_emptyAware.{u} h₂) h₃
end Hironaka.G3UniverseEmptyAwareJoin
