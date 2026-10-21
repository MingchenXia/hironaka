/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionCartesianTower

/-!
# Literal appended actual Cartesian blowup histories

The original actual smooth pullback history composes across separately selected
auxiliary stages, retaining every literal centre and actual lift. No canonicity
for the whole appended history of a different ideal is asserted.
Blueprint: `hironaka-actual-tower-pullback-append-extension.tex`.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka
open Hironaka.BlowupSequences BlowupTowers
namespace HironakaSmoothSubmersionCartesianTower
variable {n m : ℕ} {X D Z : CMfd.{u} n} {Y D' Z' : CMfd.{u} m}

/-- Append actual stepwise pullbacks without changing a single centre or upper lift. -/
theorem IsActualTowerPullback.append {b : Y → X} {g : D' → D} {k : Z' → Z}
    {Q : BlowupTower Y D'} {T : BlowupTower X D}
    {R : BlowupTower D' Z'} {S : BlowupTower D Z}
    (hT : IsActualTowerPullback b Q T g) (hS : IsActualTowerPullback g R S k) :
    IsActualTowerPullback b (Q.append R) (T.append S) k := by
  induction hS with
  | refl => exact hT
  | step h hg hπ hρ ih => exact IsActualTowerPullback.step ih hg hπ hρ

end HironakaSmoothSubmersionCartesianTower
namespace HironakaActualTowerPullbackAppend
open HironakaSmoothSubmersionCartesianTower
variable {n m : ℕ} {X D Z : CMfd.{u} n} {Y : CMfd.{u} m}

/-- The actual two-stage composite source and its universal square are internally produced. -/
theorem exists_actual_stagewise_composite {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (T : BlowupTower X D) (S : BlowupTower D Z) :
    ∃ (D' Z' : CMfd.{u} m) (Q : BlowupTower Y D') (R : BlowupTower D' Z')
      (g : D' → D) (k : Z' → Z),
      IsActualTowerPullback b Q T g ∧ IsActualTowerPullback g R S k ∧
      IsActualTowerPullback b (Q.append R) (T.append S) k ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ k ∧
      (Q.append R).length=T.length+S.length ∧
      (∀ z,(T.append S).proj (k z)=b ((Q.append R).proj z)) ∧
      HironakaSmoothSubmersionOrderedChoiceBaseChange.HolomorphicSquarePullback
        b k (Q.append R).proj (T.append S).proj := by
  obtain ⟨D',Q,g,hT⟩ := exists_actual_tower hb T
  obtain ⟨Z',R,k,hS⟩ := exists_actual_tower hT.isSubmersion S
  have h := hT.append hS
  refine ⟨D',Z',Q,R,g,k,hT,hS,h,h.isSubmersion,?_,h.proj_comm,h.universal⟩
  rw [h.length_eq,BlowupTower.length_append]

end HironakaActualTowerPullbackAppend
end Hironaka
