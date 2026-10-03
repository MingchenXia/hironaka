/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A restricted tower whose centres miss the open set is an empty tower

Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a and the commutativity with étale morphisms (the invariant
at a point is computed along the part of the resolution after the last stage at which the relevant order changed
near the point; before it, the centres lie over a closed set missing a neighbourhood of the point, so over that
neighbourhood the blowups are isomorphisms -- here, blowups along the empty set).

Let `T` be a tower over `X` and `U ⊆ X` open; `restrict U T` is its restriction to the open preimages of `U`
(`BlowupTowerTransforms.restrict`), whose centres are the traces of the centres of `T`.

* `CentresAvoid U T`: every centre of `T` is disjoint from the preimage of `U` at its stage; `CentresOver F T`: every
  centre lies in the preimage of `F` (both by recursion, like `CoefficientIdealRestriction.CentresIn`).
* `isEmptyTower_restrict_iff`: **`restrict U T` has only empty centres** (`ResolutionInvariantExt.IsEmptyTower`)
  **if and only if `CentresAvoid U T`**.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.RestrictEmptyTower

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit
open Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The centres of `T` miss the open set `U`**: each centre is disjoint from the preimage of `U` at its stage. -/
def CentresAvoid (U : Opens X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X))

/-- **The centres of `T` lie over `F`**: each centre lies in the preimage of `F` at its stage. -/
def CentresOver (F : Set X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CentresOver F T ∧ C ⊆ T.proj ⁻¹' F

@[simp] theorem centresAvoid_refl (U : Opens X) : CentresAvoid U (BlowupTower.refl : BlowupTower X X) := trivial

@[simp] theorem centresOver_refl (F : Set X) : CentresOver F (BlowupTower.refl : BlowupTower X X) := trivial

theorem centresAvoid_step_iff (U : Opens X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    CentresAvoid U (.step T C π hπ) ↔ CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X)) :=
  Iff.rfl

/-- The trace of a set on an open subset is empty iff the set misses it. -/
theorem preimage_val_eq_empty_iff {Y : Type*} [TopologicalSpace Y] (V : Opens Y) (C : Set Y) :
    ((↑) ⁻¹' C : Set V) = ∅ ↔ Disjoint C (V : Set Y) := by
  rw [Set.disjoint_left]
  constructor
  · intro h y hyC hyV
    have hp : (⟨y, hyV⟩ : V) ∈ ((↑) ⁻¹' C : Set V) := hyC
    rw [h] at hp
    exact hp
  · intro h
    ext p
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact fun hp => h hp p.2

/-- **A restricted tower has only empty centres iff the centres of the tower miss the open set.** -/
theorem isEmptyTower_restrict_iff (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower (restrict U T) ↔ CentresAvoid U T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
    show IsEmptyTower (restrict U T) ∧ ((↑) ⁻¹' C : Set (openPreimage T U)) = ∅ ↔
      CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X))
    rw [isEmptyTower_restrict_iff U T, preimage_val_eq_empty_iff]
    rfl

end

end Hironaka.RestrictEmptyTower
