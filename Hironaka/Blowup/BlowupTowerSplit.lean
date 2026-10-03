/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Blowup.BlowupSequences
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Splitting a tower before its last blowups

In the maximal-order case and the general step of the resolution algorithm (`hir:maximal-order-step`,
`hir:general-step`) the lower-dimensional invariant at a point is computed along the part of the segment since a
stage which depends on the point (the last stage at which its number of boundary members, its membership of `Z₁`, or
the order of the non-monomial part changed); nearby points are compared by re-basing
(`ResolutionInvariantExt.ResolutionInvariant.emptyPrefix`). Source: Włodarczyk 2005, proof of Proposition `pr:resol`
(the invariants are assigned "at the moment [the points] are getting blown-up" and "remain unchanged when the points
are transformed isomorphically").

`split T j` cuts a tower `T : X ← ⋯ ← Y` before its last `j` blowups (all of them if `j ≥ length T`): a stage `Y₀`, the head
`T₀ : X ← ⋯ ← Y₀` and the tail `T₁ : Y₀ ← ⋯ ← Y` with `T₀ T₁ = T`.

## Main results

* `split`, `head`, `tail`: the split, with `head_append_tail : (head T j).append (tail T j) = T`;
* `length_tail`, `length_head`: the tail has `min j (length T)` blowups, the head the rest;
* `geoTransformAlong_head_tail`, `isGeoTestTower_iff_head_tail`: projections, transforms and multiple test blow-ups
  along the split;
* `isCanonical_of_append`, `isCanonical_head`: a prefix of a canonical segment is a canonical segment;
* `isEmptyTower_append_iff`: a concatenation has only empty centres iff both parts have;
-/

open Set

universe u v

namespace Hironaka.BlowupTowerSplit

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.ResolutionDriver
open Hironaka.ResolutionInvariantSpec (IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The split of a tower before its last `j` blowups**: the stage, the head and the tail. -/
def split : {Y : CMfd.{u} n} → BlowupTower X Y → ℕ → Σ Y₀ : CMfd.{u} n, BlowupTower X Y₀ × BlowupTower Y₀ Y
  | _, T, 0 => ⟨_, T, .refl⟩
  | _, .refl, _ + 1 => ⟨X, .refl, .refl⟩
  | _, .step T C π hπ, j + 1 => ⟨(split T j).1, (split T j).2.1, .step (split T j).2.2 C π hπ⟩

/-- The head of the split: the tower up to the stage before the last `j` blowups. -/
abbrev head {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) : BlowupTower X (split T j).1 := (split T j).2.1

/-- The tail of the split: the last `j` blowups (all of them if `j ≥ length T`). -/
abbrev tail {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) : BlowupTower (split T j).1 Y := (split T j).2.2

/-- **The head followed by the tail is the tower.** -/
theorem head_append_tail : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ), (head T j).append (tail T j) = T
  | _, .refl, 0 => rfl
  | _, .step _ _ _ _, 0 => rfl
  | _, .refl, _ + 1 => rfl
  | _, .step T C π hπ, j + 1 => by
      show (head T j).append (.step (tail T j) C π hπ) = .step T C π hπ
      rw [BlowupTower.append_step, head_append_tail T j]

/-- The tail has `min j (length T)` blowups. -/
theorem length_tail : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ), (tail T j).length = min j T.length
  | _, .refl, 0 => rfl
  | _, .step _ _ _ _, 0 => by simp [tail, split]
  | _, .refl, _ + 1 => rfl
  | _, .step T C π hπ, j + 1 => by
      show (BlowupTower.step (tail T j) C π hπ).length = min (j + 1) (BlowupTower.step T C π hπ).length
      rw [BlowupTower.length_step, BlowupTower.length_step, length_tail T j]
      omega

/-- The head has the remaining `length T - j` blowups. -/
theorem length_head {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) : (head T j).length = T.length - j := by
  have h := congrArg BlowupTower.length (head_append_tail T j)
  rw [BlowupTower.length_append, length_tail] at h
  omega

/-- **Transforms along the split**: the transform along `T` is the transform of the transform along the head, along the
tail. -/
theorem geoTransformAlong_head_tail (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) :
    geoTransformAlong 𝔪 T = geoTransformAlong (geoTransformAlong 𝔪 (head T j)) (tail T j) := by
  conv_lhs => rw [← head_append_tail T j]
  exact geoTransformAlong_append 𝔪 _ _

/-- **Multiple test blow-ups along the split.** -/
theorem isGeoTestTower_iff_head_tail (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) :
    IsGeoTestTower 𝔪 T ↔
      IsGeoTestTower 𝔪 (head T j) ∧ IsGeoTestTower (geoTransformAlong 𝔪 (head T j)) (tail T j) := by
  conv_lhs => rw [← head_append_tail T j]
  exact isGeoTestTower_append_iff 𝔪 _ _

/-- **A prefix of a canonical segment is a canonical segment.** -/
theorem isCanonical_of_append {Λ : Type v} [LinearOrder Λ] (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y), IsCanonical 𝔪 inv (T₀.append T₁) → IsCanonical 𝔪 inv T₀
  | _, .refl, h => h
  | _, .step T₁ C π hπ, h => by
      obtain ⟨h1, -⟩ : IsCanonical 𝔪 inv (T₀.append T₁) ∧
          (C = ∅ ∨ C = maxLocus (inv (T₀.append T₁)) (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp) := h
      exact isCanonical_of_append 𝔪 inv T₀ T₁ h1

/-- The head of a canonical segment is a canonical segment. -/
theorem isCanonical_head {Λ : Type v} [LinearOrder Λ] (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ)
    (h : IsCanonical 𝔪 inv T) : IsCanonical 𝔪 inv (head T j) := by
  rw [← head_append_tail T j] at h
  exact isCanonical_of_append 𝔪 inv _ _ h

/-- **A concatenation has only empty centres iff both parts have.** -/
theorem isEmptyTower_append_iff {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y), IsEmptyTower (T₀.append T₁) ↔ IsEmptyTower T₀ ∧ IsEmptyTower T₁
  | _, .refl => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | _, .step T₁ C π hπ => by
      show (IsEmptyTower (T₀.append T₁) ∧ C = ∅) ↔ (IsEmptyTower T₀ ∧ (IsEmptyTower T₁ ∧ C = ∅))
      rw [isEmptyTower_append_iff T₀ T₁, and_assoc]

end

end Hironaka.BlowupTowerSplit
