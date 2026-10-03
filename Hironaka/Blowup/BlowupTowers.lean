/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Towers of blowups, recorded as data

Source: the sequences `X_0 = X ← X_1 ← ⋯ ← X_r` of blowups with smooth centres of Włodarczyk 2005 §2.1 ("multiple
test blow-ups"), Bierstone--Milman 2008 Theorem 1.3 and Definitions 2.4.

`Hironaka.BlowupSequences.IsBlowupSequence` is a `Prop`: it says that a map is SOME finite composite of blowups, and
forgets the intermediate spaces and centres. The resolution algorithm needs them as data -- the marked ideal is
transformed step by step, the invariant at a stage depends on the earlier ones, and towers are concatenated. This
file provides that data structure.

## Design (R1)

* `CMfd n` bundles a complex manifold of dimension `n` (type, topology, atlas, `IsComplexManifold`),
  so that a sequence of DIFFERENT manifold types can be an index of an inductive family without
  instance arguments.  `CMfd.of X` bundles an unbundled one; its carrier is `X` definitionally.
* `BlowupTower X Y` is the inductive family of paths `X ← ⋯ ← Y` (the free category on blowups):
  `refl : BlowupTower X X` and `step T C π hπ : BlowupTower X Z` for `T : BlowupTower X Y` and a
  blowup `π : Z → Y` along `C`.  The LAST space is an index, so concatenation `append` needs no
  cast, and `proj`, `length`, … are structural recursions.
* Steps along the empty centre are allowed (`IsBlowupAlong n ∅ π` holds for biholomorphisms); this
  is how Włodarczyk's "isomorphisms" in multiple test blow-ups and extensions (restriction to open
  sets) are encoded, with no separate constructor.

## Main declarations

* `CMfd`, `CMfd.of`;
* `BlowupTower`, `proj`, `length`, `append`, `proj_append`, `length_append`, `append_refl`,
  `refl_append`, `append_assoc`;

Restriction of a tower to an open subset needs the restriction of a single blowup to an open subset.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.BlowupTowers

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences

noncomputable section

/-- A complex manifold of dimension `n` (Hausdorff, second countable, holomorphic atlas), bundled
with its structure. -/
structure CMfd (n : ℕ) : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace (ComplexModel n) carrier]
  [isComplexManifold : IsComplexManifold n carrier]

attribute [instance] CMfd.topologicalSpace CMfd.chartedSpace CMfd.isComplexManifold

namespace CMfd

variable {n : ℕ}

instance : CoeSort (CMfd.{u} n) (Type u) := ⟨CMfd.carrier⟩

/-- Bundle a complex manifold. -/
abbrev of (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] : CMfd.{u} n :=
  ⟨X⟩

end CMfd

/-- **A tower of blowups** `X ← ⋯ ← Y` with smooth centres, recorded with all intermediate spaces,
centres and maps.  The last space `Y` is the index. -/
inductive BlowupTower {n : ℕ} (X : CMfd.{u} n) : CMfd.{u} n → Type (u + 1)
  /-- The empty tower. -/
  | refl : BlowupTower X X
  /-- Blow up the last space `Y` of `T` along the closed submanifold `C`. -/
  | step {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
      (hπ : IsBlowupAlong n C π) : BlowupTower X Z

namespace BlowupTower

variable {n : ℕ} {X Y Z W : CMfd.{u} n}

/-- The composite map from the last space to the base. -/
def proj : {Y : CMfd.{u} n} → BlowupTower X Y → Y → X
  | _, refl => id
  | _, step T _ π _ => proj T ∘ π

/-- The number of blowups. -/
def length : {Y : CMfd.{u} n} → BlowupTower X Y → ℕ
  | _, refl => 0
  | _, step T _ _ _ => length T + 1

@[simp] theorem proj_refl : (refl : BlowupTower X X).proj = id := rfl

@[simp] theorem proj_step (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) : (step T C π hπ).proj = T.proj ∘ π := rfl

@[simp] theorem length_refl : (refl : BlowupTower X X).length = 0 := rfl

@[simp] theorem length_step (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) : (step T C π hπ).length = T.length + 1 := rfl

/-- **A tower is a blowup sequence.** -/
theorem isBlowupSequence (T : BlowupTower X Y) : IsBlowupSequence n X Y T.proj := by
  induction T with
  | refl => exact IsBlowupSequence.refl
  | step T C π hπ ih => exact IsBlowupSequence.step _ C π ih hπ

/-- The projection of a tower is holomorphic. -/
theorem contMDiff_proj (T : BlowupTower X Y) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ T.proj :=
  T.isBlowupSequence.contMDiff

/-- Concatenation of towers: first `T`, then `S` over the last space of `T`. -/
def append (T : BlowupTower X Y) : {Z : CMfd.{u} n} → BlowupTower Y Z → BlowupTower X Z
  | _, refl => T
  | _, step S C π hπ => step (append T S) C π hπ

@[simp] theorem append_refl (T : BlowupTower X Y) : T.append refl = T := rfl

@[simp] theorem append_step (T : BlowupTower X Y) (S : BlowupTower Y Z) (C : Set Z)
    (π : W → Z) (hπ : IsBlowupAlong n C π) :
    T.append (step S C π hπ) = step (T.append S) C π hπ := rfl

@[simp] theorem refl_append (S : BlowupTower X Y) : (refl : BlowupTower X X).append S = S := by
  induction S with
  | refl => rfl
  | step S C π hπ ih => simp [append, ih]

theorem append_assoc {V : CMfd.{u} n} (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (R : BlowupTower Z V) : (T.append S).append R = T.append (S.append R) := by
  induction R with
  | refl => rfl
  | step R C π hπ ih => simp [append, ih]

theorem proj_append (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    (T.append S).proj = T.proj ∘ S.proj := by
  induction S with
  | refl => rfl
  | step S C π hπ ih => simp only [append, proj, ih]; rfl

theorem length_append (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    (T.append S).length = T.length + S.length := by
  induction S with
  | refl => rfl
  | step S C π hπ ih => simp only [append, length, ih]; omega

end BlowupTower

end

end Hironaka.BlowupTowers
