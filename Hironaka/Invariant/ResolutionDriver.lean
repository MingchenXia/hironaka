/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Blowup.BlowupExistence
import Hironaka.Blowup.BlowupCompact
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false

/-!
# The driver of the canonical resolution: iterate the blowup of the maximum locus

Sources: Bierstone--Milman 2008 §7 (the centre of each blowup is the maximum locus of an upper semicontinuous
invariant), Włodarczyk 2005 (Theorem 2.0.1 and the end of the proof of the resolution theorem), Kollár 2007 (§3.4:
the resolution is obtained by iterating the blowup of the maximum locus).

A tower is a *canonical segment* for an invariant `inv` (a function on the last stage of every tower) if each of its centres
is nonempty and is the set where `inv` of the preceding part attains its maximum on the cosupport
(`IsCanonicalSegment`; Definition `hir:centre-function`, with no empty steps).  Given the properties (1) (the maximum locus
is an admissible centre) and (2) (upper semicontinuity) of `hir:centre-function`, closed cosupports, and either

* (8) a bound on the length of canonical segments over a compact base, or
* (3) a strict drop of the invariant under the blowup of its maximum locus, with values in a well-founded order,

the blowup of the maximum locus can be iterated until the cosupport is empty: a resolution (`IsGeoResolution`).  The
blowups exist by Demailly's construction (`BlowupExistence.exists_isBlowupAlong`), and every stage over a compact base is
compact (`BlowupCompact.compactSpace_of_isBlowupAlong`), so the maximum is attained
(`ResolutionInvariantOrder.IsInvUSCOn.exists_isMaxOn`).

## Main results

* `compactSpace_of_tower`, `exists_blowup`: stages of towers over a compact base are compact; admissible centres with empty
  interior can be blown up;
* `maxLocus_nonempty`: on a compact stage the maximum locus of an upper semicontinuous invariant on a nonempty closed
  cosupport is nonempty;
-/

open Set

namespace Hironaka.ResolutionDriver

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
open Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantOrder

universe u

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Every stage of a tower over a compact manifold is compact.** -/
theorem compactSpace_of_tower [CompactSpace X] :
    ∀ {Y : CMfd.{u} n} (_ : BlowupTower X Y), CompactSpace Y
  | _, .refl => inferInstance
  | _, .step T _ _ hπ => by
    have := compactSpace_of_tower T
    exact BlowupCompact.compactSpace_of_isBlowupAlong hπ

/-- **A closed submanifold with empty interior can be blown up** (Demailly's blowup). -/
theorem exists_blowup {Y : CMfd.{u} n} (C : Set Y) (hC : IsClosedSubmanifold n C) (hint : interior C = ∅) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y), IsBlowupAlong n C π := by
  obtain ⟨Z, _, _, _, π, hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hint
  exact ⟨CMfd.of Z, π, hπ⟩

section Invariant

variable {Λ : Type*} [LinearOrder Λ]

/-- The **maximum locus** of `f` on `s`: the points of `s` at which `f` attains its maximum on `s`. -/
def maxLocus {Y : Type*} (f : Y → Λ) (s : Set Y) : Set Y :=
  {y | y ∈ s ∧ ∀ y' ∈ s, f y' ≤ f y}

/-- **Canonical segment** of `𝔪` for the invariant `inv` (Definition `hir:centre-function`, without empty steps): every
centre is nonempty and is the maximum locus of the invariant of the preceding part on its cosupport. -/
def IsCanonicalSegment (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ =>
    IsCanonicalSegment 𝔪 inv T ∧ C.Nonempty ∧ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp

@[simp] theorem isCanonicalSegment_refl (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    IsCanonicalSegment 𝔪 inv (BlowupTower.refl : BlowupTower X X) := trivial

theorem isCanonicalSegment_step_iff (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    IsCanonicalSegment 𝔪 inv (BlowupTower.step T C π hπ) ↔
      IsCanonicalSegment 𝔪 inv T ∧ C.Nonempty ∧ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp :=
  Iff.rfl

/-- **The maximum locus is nonempty** on a compact space, for an upper semicontinuous invariant on a nonempty closed set. -/
theorem maxLocus_nonempty {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] {f : Y → Λ} {s : Set Y}
    (hs : IsClosed s) (hf : IsInvUSCOn f s) (hne : s.Nonempty) : (maxLocus f s).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hf.exists_isMaxOn hs.isCompact hne
  exact ⟨x, hx, hmax⟩

end Invariant

end Hironaka.ResolutionDriver
