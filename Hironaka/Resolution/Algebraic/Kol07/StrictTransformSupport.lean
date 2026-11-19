/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.BlowUp.Composite
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The strict transforms along a sequence lie over each other

In the restriction of a blow-up sequence to a closed subscheme [Kol07, 30.2] the strict transform
`S_{i+1} ⊆ X_{i+1}` of `S_i ⊆ X_i` maps into `S_i`. Along a blow-up sequence, a point of the strict
transform `X̄_i` at stage `i` therefore maps to a point of the strict transform `X̄_j` at every
earlier stage `j ≤ i`, and to `V(J)` at stage `0`. The one-blow-up step is the description of the
support of the strict transform as the closure of `π⁻¹(V(J)) ∖ π⁻¹(V(D))`
(`coe_support_strictTransform`), which lies in the closed set `π⁻¹(V(J))`.

* `stageMap_mem_support_of_mem_support_strictTransformSeq`: `Π_i(X̄_i) ⊆ V(J)`.
* `stageMapBetween_mem_support_strictTransformSeq`: the stage maps carry `X̄_i` into `X̄_j`.

Used for clause (3) of [Kol07, Theorem 36]: a point of the end result `X̄_r` over an earlier
center `Z_m` lies over the restricted center `Z_m ∩ X̄_m`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence
  TopologicalSpace

namespace Hironaka.Sequence

variable {X : Scheme.{u}}

/-- One blow-up: a point of the strict transform of `J` maps to `V(J)`
(`coe_support_strictTransform`: the support is the closure of a subset of `π⁻¹(V(J))`). -/
theorem blowUpπ_mem_support_of_mem_support_strictTransform [IsLocallyNoetherian X]
    (D J : X.IdealSheafData) {x' : D.blowUp} (hx' : x' ∈ (J.strictTransform D).support) :
    D.blowUpπ x' ∈ J.support := by
  have h : x' ∈ ((J.strictTransform D).support : Set D.blowUp) := hx'
  rw [coe_support_strictTransform] at h
  have hsub : closure (D.blowUpπ ⁻¹' (J.support : Set X) \
      D.blowUpπ ⁻¹' (D.support : Set X)) ⊆ D.blowUpπ ⁻¹'
          (J.support : Set X) :=
    closure_minimal Set.sdiff_subset (J.support.isClosed.preimage D.blowUpπ.continuous)
  exact hsub h

/-- [Kol07, 30.2] along a sequence (`⟨j, hj⟩` form): `Π_j` maps the strict transform `X̄_j` of
`V(J)` into `V(J)`. -/
theorem stageMap_mem_support_of_mem_support_strictTransformSeq_mk :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) [IsLocallyNoetherian X] (J : X.IdealSheafData)
      (j : ℕ) (hj : j < S.length + 1) (p : S.stage ⟨j, hj⟩),
      p ∈ (S.strictTransformSeq J ⟨j, hj⟩).support → S.stageMap ⟨j, hj⟩ p ∈ J.support
  | _, nil Y, _, J, j, hj, p, hp => by
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    exact hp
  | _, cons Y D rest, _, J, 0, hj, p, hp => hp
  | _, cons Y D rest, _, J, j + 1, hj, p, hp => by
    have : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    have ih := stageMap_mem_support_of_mem_support_strictTransformSeq_mk rest (J.strictTransform D)
      j (Nat.lt_of_succ_lt_succ hj) p hp
    exact blowUpπ_mem_support_of_mem_support_strictTransform D J ih

/-- [Kol07, 30.2] along a sequence: `Π_i` maps the strict transform `X̄_i` of `V(J)` into `V(J)`. -/
theorem stageMap_mem_support_of_mem_support_strictTransformSeq [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (J : X.IdealSheafData) (i : Fin (S.length + 1)) {p : S.stage i}
    (hp : p ∈ (S.strictTransformSeq J i).support) : S.stageMap i p ∈ J.support := by
  obtain ⟨j, hj⟩ := i
  exact stageMap_mem_support_of_mem_support_strictTransformSeq_mk S J j hj p hp

/-- [Kol07, 30.2] along a sequence (`⟨j, hj⟩` form): the stage map from stage `i` to an earlier
stage `j` carries the strict transform `X̄_i` into `X̄_j`. -/
theorem stageMapBetween_mem_support_strictTransformSeq_mk :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) [IsLocallyNoetherian X] (J : X.IdealSheafData)
      (i j : ℕ) (hi : i < S.length + 1) (hj : j < S.length + 1) (hji : j ≤ i)
      (p : S.stage ⟨i, hi⟩), p ∈ (S.strictTransformSeq J ⟨i, hi⟩).support →
        S.stageMapBetween ⟨i, hi⟩ ⟨j, hj⟩ hji p ∈ (S.strictTransformSeq J ⟨j, hj⟩).support
  | _, nil Y, _, J, i, j, hi, hj, hji, p, hp => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    exact hp
  | _, cons Y D rest, _, J, 0, j, hi, hj, hji, p, hp => by
    obtain rfl : j = 0 := Nat.le_zero.mp hji
    exact hp
  | _, cons Y D rest, _, J, i + 1, 0, hi, hj, hji, p, hp =>
    stageMap_mem_support_of_mem_support_strictTransformSeq_mk (cons Y D rest) J (i + 1) hi p hp
  | _, cons Y D rest, _, J, i + 1, j + 1, hi, hj, hji, p, hp => by
    have : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    exact stageMapBetween_mem_support_strictTransformSeq_mk rest (J.strictTransform D) i j
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) (Nat.le_of_succ_le_succ hji) p hp

/-- [Kol07, 30.2] along a sequence: the stage map from stage `i` to an earlier stage `j` carries
the strict transform `X̄_i` of `V(J)` into `X̄_j`. -/
theorem stageMapBetween_mem_support_strictTransformSeq [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (J : X.IdealSheafData) {i j : Fin (S.length + 1)} (hji : j ≤ i)
    {p : S.stage i} (hp : p ∈ (S.strictTransformSeq J i).support) :
    S.stageMapBetween i j hji p ∈ (S.strictTransformSeq J j).support := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  exact stageMapBetween_mem_support_strictTransformSeq_mk S J i j hi hj hji p hp

end Hironaka.Sequence
