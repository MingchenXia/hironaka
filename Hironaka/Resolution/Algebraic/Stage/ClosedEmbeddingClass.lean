/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.EmptyFamily
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Algebra.Util.JacobsonCover
import Hironaka.Resolution.Algebraic.OrderReduction.Step3Globalization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The class of the source of a closed embedding

Kollár's Claim 71.2 [Kol07, Claim 71.2] compares `BMO_1(X, I, 1, ∅)` with `τ_* BMO_1(Y, J, 1, ∅)`
for a closed embedding `τ : Y ↪ X` of smooth schemes. In the library the functors are the stage
functors of the tower (`Hironaka.Resolution.Algebraic.Stage.Tower`), defined on the class
`MarkedTriple.BMOClass n 1` — mark `1` and dimension `≤ n`. The triple of `X` is in the class by
hypothesis; the triple of `Y` is in it because a closed subscheme smooth over `k` of a scheme of
dimension `≤ n` has dimension `≤ n` and carries the same mark (`MarkedTriple.ClosedEmbedding`). This
module proves that membership, `bmoClass_of_closedEmbedding`, so that the identity of Claim 71.2
(`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingGeneral`) can be stated without taking `Y`'s
class as a hypothesis Kollár does not have.

The dimension inequality `dim Y ≤ dim X` is read off the Krull dimension of the stalks at a closed
point (`Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed`, over a perfect field —
`PerfectField.ofCharZero`): the stalk of `Y` at a closed point `p` is a quotient of the stalk of `X`
at `τ p` (the stalk map of a closed immersion is surjective), so its Krull dimension is at most that
of `X`'s stalk (Mathlib's `ringKrullDim_le_of_surjective`); `τ p` is a closed point (a closed
immersion is a closed embedding), and a closed point of `Y` exists when `Y` is nonempty (`Y` is of
finite type over `k`, hence Jacobson — `exists_isClosed_singleton_mem_specializes`); an empty `Y`
has every relative dimension (`smoothOfRelativeDimension_of_isEmpty`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme

namespace Hironaka.Stage

variable {k : Type u} [Field k]

/-- **A closed embedding of smooth `k`-schemes does not raise the dimension bound**: for `j : Y ↪ X`
a closed immersion with `X` of dimension `≤ n`, `Y` has dimension `≤ n` — at a closed point `p` of
`Y` the stalk of `Y` is a quotient of the stalk of `X` at the closed point `j p`, so
`dim Y = dim 𝒪_{Y,p} ≤ dim 𝒪_{X,j p} = dim X` (the Krull dimension of the stalks at closed points of
a scheme smooth of relative dimension `d` over a perfect field). Only the closed immersion and the
two triples' smoothness enter; the `k`-compatibility of `j` is not needed. -/
theorem hasDimLE_of_closedEmbedding [CharZero k] {TX TY : Triple k} (j : TY.X.left ⟶ TX.X.left)
    [IsClosedImmersion j] {n : ℕ} (hX : TX.HasDimLE n) : TY.HasDimLE n := by
  obtain ⟨dX, hdXn, hdX⟩ := hX
  obtain ⟨dY, hdY⟩ := TY.smoothOfRelativeDimension
  by_cases hemp : IsEmpty TY.X.left
  · exact ⟨0, Nat.zero_le _, Hironaka.BO.smoothOfRelativeDimension_of_isEmpty _ 0⟩
  · rw [not_isEmpty_iff] at hemp
    obtain ⟨y⟩ := hemp
    have : JacobsonSpace TY.X.left :=
      LocallyOfFiniteType.jacobsonSpace (TY.X.left ↘ Spec (CommRingCat.of k))
    obtain ⟨p, hp, -, -⟩ := exists_isClosed_singleton_mem_specializes
      (X := TY.X.left) isClosed_univ (Set.mem_univ y)
    have hjp : IsClosed ({j.base p} : Set TX.X.left) := by
      have := j.isClosedEmbedding.isClosedMap _ hp
      rwa [Set.image_singleton] at this
    have : PerfectField k := PerfectField.ofCharZero
    have : SmoothOfRelativeDimension dX (TX.X.left ↘ Spec (CommRingCat.of k)) := hdX
    have : SmoothOfRelativeDimension dY (TY.X.left ↘ Spec (CommRingCat.of k)) := hdY
    have hX' := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed
      (TX.X.left ↘ Spec (CommRingCat.of k)) dX hjp
    have hY' := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed
      (TY.X.left ↘ Spec (CommRingCat.of k)) dY hp
    have hle := ringKrullDim_le_of_surjective (j.stalkMap p).hom (j.stalkMap_surjective p)
    rw [hX', hY'] at hle
    have hdd : dY ≤ dX := by exact_mod_cast hle
    exact ⟨dY, hdd.trans hdXn, hdY⟩

/-- **The source of a closed embedding of marked triples with `E = ∅` and mark `1` is in the stage
class**: `TY.BMOClass n 1` from `TX.BMOClass n 1` — the mark is transported by
`MarkedTriple.ClosedEmbedding`, the dimension bound by `hasDimLE_of_closedEmbedding`. This is the
class proof on the side of `Y` in the statements of Claim 71.2. -/
theorem bmoClass_of_closedEmbedding [CharZero k] {TX TY : MarkedTriple k}
    {j : TY.X.left ⟶ TX.X.left}
    [IsClosedImmersion j] (hj : MarkedTriple.ClosedEmbedding TX TY j) {n : ℕ}
    (hTX : TX.BMOClass n 1) : TY.BMOClass n 1 :=
  ⟨le_rfl, hasDimLE_of_closedEmbedding j hTX.2.1, hj.2.trans hTX.2.2⟩

end Hironaka.Stage
