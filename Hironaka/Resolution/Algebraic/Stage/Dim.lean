/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The dimension of a triple

Kollár's functors `BO_m`, `BMO_m` of [Kol07, Theorems 68 and 69] are assembled from the stages of
the induction of [Kol07, 70], one stage per dimension bound. A triple is equidimensional by
[Kol07, Notation 64 (1)] — its structure morphism is smooth of ONE relative dimension
(`Triple.smoothOfRelativeDimension : ∃ n, SmoothOfRelativeDimension n (X ↘ Spec k)`) — so "`dim X`",
the maximum of the local dimensions, is that relative dimension: `Triple.dim T` chooses it. Every
triple then lies in the stage `dim X` (`HasDimLE T T.dim`), and `tower base T.dim` is the canonical
stage for `X` (the coherence of `Hironaka.Resolution.Algebraic.Stage.Coherence` makes every higher
stage agree with it). On a nonempty `X` the relative dimension is unique
(`SmoothOfRelativeDimension.eq_of_nonempty`), so `HasDim n ↔ dim = n` and `HasDimLE n ↔ dim ≤ n`
(`HironakaExamples.Stage.BaseCases`); on the empty scheme every `n` is a relative dimension and
`dim` is the chosen one. No cotangent-rank computation is needed: equidimensional triples carry
their dimension as data.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- **The dimension of a triple** (Kollár's `dim X = n` of [Kol07, Theorem 103], for the
equidimensional `X` of [Kol07, Notation 64 (1)]): the relative dimension of its structure morphism,
chosen from `Triple.smoothOfRelativeDimension`; unique when `X` is nonempty
(`SmoothOfRelativeDimension.eq_of_nonempty`). -/
noncomputable def dim (T : Triple k) : ℕ :=
  Classical.choose T.smoothOfRelativeDimension

/-- The chosen relative dimension is a relative dimension of the structure morphism
(`Classical.choose_spec` on `Triple.smoothOfRelativeDimension`). -/
theorem hasDim_dim (T : Triple k) : T.HasDim T.dim :=
  Classical.choose_spec T.smoothOfRelativeDimension

/-- Every triple lies in some stage: the stage of its own dimension. -/
theorem hasDimLE_dim (T : Triple k) : T.HasDimLE T.dim :=
  ⟨T.dim, le_rfl, T.hasDim_dim⟩

end AlgebraicGeometry.Triple
