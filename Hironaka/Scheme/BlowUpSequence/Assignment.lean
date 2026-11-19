/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs

/-!
# Assignments of successions of blow-ups

The data of the functors that the proofs of Kollár's Theorem 36 and of Włodarczyk's Theorem 1.0.2
construct (`Hironaka.Resolution.BRFunctor`, `Hironaka.Resolution.EDFunctor`): a succession of
blow-ups for every input, with no conditions. The
statements of the theorems use `AlgebraicGeometry.BlowUpSequenceFunctor`
(`Hironaka.Scheme.Resolution.Defs`); these unbundled forms are the ones the constructions are
written in. -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

/-- A resolution functor on all algebraic `k`-schemes [Kol07, Theorem 36]: an assignment of a
succession of monoidal transformations `BR(X)` to every scheme of finite type over `Spec k`
(separated, as every scheme of this library). The resolution functor
`Hironaka.Resolution.BRFunctor` is one; the statement of the theorem uses
`AlgebraicGeometry.BlowUpSequenceFunctor`. -/
structure ResolutionAssignment (k : Type u) [Field k] where
  /-- The succession `BR(X)`. -/
  seq : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))],
    BlowUpSequence X

/-- An embedded desingularization assignment [Wlo05, Theorem 1.0.2]: a succession of monoidal
transformations of the smooth ambient `X` for every closed subscheme `Y ⊆ X` (given by its ideal
sheaf). The embedded desingularization functor `Hironaka.Resolution.EDFunctor` is one; the
statement of the theorem, `AlgebraicGeometry.exists_functorial_embeddedDesingularization`, uses
`AlgebraicGeometry.BlowUpSequenceFunctor` on embedded pairs. -/
structure EmbeddedDesingularizationAssignment (k : Type u) [Field k] where
  /-- The succession assigned to `Y ⊆ X`. -/
  seq : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))],
    X.IdealSheafData → BlowUpSequence X

end AlgebraicGeometry
