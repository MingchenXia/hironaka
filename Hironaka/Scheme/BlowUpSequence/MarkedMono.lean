/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Order `≥ m` for a smaller marked ideal along the same sequence

In the proof of Theorem 107, order reduction for the monomial part `M(I)` is run where `I = M(I)`,
off the cosupport of the nonmonomial part [Kol07, 111, Steps 2 and 3]. In this library the
geometric third step is run on `X` itself for the marked ideal `(M(I), m)`, and its centers are
read as centers for `(I, m)`: the sequence is of order `≥ m` for `(I, m)` because `I ⊆ M(I)` and
the marked transform is monotone in the ideal (`markedTransformSeq_mono`), so at every center
`ord_{Z_i} I_i ≥ ord_{Z_i} M_i ≥ m` (a smaller ideal has the larger cosupport, property (1) of
the cosupport in [Kol07, Definition 59]). This is the marked analogue of
`isOrderGeSeq_of_isOrderSeq_of_le` (`Hironaka/Scheme/BlowUpSequence/MarkedLeWeak.lean`: order `d ≥
m` for `J` unmarked, hence `≥ m` for `(I, m)` marked); here both ideals are marked at the same `m`.

* `isOrderGeSeq_of_le`: a smooth blow-up sequence of order `≥ m` for `(X, J, m, E)` is one for
  `(X, I, m, E)` whenever `I ≤ J` (same centers, same boundaries; no smoothness of `X` enters).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A smooth blow-up sequence of order `≥ m` for `(X, J, m, E)` is a smooth blow-up sequence of
order `≥ m` for `(X, I, m, E)` whenever `I ⊆ J`: the same centers, smooth and with simple normal
crossings with the same boundaries, and `ord_{Z_i} I_i ≥ ord_{Z_i} J_i ≥ m` at every stage since
`Π^{-1}_{i *}(I, m) ⊆ Π^{-1}_{i *}(J, m)` ("`cosupp(I, m) ⊃ cosupp(J, m)` for `I ⊂ J`",
[Kol07, Definition 59]). The marked analogue of `isOrderGeSeq_of_isOrderSeq_of_le`; no
smoothness of `X` is used beyond what `IsOrderGeSeq f` carries. -/
theorem isOrderGeSeq_of_le {I J : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
    {S : BlowUpSequence X} (hS : S.IsOrderGeSeq f J m E) (hIJ : I ≤ J) :
    S.IsOrderGeSeq f I m E :=
  ⟨hS.1, fun i => ⟨(hS.2 i).1, fun η hη =>
    le_trans ((hS.2 i).2 η hη) (IdealSheafData.ord_anti (markedTransformSeq_mono S hIJ m
        i.castSucc) η)⟩⟩

end AlgebraicGeometry
