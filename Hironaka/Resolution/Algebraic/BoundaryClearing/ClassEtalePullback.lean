/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.FunctorIndependence
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The class of Lemma 102 is closed under étale pull-backs covering the cosupport

Kollár's functoriality step for order reduction ([Kol07, 104, Step 2.3]) applies Theorem 92 to the
triple handed to `BD_{n,m,0}` and Theorem 97 to the two resulting sequences;
`functor_independent_of_maximalContact_of_closed`
(`Hironaka/Resolution/Algebraic/MaximalContact/FunctorIndependence.lean`) packages both, for a
functor on a class `Dom` closed under the étale pull-backs whose image contains the cosupport
(`ClosedUnderEtalePullbackOverCosupp`). For Lemma 102's class `BDClass n m j` this closure is
elementary: the relative dimension is unchanged along an étale morphism (Mathlib's
`smoothOfRelativeDimension_comp` with the étale morphism of relative dimension `0`), `max-ord` does
not increase under smooth pull-back (`maxOrd_comap_le_of_smooth`,
`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean`), and the inverse image of a divisor
family keeps its index set. Used in `Hironaka/Resolution/Algebraic/OrderReduction/Step22Indep.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme.IdealSheafData

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k]

/-- `BDClass n m j` is closed under pull-back along étale morphisms whose image contains the
cosupport: the closure hypothesis of `functor_independent_of_maximalContact_of_closed` for the
class of [Kol07, Lemma 102]. -/
theorem bdClass_closedUnderEtalePullbackOverCosupp (n m j : ℕ) :
    Scheme.IdealSheafData.ClosedUnderEtalePullbackOverCosupp (Triple.BDClass (k := k) n m j) m := by
  intro T hT Y _ _ _ hY h _ _ _
  obtain ⟨⟨n₀, hn₀n, hn₀⟩, hmax, hj⟩ := hT
  refine ⟨⟨n₀, hn₀n, ?_⟩, ?_, hj⟩
  · have : SmoothOfRelativeDimension n₀ (T.X.left ↘ Spec (.of k)) := hn₀
    have hcomp : SmoothOfRelativeDimension (0 + n₀) (h ≫ (T.X.left ↘ Spec (.of k))) := inferInstance
    have e : h ≫ (T.X.left ↘ Spec (.of k)) = Y ↘ Spec (.of k) :=
      comp_over (f := h) (S := Spec (CommRingCat.of k))
    rw [e, Nat.zero_add] at hcomp
    exact hcomp
  · exact (maxOrd_comap_le_of_smooth h T.I).trans hmax

end Hironaka.BO
