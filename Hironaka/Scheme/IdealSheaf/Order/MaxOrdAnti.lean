/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The maximal order is antitone in the ideal sheaf

[Kol07, Definition 47]: `ord_x I ≥ r` iff `I_x ⊆ 𝔪_x^r`, and `max-ord I := max{ord_x I : x ∈ X}`.
A larger ideal sheaf has a smaller order at every point (`ord_anti`,
`Hironaka/Scheme/IdealSheaf/Order/Basic.lean`), hence a smaller maximal order:

* `maxOrd_anti`: `I ≤ J → max-ord J ≤ max-ord I`;
* `maxOrdAlong_anti`: the same along a subset `Z`.

Used in the first step of the proof of [Kol07, Theorem 107] ([Kol07, 111]) in the form
`max-ord N(J) ≤ max-ord J` for the nonmonomial part `N(J) ⊇ J`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step1NonmonomialPart.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Clause3.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step2Separation.lean`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- The maximal order along a subset is antitone in the ideal sheaf — pointwise `ord_anti` under
the supremum. -/
theorem maxOrdAlong_anti {I J : X.IdealSheafData} (h : I ≤ J) (Z : Set X) :
    J.maxOrdAlong Z ≤ I.maxOrdAlong Z := by
  rw [maxOrdAlong_eq_sSup_image, maxOrdAlong_eq_sSup_image]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (ord_anti h x).trans (le_sSup ⟨x, hx, rfl⟩)

/-- The maximal order is antitone in the ideal sheaf, `I ≤ J → max-ord J ≤ max-ord I`; in its use,
`max-ord N(J) ≤ max-ord J` since `J ⊆ N(J)`. -/
theorem maxOrd_anti {I J : X.IdealSheafData} (h : I ≤ J) : J.maxOrd ≤ I.maxOrd :=
  (maxOrd_le_iff J).mpr fun x => (ord_anti h x).trans (le_maxOrd I x)

end AlgebraicGeometry.Scheme.IdealSheafData
