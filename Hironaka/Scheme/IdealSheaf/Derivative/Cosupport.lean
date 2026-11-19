/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
import Hironaka.Algebra.Order.Cosupport
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The cosupport transfer `{ord_x I ≥ m} = V(D^{m−1} I)`

[Kol07, Lemma 74 (3)]: `cosupp(I, m) = cosupp(Dʳ(I), m − r)` for `r < m`, "char. 0 only!";
[Wlo05, Lemma 2.6.2]: `supp(I, μ) = supp(Dⁱ(I), μ − i)` for `i ≤ μ − 1`, so that
`supp(I, μ) = V(D^{μ−1}(I))` is closed. On a scheme smooth of relative dimension `n` over a field
`k` of characteristic zero:

  `ord_x I ≥ m ⟺ ord_x Dʳ(I) ≥ m − r` for `r < m` (`le_ord_iff_le_ord_derivativeIter`), in
  particular `{x : ord_x I ≥ m} = V(D^{m−1} I)` (`le_ord_iff_mem_support_derivativeIter`).

At the stalk `𝒪_{X,x}` (the order of the stalk ideal, `Hironaka/Scheme/IdealSheaf/Order/Basic.lean`;
`Dʳ(I)_x = Dʳ(I_x)`, `Hironaka/Scheme/IdealSheaf/Derivative/Sheaf.lean`), the two directions are:
`⟹` for every derivation, by Leibniz (`derivativeIter_le_pow`,
`Hironaka/Algebra/Derivative/Basic.lean`); `⟸` through the coordinates on the stalk with `k`-linear
derivations (`exists_regularCoords_stalk`,
`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`): `c.Dʳ(I_x) ⊆ Dʳ(I_x) ⊆ 𝔪^(m−r)` and the
local cosupport lemma `I_x ⊆ 𝔪ᵐ ⟺ c.Dʳ(I_x) ⊆ 𝔪^(m−r)` (`le_maximalIdeal_pow_iff_Dpow_le`,
`Hironaka/Algebra/Order/Cosupport.lean`). The spanning of the derivations by the `∂ᵢ` is not used,
so the argument holds at non-closed points, where the coordinate derivations are fewer than the
generators of `Der`.

Used for the cosupport of marked ideals and maximal contact
(`Hironaka/Resolution/Algebraic/MaximalContact/Basic.lean`,
`Hironaka/Resolution/Algebraic/Balanced/Order.lean`,
`Hironaka/Scheme/IdealSheaf/Order/Semicontinuity.lean`,
`Hironaka/Scheme/IdealSheaf/Order/AffineSpace.lean`,
`Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Sequence.lean`) and for functoriality
(`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/BaseChangeParameters.lean`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing

universe u

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- [Kol07, Lemma 74 (3)]; [Wlo05, Lemma 2.6.2]: on a smooth `k`-scheme in characteristic zero,
`ord_x I ≥ m ⟺ ord_x Dʳ(I) ≥ m − r` for `r < m`. -/
theorem le_ord_iff_le_ord_derivativeIter (I : X.IdealSheafData) (x : X) {r m : ℕ} (h : r < m) :
    (m : ℕ∞) ≤ I.ord x ↔ ((m - r : ℕ) : ℕ∞) ≤ (I.derivativeIter f r).ord x := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  let _ := f.stalkAlgebra x
  let _ := f.stalkAlgebraRat x
  have hreg := @isRegularLocalRing_stalk k _ X f hs x
  rw [le_ord_iff, le_ord_iff, stalkIdeal_derivativeIter]
  constructor
  · intro hJ
    have hJ' : I.stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) ^ ((m - r) + r) := by
      rwa [Nat.sub_add_cancel h.le]
    exact Ideal.derivativeIter_le_pow hJ'
  · intro hD
    obtain ⟨m', c, hk⟩ := exists_regularCoords_stalk f n x
    exact (c.le_maximalIdeal_pow_iff_Dpow_le (I.stalkIdeal x) h).mpr
      ((Ideal.Dpow_le_derivativeIter c hk r _).trans hD)

include n in
/-- [Wlo05, Lemma 2.6.2], `supp(I, μ) = V(D^{μ−1}(I))`: `{x : ord_x I ≥ m} = V(D^{m−1} I)` for
`m ≥ 1`, the sheaf form of the cosupport transfer. -/
theorem le_ord_iff_mem_support_derivativeIter (I : X.IdealSheafData) (x : X) {m : ℕ}
    (hm : 1 ≤ m) :
    (m : ℕ∞) ≤ I.ord x ↔ x ∈ (I.derivativeIter f (m - 1)).support := by
  rw [le_ord_iff_le_ord_derivativeIter f n I x (Nat.sub_lt hm one_pos),
    show m - (m - 1) = 1 by omega, Nat.cast_one, one_le_ord_iff]

end AlgebraicGeometry.Scheme.IdealSheafData
