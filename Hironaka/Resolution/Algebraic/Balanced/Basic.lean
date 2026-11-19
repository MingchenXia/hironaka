/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# D-balanced ideals and ideal sheaves

Kollár's D-balanced ideals [Kol07, Definition 83; also 52]: an ideal `I` with `m = max-ord I` is
D-balanced if "`(Dⁱ I)^m ⊂ I^{m−i}` for all `i < m`", where `D` is the derivative ideal
[Kol07, Definition 73]. Two forms of the definition, both with the mark `m` an explicit parameter
(Kollár takes `m = max-ord I`; the statements that need that side condition carry it):

* `Ideal.IsDBalanced k J m` for an ideal `J` of a `k`-algebra `A`, with the intrinsic derivative
  ideals `Ideal.derivativeIter k i J` of `Hironaka.Derivative` (at a regular local ring with
  coordinates whose derivations span, this is `RegularCoords.IsDBalanced` of `Hironaka.Local` by
  `Ideal.derivativeIter_eq_Dpow`);
* `AlgebraicGeometry.Scheme.IdealSheafData.IsDBalanced f I m` for an ideal sheaf `I` on a `k`-scheme
  `f : X ⟶ Spec k`, with the derivative ideal sheaves `derivativeIter f i I`.

D-balanced ideals are the ideals whose order reduction can be pushed to a hypersurface of maximal
contact [Kol07, Theorem 84]; the tuned ideal `W_s(I)` of `Hironaka.Tuning` is D-balanced
[Kol07, Corollary 101], and `Hironaka.Resolution.Algebraic.Balanced.Order` proves the order
dichotomy of D-balanced ideal sheaves.
-/

@[expose] public section

universe u

namespace Ideal

variable (k : Type*) {A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Kollár's D-balanced ideals [Kol07, Definition 83; 52], ring form: `J` is **D-balanced with
respect to `m`** if `(Dⁱ J)^m ≤ J^{m−i}` for every `i < m`, with `D` the intrinsic derivative ideal
`Ideal.derivativeIter`. -/
def IsDBalanced (J : Ideal A) (m : ℕ) : Prop :=
  ∀ i < m, derivativeIter k i J ^ m ≤ J ^ (m - i)

variable {k}

theorem isDBalanced_iff (J : Ideal A) (m : ℕ) :
    IsDBalanced k J m ↔ ∀ i < m, derivativeIter k i J ^ m ≤ J ^ (m - i) := Iff.rfl

/-- The unit ideal is D-balanced with respect to every mark. -/
theorem isDBalanced_top (m : ℕ) : IsDBalanced k (⊤ : Ideal A) m := fun i _ => by
  rw [Ideal.top_pow]; exact le_top

/-- Every ideal is D-balanced with respect to the mark `0` (there is no `i < 0`). -/
theorem isDBalanced_zero (J : Ideal A) : IsDBalanced k J 0 := fun _ h => (Nat.not_lt_zero _ h).elim

end Ideal

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Kollár's D-balanced ideals [Kol07, Definition 83; 52], sheaf form: the ideal sheaf `I` on the
`k`-scheme `f : X ⟶ Spec k` is **D-balanced with respect to `m`** if `(Dⁱ I)^m ≤ I^{m−i}` for every
`i < m`, with `D` the derivative ideal sheaf `derivativeIter f`. Kollár's side condition
`m = max-ord I` is carried by the statements that use it. -/
def IsDBalanced (I : X.IdealSheafData) (m : ℕ) : Prop :=
  ∀ i < m, derivativeIter f i I ^ m ≤ I ^ (m - i)

theorem isDBalanced_iff (I : X.IdealSheafData) (m : ℕ) :
    IsDBalanced f I m ↔ ∀ i < m, derivativeIter f i I ^ m ≤ I ^ (m - i) := Iff.rfl

/-- The unit ideal sheaf is D-balanced with respect to every mark. -/
theorem isDBalanced_top (m : ℕ) : IsDBalanced f (⊤ : X.IdealSheafData) m := fun i _ => by
  rw [show (⊤ : X.IdealSheafData) ^ (m - i) = ⊤ from one_pow (m - i)]; exact le_top

/-- Every ideal sheaf is D-balanced with respect to the mark `0`. -/
theorem isDBalanced_zero (I : X.IdealSheafData) : IsDBalanced f I 0 :=
  fun _ h => (Nat.not_lt_zero _ h).elim

end AlgebraicGeometry.Scheme.IdealSheafData
