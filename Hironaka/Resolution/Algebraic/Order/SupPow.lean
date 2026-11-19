/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.Order
import Hironaka.Resolution.Algebraic.Kol07.Tuning
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The order of a sum of powers

The second step of the proof of [Kol07, Theorem 107] ([Kol07, 111]): "the following simple
observation reduces the general case to a single ideal", `ord_Z J₁ ≥ s` and `ord_Z J₂ ≥ m` iff
`ord_Z (J₁^m + J₂^s) ≥ ms`. The order of a sum is the minimum ([Kol07, Definition 59 (4)],
`IsLocalRing.ord_sup` of `Hironaka/Algebra/Local/Order.lean` at the stalk) and the order of a power
is the multiple ([Kol07, Definition 59 (3)], `ord_pow` of
`Hironaka/Resolution/Algebraic/Kol07/Tuning.lean` on a smooth scheme, where the stalks are regular
local rings containing `ℚ`), so `ord_x (J₁^m + J₂^s) = min (m · ord_x J₁, s · ord_x J₂)`
and, for `m, s ≥ 1`, this is `≥ ms` iff both `ord_x J₁ ≥ s` and `ord_x J₂ ≥ m`. Hence
`cosupp(J₁^m + J₂^s, ms) = cosupp(J₁, s) ∩ cosupp(J₂, m)`, and the same along a centre `Z` (at its
generic points, Kollár's `ord_Z`).

* `stalkIdeal_sup`, `ord_sup_eq_min`: the sum at the stalk and its order (the sum of ideal sheaves
  is their supremum).
* `le_ord_pow_sup_pow_iff`: the observation at a point; `setOf_le_ord_pow_sup_pow`: its cosupport
  form; `leOrdAlong_pow_sup_pow_iff`: its form along a closed set (`LeOrdAlong`).

Used in the second step of the proof of Theorem 107
(`Hironaka/Resolution/Algebraic/Kol07/MarkedSupPow.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step2Separation.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothLoop.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The stalk of a sum of ideal sheaves is the sum of the stalks: an identity of stalks on any
scheme, with no smoothness and no structure morphism. -/
theorem stalkIdeal_sup (I J : X.IdealSheafData) (x : X) :
    (I ⊔ J).stalkIdeal x = I.stalkIdeal x ⊔ J.stalkIdeal x := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hx, stalkIdeal_eq_map_germ I U hx, stalkIdeal_eq_map_germ J U hx,
    ideal_sup, Pi.sup_apply, Ideal.map_sup]

/-- [Kol07, Definition 59 (4)]: the order of a sum is the minimum of the orders. `ord` is the
order in the local ring `𝒪_{X,x}`, and in any local ring the order of a sum of ideals is the
minimum (`IsLocalRing.ord_sup`); no smoothness enters — it is the power `ord_pow` that needs the
regular stalks. -/
theorem ord_sup_eq_min (I J : X.IdealSheafData) (x : X) :
    (I ⊔ J).ord x = min (I.ord x) (J.ord x) := by
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal, stalkIdeal_sup]
  exact IsLocalRing.ord_sup _ _

section Smooth

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include f n in
/-- Kollár's observation in the proof of Theorem 107 ([Kol07, 111]), `ord_Z J₁ ≥ s` and
`ord_Z J₂ ≥ m` iff `ord_Z (J₁^m + J₂^s) ≥ ms`, at a point: for `m, s ≥ 1`,
`ms ≤ ord_x (J₁^m + J₂^s)` iff `s ≤ ord_x J₁` and `m ≤ ord_x J₂` — the order of the sum is the
minimum, the order of a power is the multiple ([Kol07, Definition 59 (3), (4)]), and `m`, `s`
cancel in `ℕ∞`. -/
theorem le_ord_pow_sup_pow_iff (J₁ J₂ : X.IdealSheafData) {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s)
    (x : X) :
    ((m * s : ℕ) : ℕ∞) ≤ (J₁ ^ m ⊔ J₂ ^ s).ord x ↔
      (s : ℕ∞) ≤ J₁.ord x ∧ (m : ℕ∞) ≤ J₂.ord x := by
  rw [ord_sup_eq_min, Hironaka.Sequence.ord_pow f n J₁ m hm x,
    Hironaka.Sequence.ord_pow f n J₂ s hs x, le_min_iff, Nat.cast_mul]
  have hm0 : (m : ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  have hs0 : (s : ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hs
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(ENat.mul_le_mul_left_iff hm0 (ENat.natCast_ne_top m)).mp h1, ?_⟩
    rw [mul_comm (m : ℕ∞) (s : ℕ∞)] at h2
    exact (ENat.mul_le_mul_left_iff hs0 (ENat.natCast_ne_top s)).mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨mul_le_mul_of_nonneg_left h1 zero_le, ?_⟩
    rw [mul_comm (m : ℕ∞) (s : ℕ∞)]
    exact mul_le_mul_of_nonneg_left h2 zero_le

include f n in
/-- The cosupport of the sum of powers at the mark `ms` is the intersection of the two cosupports,
for `m, s ≥ 1`: in the use of [Kol07, 111],
`cosupp(N(I)^m + I^s, ms) = cosupp(N(I), s) ∩ cosupp(I, m)`. -/
theorem setOf_le_ord_pow_sup_pow (J₁ J₂ : X.IdealSheafData) {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    {x | ((m * s : ℕ) : ℕ∞) ≤ (J₁ ^ m ⊔ J₂ ^ s).ord x} =
      {x | (s : ℕ∞) ≤ J₁.ord x} ∩ {x | (m : ℕ∞) ≤ J₂.ord x} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact le_ord_pow_sup_pow_iff f n J₁ J₂ hm hs x

include f n in
/-- Kollár's observation along a closed set `Z` (Kollár's `ord_Z`, the order at the generic
points; [Kol07, 111]): `ord_Z (J₁^m + J₂^s) ≥ ms` iff `ord_Z J₁ ≥ s` and `ord_Z J₂ ≥ m`, for
`m, s ≥ 1`. -/
theorem leOrdAlong_pow_sup_pow_iff (J₁ J₂ : X.IdealSheafData) (Z : Closeds X) {m s : ℕ}
    (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (J₁ ^ m ⊔ J₂ ^ s).LeOrdAlong Z ((m * s : ℕ) : ℕ∞) ↔
      J₁.LeOrdAlong Z (s : ℕ∞) ∧ J₂.LeOrdAlong Z (m : ℕ∞) := by
  constructor
  · intro h
    exact ⟨fun η hη => ((le_ord_pow_sup_pow_iff f n J₁ J₂ hm hs η).mp (h η hη)).1,
      fun η hη => ((le_ord_pow_sup_pow_iff f n J₁ J₂ hm hs η).mp (h η hη)).2⟩
  · rintro ⟨h1, h2⟩ η hη
    exact (le_ord_pow_sup_pow_iff f n J₁ J₂ hm hs η).mpr ⟨h1 η hη, h2 η hη⟩

end Smooth

end AlgebraicGeometry.Scheme.IdealSheafData
