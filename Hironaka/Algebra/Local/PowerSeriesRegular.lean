/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Hironaka.Algebra.Local.PowerSeries
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# `K⟦X₁, …, Xₙ⟧` is a regular local ring of dimension `n`

Kollár identifies the completion of a smooth stalk with `k(p)⟦x₁, …, xₙ⟧` [Kol07, Definition 55];
the library needs the target to be a regular local ring of dimension `n`, a fact Mathlib does
not state.

**The argument.**  Two bounds meet:

* `spanFinrank 𝔪 ≤ n`, because `𝔪 = ⟨X₁, …, Xₙ⟧` (`MvPowerSeries.maximalIdeal_eq_span_range_X`)
  is spanned by the `n` variables (`Submodule.spanFinrank_span_le_ncard_of_finite`);
* `n ≤ dim K⟦X₁, …, Xₙ⟧`, by induction on `n` through `K⟦X₁, …, X_{n+1}⟧ ≅ K⟦X₁, …, Xₙ⟧⟦X⟧`
  (`MvPowerSeries.finSuccEquiv`) and `dim R + 1 ≤ dim R⟦X⟧`
  (`ringKrullDim_succ_le_ringKrullDim_powerseries`: `X` is a nonzerodivisor with `R⟦X⟧/(X) ≅ R`).

Since `K⟦X⟧` is Noetherian (`MvPowerSeries.isNoetherianRing`) and local, Krull's height theorem
gives `dim ≤ spanFinrank 𝔪` for free (`ringKrullDim_le_spanFinrank_maximalIdeal`),
so `spanFinrank 𝔪 ≤ n ≤ dim ≤ spanFinrank 𝔪`: the ring is regular
(`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`) of dimension exactly `n`.  No chain of
primes needs to be exhibited, and no characteristic hypothesis enters.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

variable (K : Type*) [Field K]

/-- `n ≤ dim K⟦X₁, …, Xₙ⟧`, by induction through `K⟦X₁, …, X_{n+1}⟧ ≅ K⟦X₁, …, Xₙ⟧⟦X⟧` and
`dim R + 1 ≤ dim R⟦X⟧`. -/
theorem natCast_le_ringKrullDim_mvPowerSeries (n : ℕ) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin n) K) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv K n).toRingEquiv, Nat.cast_succ]
    exact le_trans (add_le_add ih le_rfl) ringKrullDim_succ_le_ringKrullDim_powerseries

/-- `𝔪 = ⟨X₁, …, Xₙ⟧` needs at most `n` generators. -/
theorem spanFinrank_maximalIdeal_mvPowerSeries_le (n : ℕ) :
    (maximalIdeal (MvPowerSeries (Fin n) K)).spanFinrank ≤ n := by
  rw [maximalIdeal_eq_span_range_X (Fin n) K]
  refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)) ?_
  rw [← Set.image_univ]
  exact le_trans (Set.ncard_image_le Set.finite_univ)
    (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin])

/-- `K⟦X₁, …, Xₙ⟧` is a regular local ring (the target of the identification of
[Kol07, Definition 55]). -/
theorem isRegularLocalRing_mvPowerSeries (n : ℕ) : IsRegularLocalRing (MvPowerSeries (Fin n) K) :=
  IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (MvPowerSeries (Fin n) K)
    (le_trans (Nat.cast_le.mpr (spanFinrank_maximalIdeal_mvPowerSeries_le K n))
      (natCast_le_ringKrullDim_mvPowerSeries K n))

/-- The regularity of `K⟦X₁, …, Xₙ⟧` as an instance, so that constructions such as
`RegularCoords.mvPowerSeries` find it by instance search. -/
instance instIsRegularLocalRingMvPowerSeries (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) K) :=
  isRegularLocalRing_mvPowerSeries K n

/-- `dim K⟦X₁, …, Xₙ⟧ = n`. -/
theorem ringKrullDim_mvPowerSeries (n : ℕ) : ringKrullDim (MvPowerSeries (Fin n) K) = n := by
  have := isRegularLocalRing_mvPowerSeries K n
  refine le_antisymm ?_ (natCast_le_ringKrullDim_mvPowerSeries K n)
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
  exact Nat.cast_le.mpr (spanFinrank_maximalIdeal_mvPowerSeries_le K n)

/-- The coordinate structure `RegularCoords.mvPowerSeries` on `K⟦X₁, …, Xₙ⟧` with its hypotheses
discharged. -/
noncomputable abbrev RegularCoords.stdMvPowerSeries [CharZero K] (n : ℕ) :
    RegularCoords (MvPowerSeries (Fin n) K) n :=
  RegularCoords.mvPowerSeries K n (maximalIdeal_eq_span_range_X (Fin n) K)
    (ringKrullDim_mvPowerSeries K n).symm

end IsLocalRing
