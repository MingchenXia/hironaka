/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Generalities on a marked triple and one smooth blow-up

Four facts about a marked triple `(X, I, m, E)` [Kol07, Notation 64] and one smooth blow-up that
involve no monomial part: the power of the exceptional ideal at the exceptional order divides the
total transform (`pow_exceptionalOrderAlong_dvd`, the multiplicity of `π^* I` along the exceptional
divisor in [Kol07, 58]); on a triple's scheme the product of nonvanishing ideal sheaves is
nonvanishing (`isNonzeroEverywhere_mul`); a smooth blow-up of order `≥ m` for `(X, I, m, E)` is a
smooth blow-up sequence of order `≥ m` of length one (`isOrderGeSeq_single`,
[Kol07, Definition 65, (1′)–(2′)]); the exceptional divisor is the last member of the total
transform (`support_exceptionalDivisor_le`). They are used by the marked order reduction functor
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/`), whose namespace `Hironaka.BMO` they share.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData Hironaka
  Scheme.BlowUpSequence

namespace AlgebraicGeometry

/-- The power of the exceptional ideal at the exceptional order divides the total transform: the
set `{c | F^c ∣ π^* J}` is either all of `ℕ` or bounded, and a bounded nonempty set of naturals
contains its supremum. -/
theorem pow_exceptionalOrderAlong_dvd {B X : Scheme.{u}} (π : B ⟶ X) (F : B.IdealSheafData)
    (J : X.IdealSheafData) : F ^ exceptionalOrderAlong π F J ∣ J.comap π := by
  by_cases h : ∀ c, F ^ c ∣ J.comap π
  · exact h _
  · rw [not_forall] at h
    obtain ⟨c, hc⟩ := h
    have hbdd : BddAbove {d : ℕ | F ^ d ∣ J.comap π} := ⟨c, fun d hd => by
      by_contra hlt
      exact hc ((pow_dvd_pow F (not_le.mp hlt).le).trans hd)⟩
    exact Nat.sSup_mem ⟨0, by change F ^ 0 ∣ J.comap π; rw [pow_zero]; exact one_dvd _⟩ hbdd

section Auxiliary

variable {k : Type u} [Field k] (T' : Triple k)

/-- On a triple's scheme the product of two nonvanishing ideal sheaves is nonvanishing (the stalks
are domains). -/
theorem isNonzeroEverywhere_mul {I J : T'.X.left.IdealSheafData} (hI : IsNonzeroEverywhere I)
    (hJ : IsNonzeroEverywhere J) : IsNonzeroEverywhere (I * J) := fun x h => by
  have := isRegularLocalRing_stalk (T'.X.left ↘ Spec (.of k)) x
  change (I * J).stalkIdeal x = ⊥ at h
  rw [stalkIdeal_mul, Ideal.mul_eq_bot] at h
  rcases h with h | h
  · exact hI x h
  · exact hJ x h

end Auxiliary

section Transform

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k) (Z : T.X.left.IdealSheafData)
  (hZ : T.IsOrderGeBlowUp Z)

include hZ

omit [CharZero k] in
/-- Conditions (1′)–(2′) of [Kol07, Definition 65] as the one-step sequence: a smooth blow-up of
order `≥ m` for `(X, I, m, E)` is a smooth blow-up sequence of order `≥ m` of length one. -/
theorem isOrderGeSeq_single :
    (cons T.X.left Z (nil _)).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
  (isOrderGeSeq_cons_iff _ _ _ _ _ _).mpr
    ⟨⟨hZ.1, hZ.2.1, hZ.2.2⟩, isOrderGeSeq_nil _ _ _ _⟩

omit [CharZero k] hZ in
/-- The exceptional divisor is the last member of the total transform [Kol07, Definition 65]. -/
theorem support_exceptionalDivisor_le :
    Z.exceptionalDivisor.support ≤ (T.E.totalTransform Z).support :=
  le_iSup (fun j => ((T.E.totalTransform Z).component j).support) (toLex (Sum.inr PUnit.unit))

end Transform

end AlgebraicGeometry
