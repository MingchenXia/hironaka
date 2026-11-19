import Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Nilpotent parameter ideal for finite local complex algebras -/
set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10FiniteLocalAlgebra

/-- A finite-dimensional local complex algebra has nilpotent maximal ideal.
  This is the concrete Artinian-parameter input in Frisch's argument. -/
theorem maximalIdeal_nilpotent {A : Type*} [CommRing A] [Algebra ℂ A]
    [Module.Finite ℂ A] [IsLocalRing A] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ n = ⊥ := by
  let : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  have h : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  exact h

end Hironaka.Analytic.Unibranch.HironakaG10FiniteLocalAlgebra
