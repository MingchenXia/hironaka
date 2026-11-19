import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Pi

/-!
# Actual original quotient columns contain a local finite basis

Native finite presentation and flatness suffice; neither a basis nor a
pivot condition is assumed. Every selected original column is retained.
-/

noncomputable section

open Module

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  [Module.FinitePresentation A M] [Module.Flat A M]
  {E : Type w} [Fintype E] [DecidableEq E]

/-- A SAME actual original quotient has a finite local basis among its ORIGINAL columns, with the selected original indices an actual embedding. -/
theorem originalLocalQuotient_exists_columnBasis (q : (E → A) →ₗ[A] M)
    (hq : Function.Surjective q) :
    ∃ (I : Type w) (_ : Finite I) (a : I ↪ E) (b : Basis I A M),
      ∀ i, b i = q (Pi.single (a i) (1 : A)) := by
  let v : E → M := fun i => q (Pi.single i (1 : A))
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    have h := congrArg (Submodule.map q) (Pi.basisFun A E).span_eq
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Pi.basisFun_apply, Submodule.map_top, LinearMap.range_eq_top.mpr hq, v] using h
  obtain ⟨I, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  have ha : Function.Injective a := by
    intro i j h
    apply b.injective
    rw [hb i, hb j, h]
  exact ⟨I, Module.Finite.finite_basis b, ⟨a, ha⟩, b, hb⟩

end Hironaka.Algebra.PluckerQuotTransition
