import DeJongAlterations.Algebra.NodeFittingModuleBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Faithfully flat detection of ENTIRE original intrinsic module Fitting ideals -/

noncomputable section

open scoped TensorProduct

namespace DeJongAlterations.Algebra.NodeFittingModule

variable {R : Type*} [CommRing R] (C : Type*) [CommRing C] [Algebra R C]
  [Module.FaithfullyFlat R C] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.FinitePresentation R M] [Module.FinitePresentation R N]

/-- A genuine actual faithfully flat tensor-module equivalence detects the ENTIRE original Fitting ideals. -/
theorem fittingIdeal_eq_of_faithfullyFlat_baseChange (e : C ⊗[R] M ≃ₗ[C] C ⊗[R] N) (i : ℕ) :
    fittingIdeal (R := R) (M := M) i = fittingIdeal (R := R) (M := N) i := by
  apply Ideal.map_injective_of_faithfullyFlat (B := C)
  exact (fittingIdeal_baseChange (R := R) (M := M) C i).trans
    ((fittingIdeal_equiv e i).trans (fittingIdeal_baseChange (R := R) (M := N) C i).symm)

end DeJongAlterations.Algebra.NodeFittingModule
