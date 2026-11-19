import Hironaka.Algebra.FiniteMorphismFlattening
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AsSubring

/-!
# The original chart tensor map is actual coefficient localization

The fraction field is the localization of every fraction subalgebra at
the original base denominators. Base change and tensor cancellation
therefore identify the actual pure-transform map as the actual generic
coefficient localization, without reducedness assumptions on the algebra.
-/

noncomputable section

open scoped TensorProduct

namespace Hironaka.Algebra.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- A fraction subalgebra has the original fraction field after inverting original base denominators. -/
instance fractionSubalgebra_isLocalization (S : Subalgebra R (FractionRing R)) :
    IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (FractionRing R) where
  map_units := by
    rintro ⟨_, r, hr, rfl⟩
    rw [← IsScalarTower.algebraMap_apply R S (FractionRing R)]
    exact IsLocalization.map_units (FractionRing R) ⟨r, hr⟩
  surj x := by
    obtain ⟨⟨a, d⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) x
    refine ⟨⟨algebraMap R S a, ⟨algebraMap R S d, d, d.property, rfl⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply R S (FractionRing R)] using h
  exists_of_eq h := by
    have heq := (IsFractionRing.injective S (FractionRing R)) h
    exact ⟨1, by simpa using heq⟩

/-- The actual coefficient fraction square is a native algebra pushout. -/
theorem fractionSubalgebra_isPushout (S : Subalgebra R (FractionRing R)) :
    Algebra.IsPushout R S (FractionRing R) (FractionRing R) :=
  Algebra.isPushout_of_isLocalization (nonZeroDivisors R) (FractionRing R) S (FractionRing R)

/-- The tensor cancellation isomorphism retains the literal original generic tensor images. -/
def chartGenericTensorEquiv (S : Subalgebra R (FractionRing R)) :
    FractionRing R ⊗[S] (S ⊗[R] A) ≃ₐ[FractionRing R] FractionRing R ⊗[R] A :=
  Algebra.TensorProduct.cancelBaseChange R S (FractionRing R) (FractionRing R) A

omit [IsDomain R] in
/-- The actual canonical chart algebra map is the original generic-localization map through cancellation. -/
theorem chartGenericTensorEquiv_comp_includeRight (S : Subalgebra R (FractionRing R)) :
    ((chartGenericTensorEquiv R A S).toAlgHom.restrictScalars S).comp
      (Algebra.TensorProduct.includeRight : S ⊗[R] A →ₐ[S]
        FractionRing R ⊗[S] (S ⊗[R] A)) = tensorAlgMap R A S := by
  ext a
  simp [chartGenericTensorEquiv, tensorAlgMap, Algebra.smul_def]

end Hironaka.Algebra.FiniteMorphismFlattening
