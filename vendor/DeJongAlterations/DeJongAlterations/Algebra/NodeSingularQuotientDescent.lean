import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Descent of the actual coefficient-valued quotient

The quotient after a faithfully flat algebra extension is identified with the
SAME coefficient algebra. Its original quotient then has an actual algebra
equivalence with those coefficients, without residue separability or localness.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeSingularQuotientDescent

variable {K R C : Type*} [CommRing K] [CommRing R] [CommRing C]
  [Algebra K R] [Algebra K C] [Algebra R C] [IsScalarTower K R C]
  (J : Ideal R) (e : (C ⧸ J.map (algebraMap R C)) ≃ₐ[K] K)

/-- The original coefficient-preserving composite through the actual quotient. -/
def quotientRetraction : R →ₐ[K] K :=
  e.toAlgHom.comp ((Ideal.Quotient.mkₐ K _).comp (IsScalarTower.toAlgHom K R C))

@[simp]
theorem quotientRetraction_coefficient (k : K) :
    quotientRetraction J e (algebraMap K R k) = k :=
  (quotientRetraction J e).commutes k

theorem quotientRetraction_surjective : Function.Surjective (quotientRetraction J e) :=
  fun k ↦ ⟨algebraMap K R k, quotientRetraction_coefficient J e k⟩

/-- Faithful flatness reflects the ENTIRE original ideal, rather than only its support. -/
theorem quotientRetraction_ker [Module.FaithfullyFlat R C] :
    RingHom.ker (quotientRetraction J e) = J := by
  ext r
  change e (Ideal.Quotient.mk _ (algebraMap R C r)) = 0 ↔ r ∈ J
  rw [← map_zero e, e.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
  change r ∈ (J.map (algebraMap R C)).comap (algebraMap R C) ↔ r ∈ J
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- The actual original quotient descends with its SAME original coefficient action. -/
def quotientDescentEquiv [Module.FaithfullyFlat R C] : (R ⧸ J) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (quotientRetraction_ker J e).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (quotientRetraction_surjective J e))

@[simp]
theorem quotientDescentEquiv_mk [Module.FaithfullyFlat R C] (r : R) :
    quotientDescentEquiv J e (Ideal.Quotient.mk J r) =
      e (Ideal.Quotient.mk _ (algebraMap R C r)) := by
  simp only [quotientDescentEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  rfl

@[simp]
theorem quotientDescentEquiv_coefficient [Module.FaithfullyFlat R C] (k : K) :
    quotientDescentEquiv J e (algebraMap K (R ⧸ J) k) = k :=
  (quotientDescentEquiv J e).commutes k

end DeJongAlterations.Algebra.NodeSingularQuotientDescent
