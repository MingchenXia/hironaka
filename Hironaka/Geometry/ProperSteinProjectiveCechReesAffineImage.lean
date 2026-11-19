/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesFamily
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
Adapted closed native proof from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesFormalAffine.lean`,
SHA256 e0d6a785dfa9dc1dc6b954f259aee6012253b086d9943b8b8e7ae8dc1a8f76f3.
Only native Mathlib and owned actual original Rees helper modules are imported.
The geometric finite cohomology/formal-functions comparison remains separate.


# Actual affine rings of the schematic Rees family

The genuine polynomial tensor comparison identifies the affine image ring
with the Rees algebra of the actual extended ideal. No flatness or supplied
image-ring comparison is assumed.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Polynomial
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesAffineImage

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual polynomial tensor algebra isomorphism, constructed through
the genuine one-variable polynomial universal equivalences. -/
def polynomialTensorEquiv : A ⊗[R] R[X] ≃ₐ[A] A[X] :=
  (Algebra.TensorProduct.congr (.refl : A ≃ₐ[A] A)
    (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
    ((MvPolynomial.algebraTensorAlgEquiv R A).trans (MvPolynomial.uniqueAlgEquiv A Unit))

/-- Every tensor polynomial keeps the ENTIRE coefficient polynomial. -/
theorem polynomialTensorEquiv_tmul (a : A) (p : R[X]) :
    polynomialTensorEquiv R A (a ⊗ₜ[R] p) =
      Polynomial.C a * p.map (algebraMap R A) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, hp, hq, Polynomial.map_add, mul_add]
  | monomial n r =>
    simp [polynomialTensorEquiv, Algebra.TensorProduct.congr_apply,
      MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.uniqueAlgEquiv_symm_apply,
      Polynomial.eval₂_monomial, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.smul_monomial, smul_eq_mul]

variable (I : Ideal R)

/-- The genuine tensor extension of the original Rees inclusion into the
polynomial ring; this is the actual affine polynomial-to-Rees scheme map. -/
def tensorInclusion : A ⊗[R] reesAlgebra I →ₐ[A] A ⊗[R] R[X] :=
  Algebra.TensorProduct.map (AlgHom.id A A) (reesAlgebra I).val

/-- The WHOLE actual tensor inclusion, transported by the genuine polynomial
tensor isomorphism, factors through exactly the actual extended Rees algebra. -/
theorem polynomialTensorEquiv_comp_inclusion :
    (polynomialTensorEquiv R A).toAlgHom.comp (tensorInclusion R A I) =
      (reesAlgebra (I.map (algebraMap R A))).val.comp
        (ReesBaseChange.baseChangeMap I) := by
  apply Algebra.TensorProduct.ext'
  intro a p
  change polynomialTensorEquiv R A (a ⊗ₜ[R] (p : R[X])) =
    (ReesBaseChange.baseChangeMap I (a ⊗ₜ[R] p) : A[X])
  rw [polynomialTensorEquiv_tmul, ReesBaseChange.baseChangeMap_tmul_val]

/-- The genuine tensor map defining the affine schematic image has exactly
the kernel of the constructed surjection onto the extended ideal Rees ring. -/
theorem tensorInclusion_ker :
    RingHom.ker (tensorInclusion R A I).toRingHom =
      RingHom.ker (ReesBaseChange.baseChangeMap (A := A) I).toRingHom := by
  ext x
  change tensorInclusion R A I x = 0 ↔ ReesBaseChange.baseChangeMap I x = 0
  rw [← map_eq_zero_iff (polynomialTensorEquiv R A) (polynomialTensorEquiv R A).injective]
  have hx := DFunLike.congr_fun (polynomialTensorEquiv_comp_inclusion R A I) x
  change polynomialTensorEquiv R A (tensorInclusion R A I x) =
    (ReesBaseChange.baseChangeMap I x : A[X]) at hx
  rw [hx]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    rw [h]
    rfl

/-- The actual affine schematic-image quotient is the whole extended ideal
Rees algebra, as an algebra over the actual original affine coefficients. -/
def affineImageEquiv :
    ((A ⊗[R] reesAlgebra I) ⧸ RingHom.ker (tensorInclusion R A I).toRingHom) ≃ₐ[A]
      reesAlgebra (I.map (algebraMap R A)) :=
  (Ideal.quotientEquivAlgOfEq A (tensorInclusion_ker R A I)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (ReesBaseChange.baseChangeMap_surjective I))

/-- Every whole original tensor section is retained by the actual image
quotient comparison. -/
theorem affineImageEquiv_mk (x : A ⊗[R] reesAlgebra I) :
    affineImageEquiv R A I (Ideal.Quotient.mk _ x) =
      ReesBaseChange.baseChangeMap I x := by
  change Ideal.quotientKerAlgEquivOfSurjective
      (ReesBaseChange.baseChangeMap_surjective I)
      (Ideal.quotientEquivAlgOfEq A (tensorInclusion_ker R A I) (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk
    (ReesBaseChange.baseChangeMap_surjective I) x

/-- Equality of actual affine ring kernels gives equality of the actual
scheme-theoretic image ideal sheaves, with no reducedness hypotheses. -/
theorem specMap_ker_eq_of_ringKer_eq
    {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (φ : B →+* C) (ψ : B →+* D) (hker : RingHom.ker φ = RingHom.ker ψ) :
    (Spec.map (CommRingCat.ofHom φ)).ker = (Spec.map (CommRingCat.ofHom ψ)).ker := by
  rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
  congr 1
  ext s
  change (Spec.map (CommRingCat.ofHom φ)).appTop s = 0 ↔
    (Spec.map (CommRingCat.ofHom ψ)).appTop s = 0
  have hφ := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) s
  have hψ := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)) s
  change (Scheme.ΓSpecIso (.of C)).hom
    ((Spec.map (CommRingCat.ofHom φ)).appTop s) =
      φ ((Scheme.ΓSpecIso (.of B)).hom s) at hφ
  change (Scheme.ΓSpecIso (.of D)).hom
    ((Spec.map (CommRingCat.ofHom ψ)).appTop s) =
      ψ ((Scheme.ΓSpecIso (.of B)).hom s) at hψ
  have hboth : φ ((Scheme.ΓSpecIso (.of B)).hom s) = 0 ↔
      ψ ((Scheme.ΓSpecIso (.of B)).hom s) = 0 := by
    change (Scheme.ΓSpecIso (.of B)).hom s ∈ RingHom.ker φ ↔
      (Scheme.ΓSpecIso (.of B)).hom s ∈ RingHom.ker ψ
    rw [hker]
  rw [← map_eq_zero_iff (Scheme.ΓSpecIso (.of C)).hom.hom
    (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.injective, hφ]
  rw [← map_eq_zero_iff (Scheme.ΓSpecIso (.of D)).hom.hom
    (Scheme.ΓSpecIso (.of D)).commRingCatIsoToRingEquiv.injective, hψ]
  exact hboth

/-- The actual scheme-theoretic image of the genuine polynomial tensor
map is the affine scheme of the whole extended Rees algebra. -/
def affineImageSchemeIso :
    (Spec.map (CommRingCat.ofHom (tensorInclusion R A I).toRingHom)).image ≅
      Spec (.of (reesAlgebra (I.map (algebraMap R A)))) := by
  let p := Spec.map (CommRingCat.ofHom (tensorInclusion R A I).toRingHom)
  let j := Spec.map (CommRingCat.ofHom (ReesBaseChange.baseChangeMap (A := A) I).toRingHom)
  have : IsClosedImmersion j := ReesBaseChange.spec_baseChangeMap_isClosedImmersion I
  have hker : j.ker = p.imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (specMap_ker_eq_of_ringKer_eq _ _ (tensorInclusion_ker R A I)).symm
  have := IsClosedImmersion.isIso_lift j p.imageι hker
  exact asIso (IsClosedImmersion.lift j p.imageι hker.le)

/-- The actual affine image isomorphism retains the WHOLE original closed
immersion into the actual tensor coefficient spectrum. -/
theorem affineImageSchemeIso_comp_immersion :
    (affineImageSchemeIso R A I).hom ≫
        Spec.map (CommRingCat.ofHom (ReesBaseChange.baseChangeMap (A := A) I).toRingHom) =
      (Spec.map (CommRingCat.ofHom (tensorInclusion R A I).toRingHom)).imageι := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (ReesBaseChange.baseChangeMap (A := A) I).toRingHom)) :=
    ReesBaseChange.spec_baseChangeMap_isClosedImmersion I
  exact IsClosedImmersion.lift_fac _ _ _

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesAffineImage
