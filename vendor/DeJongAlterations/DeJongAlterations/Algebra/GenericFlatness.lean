/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import DeJongAlterations.Algebra.GenericFreeness
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient


/-!
# Generic flatness of polynomial quotients

The quotient base-change equivalence is extracted from the characteristic-free prefix of
`TranscendentalNakamaye/Pending/HironakaRelativeNormalCoefficientPolynomialBaseChange.lean`,
source SHA-256 `3a6c74feabc336672921c34ab5a566b85420192606bd8d31180cc7fa81d2b332`.
The denominator and standard basis construct flat native affine scheme morphisms over every domain.
-/

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
open scoped TensorProduct

namespace DeJongAlterations.Algebra.GenericFlatness
noncomputable section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- A genuine algebra equivalence descends through the entire ideal image. -/
def wholeIdealQuotientAlgEquiv (e : A ≃ₐ[R] B) (H : Ideal A) :
    (A ⧸ H) ≃ₐ[R] (B ⧸ Ideal.map e.toRingHom H) :=
  Ideal.quotientEquivAlg H (Ideal.map e.toRingHom H) e rfl

variable (R) (S : Type*) [CommRing S] [Algebra R S]

/-- The entire extended polynomial ideal quotient is actual tensor base change. -/
def polynomialQuotientBaseChangeEquiv (t : ℕ) (H : Ideal (MvPolynomial (Fin t) R)) :
    (S ⊗[R] (MvPolynomial (Fin t) R ⧸ H)) ≃ₐ[S]
      (MvPolynomial (Fin t) S ⧸ Ideal.map (MvPolynomial.map (algebraMap R S)) H) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin t) R S
  let J := Ideal.map (Algebra.TensorProduct.includeRight (A := S) (R := R)) H
  have hJ : Ideal.map e.toRingHom J = Ideal.map (MvPolynomial.map (algebraMap R S)) H := by
    dsimp only [J]
    change Ideal.map e.toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom H) = _
    rw [Ideal.map_map (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom e.toRingHom]
    congr 1
    apply RingHom.ext
    intro P
    change e (1 ⊗ₜ[R] P) = MvPolynomial.map (algebraMap R S) P
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  let T := Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (MvPolynomial (Fin t) R) S H
  let E := wholeIdealQuotientAlgEquiv e J
  rw [← hJ]
  exact T.trans E

/-- Whole free polynomial quotients remain free under actual coefficient extension. -/
theorem moduleFree_coefficient_extended_quotient (t : ℕ) (H : Ideal (MvPolynomial (Fin t) R))
    [Module.Free R (MvPolynomial (Fin t) R ⧸ H)] :
    Module.Free S (MvPolynomial (Fin t) S ⧸ Ideal.map (MvPolynomial.map (algebraMap R S)) H) := by
  let e := polynomialQuotientBaseChangeEquiv R S t H
  exact Module.Free.of_equiv e.toLinearEquiv


universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section UniformDenominator

open DeJongAlterations.Algebra.GenericFreeness

variable {D K : Type u} [CommRing D] [IsDomain D] [Field K]
  [Algebra D K] [IsFractionRing D K]

/-- The internally chosen uniform denominator makes the actual coefficient-localized quotient
flat as a native affine scheme over the localized coefficient ring. -/
theorem flat_uniformLocalizedQuotient (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) D)) :
    Flat (Spec.map (CommRingCat.ofHom
      (R := Localization.Away (uniformLeadingDenominator (K := K) t m H))
      (S := MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)) ⧸
        uniformLocalizedIdeal (K := K) t m H)
      (algebraMap _ _))) := by
  let := moduleFree_uniform_localized_quotient (K := K) t m H
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The same internally chosen denominator makes the actual tensor base change flat,
transporting through the genuine coefficient-extension quotient algebra equivalence. -/
theorem flat_uniformTensorQuotient (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) D)) :
    Flat (Spec.map (CommRingCat.ofHom
      (R := Localization.Away (uniformLeadingDenominator (K := K) t m H))
      (S := Localization.Away (uniformLeadingDenominator (K := K) t m H) ⊗[D]
        (MvPolynomial (Fin t) D ⧸ H))
      (algebraMap _ _))) := by
  let L := Localization.Away (uniformLeadingDenominator (K := K) t m H)
  let : Module.Free L
      (MvPolynomial (Fin t) L ⧸ Ideal.map (MvPolynomial.map (algebraMap D L)) H) :=
    moduleFree_uniform_localized_quotient (K := K) t m H
  let e := polynomialQuotientBaseChangeEquiv D L t H
  let : Module.Flat L (L ⊗[D] (MvPolynomial (Fin t) D ⧸ H)) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv
  apply Flat.SpecMap_iff.mpr
  exact (RingHom.flat_algebraMap_iff
    (R := L) (S := L ⊗[D] (MvPolynomial (Fin t) D ⧸ H))).mpr inferInstance

end UniformDenominator

/-- Every polynomial quotient over a domain has a nonempty principal base open on which its
literal coefficient-localized quotient gives a flat native affine morphism. -/
theorem exists_nonzero_flat_polynomial_quotient (D : Type u) [CommRing D] [IsDomain D]
    (t : ℕ) (H : Ideal (MvPolynomial (Fin t) D)) :
    ∃ b : D, b ≠ 0 ∧
      Flat (Spec.map (CommRingCat.ofHom (R := Localization.Away b)
        (S := MvPolynomial (Fin t) (Localization.Away b) ⧸
          Ideal.map (MvPolynomial.map (algebraMap D (Localization.Away b))) H)
        (algebraMap _ _))) := by
  let : Field (FractionRing D) := FractionRing.field D
  let m : MonomialOrder (Fin t) := MonomialOrder.degLex
  refine ⟨GenericFreeness.uniformLeadingDenominator (K := FractionRing D) t m H,
    GenericFreeness.uniformLeadingDenominator_ne_zero (K := FractionRing D) t m H, ?_⟩
  exact flat_uniformLocalizedQuotient (K := FractionRing D) t m H

/-- The actual base change of the original polynomial quotient is flat after inverting
one internally constructed nonzero base element. -/
theorem exists_nonzero_flat_tensor_quotient (D : Type u) [CommRing D] [IsDomain D]
    (t : ℕ) (H : Ideal (MvPolynomial (Fin t) D)) :
    ∃ b : D, b ≠ 0 ∧
      Flat (Spec.map (CommRingCat.ofHom (R := Localization.Away b)
        (S := Localization.Away b ⊗[D] (MvPolynomial (Fin t) D ⧸ H))
        (algebraMap _ _))) := by
  let : Field (FractionRing D) := FractionRing.field D
  let m : MonomialOrder (Fin t) := MonomialOrder.degLex
  refine ⟨GenericFreeness.uniformLeadingDenominator (K := FractionRing D) t m H,
    GenericFreeness.uniformLeadingDenominator_ne_zero (K := FractionRing D) t m H, ?_⟩
  exact flat_uniformTensorQuotient (K := FractionRing D) t m H


/-- Generic flatness for every affine finite-type algebra over a domain, using an internally
selected finite polynomial presentation and genuine tensor algebra-equivalence transport. -/
theorem exists_nonzero_flat_finiteType_algebra (D A : Type u) [CommRing D] [IsDomain D]
    [CommRing A] [Algebra D A] [Algebra.FiniteType D A] :
    ∃ b : D, b ≠ 0 ∧
      Flat (Spec.map (CommRingCat.ofHom (R := Localization.Away b)
        (S := Localization.Away b ⊗[D] A) (algebraMap _ _))) := by
  obtain ⟨t, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := D) (S := A)).mp
    (inferInstance : Algebra.FiniteType D A)
  let H := RingHom.ker f
  obtain ⟨b, hb, hflat⟩ := exists_nonzero_flat_tensor_quotient D t H
  let L := Localization.Away b
  let eQ : (MvPolynomial (Fin t) D ⧸ H) ≃ₐ[D] A :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  let e : (L ⊗[D] (MvPolynomial (Fin t) D ⧸ H)) ≃ₐ[L] (L ⊗[D] A) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) eQ
  have hringflat := Flat.SpecMap_iff.mp hflat
  let : Module.Flat L (L ⊗[D] (MvPolynomial (Fin t) D ⧸ H)) :=
    (RingHom.flat_algebraMap_iff
      (R := L) (S := L ⊗[D] (MvPolynomial (Fin t) D ⧸ H))).mp hringflat
  let : Module.Flat L (L ⊗[D] A) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  refine ⟨b, hb, ?_⟩
  apply Flat.SpecMap_iff.mpr
  exact (RingHom.flat_algebraMap_iff (R := L) (S := L ⊗[D] A)).mpr inferInstance

end

end DeJongAlterations.Algebra.GenericFlatness
