/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalCoefficientFunctionAlgebra
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Whole polynomial coefficient extension as an actual tensor base change -/

set_option autoImplicit false
open scoped TensorProduct

namespace Hironaka.HironakaRelativeNormalCoefficientPolynomialBaseChange
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

section UniformDenominator

open HironakaRelativeNormalUniformLocalization

variable {D K T : Type*} [CommRing D] [IsDomain D] [Field K]
  [Algebra D K] [IsFractionRing D K] [CommRing T]

/-- A single genuine uniform denominator makes all actual coefficient-image quotients free. -/
theorem moduleFree_coefficient_image_at_uniform_denominator
    (t : ℕ) (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* T)
    (hf : IsUnit (f (uniformLeadingDenominator (K := K) t m H))) :
    Module.Free T (MvPolynomial (Fin t) T ⧸ Ideal.map (MvPolynomial.map f) H) := by
  let b := uniformLeadingDenominator (K := K) t m H
  let L := Localization.Away b
  let f' : L →+* T := IsLocalization.Away.lift b hf
  let : Algebra L T := f'.toAlgebra
  let HL := uniformLocalizedIdeal (K := K) t m H
  let : Module.Free L (MvPolynomial (Fin t) L ⧸ HL) := moduleFree_uniform_localized_quotient t m H
  have hfree := moduleFree_coefficient_extended_quotient L T t HL
  have hcomp : f'.comp (algebraMap D L) = f := by
    apply RingHom.ext
    intro r
    exact IsLocalization.Away.lift_eq b hf r
  have hmap : Ideal.map (MvPolynomial.map (algebraMap L T)) HL = Ideal.map (MvPolynomial.map f) H := by
    change Ideal.map (MvPolynomial.map f')
      (Ideal.map (MvPolynomial.map (algebraMap D L)) H) = _
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro P
    change MvPolynomial.map f' (MvPolynomial.map (algebraMap D L) P) = MvPolynomial.map f P
    rw [MvPolynomial.map_map, hcomp]
  rw [hmap] at hfree
  exact hfree

end UniformDenominator

end
end Hironaka.HironakaRelativeNormalCoefficientPolynomialBaseChange
