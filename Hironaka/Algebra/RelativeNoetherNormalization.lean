import Hironaka.Algebra.RelativeNoetherNormalizationCoordinates
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Normalization coordinates with cleared monic equations for actual algebra generators

For an injective finite-type map of domains, we internally construct an
injective polynomial map into the original algebra and a finite original
algebra-generating family. One nonzero base multiplier makes every member
of that family integral over this polynomial map. The polynomial map and
all monic relations are produced from actual generic Noether normalization.
The final principal-localized module-finiteness assembly is separate.
-/

noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace Hironaka.Algebra.RelativeNoetherNormalization

open RelativeNoetherNormalizationCoordinates RelativeNoetherNormalizationDenominators

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R A] [Algebra.FiniteType R A]

/-- Actual generic normalization constructs original polynomial coordinates and clears
monic relations of an internally chosen finite original algebra-generating family. -/
theorem exists_integral_generating_family (hinj : Function.Injective (algebraMap R A)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Injective f ∧
      ∃ b : R, b ≠ 0 ∧ ∃ s : Finset A, Algebra.adjoin R (s : Set A) = ⊤ ∧
        ∀ a ∈ s, f.toRingHom.IsIntegralElem (b • a) := by
  classical
  let K := FractionRing R
  let B := K ⊗[R] A
  obtain ⟨n, f, g, hf, hg, hfin, hcomp⟩ := exists_generic_finite_polynomial_model R A hinj
  let P := MvPolynomial (Fin n) R
  let P_K := MvPolynomial (Fin n) K
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra P_K B := g.toRingHom.toAlgebra
  let : Algebra P B :=
    (g.toRingHom.comp (MvPolynomial.map (algebraMap R K))).toAlgebra
  have : IsScalarTower P P_K B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' hcomp
  have : IsScalarTower R P A :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower R P B := by
    apply IsScalarTower.of_algebraMap_eq'
    calc
      algebraMap R B = (algebraMap A B).comp (algebraMap R A) :=
        IsScalarTower.algebraMap_eq R A B
      _ = ((algebraMap A B).comp f.toRingHom).comp (algebraMap R P) := by
        rw [RingHom.comp_assoc]
        exact RingHom.ext fun r => congrArg (algebraMap A B) (f.commutes r).symm
      _ = (algebraMap P B).comp (algebraMap R P) := by rw [← hcomp]; rfl
  have hM : Algebra.algebraMapSubmonoid A (nonZeroDivisors R) ≤ nonZeroDivisors A := by
    rintro x ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro h
    exact mem_nonZeroDivisors_iff_ne_zero.mp hr (hinj (by simpa using h))
  have hj : Function.Injective (IsScalarTower.toAlgHom P A B) :=
    IsLocalization.injective B hM
  have : Module.Finite P_K B := hfin
  have : Algebra.IsIntegral P_K B := Algebra.IsIntegral.of_finite P_K B
  have : IsLocalization ((nonZeroDivisors R).map (algebraMap R P)) P_K :=
    MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors R) K
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  obtain ⟨b, hb, hbi⟩ := exists_nonzero_integral_smul_family_of_injective
    (R := R) (P := P) (P_K := P_K) (IsScalarTower.toAlgHom P A B) hj
    (fun i : s => (i : A)) (fun _ => Algebra.IsIntegral.isIntegral _)
  exact ⟨n, f, hf, b, hb, s, hs, fun a ha => hbi ⟨a, ha⟩⟩

end Hironaka.Algebra.RelativeNoetherNormalization
