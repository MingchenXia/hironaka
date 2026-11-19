import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.FiniteStability
import Hironaka.Algebra.RelativeNoetherNormalizationDenominators

/-!
# Actual polynomial normalization coordinates in the original domain algebra

Field Noether normalization of the literal generic tensor algebra supplies
coordinates. A common nonzero base denominator brings them into the original
algebra. A genuine invertible polynomial rescaling preserves the finite
generic normalization, and injectivity descends to the original polynomial
map. Finiteness after one principal base localization is a separate producer.
-/

noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace Hironaka.Algebra.RelativeNoetherNormalizationCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Multiplying every polynomial variable by an actual unit is an actual algebra automorphism. -/
def scaleVariables {K : Type*} [CommRing K] {ι : Type*} (c : Kˣ) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (aeval fun i => C (c : K) * X i)
    (aeval fun i => C ((c⁻¹ : Kˣ) : K) * X i)
    (by ext i; simp) (by ext i; simp)

@[simp]
theorem scaleVariables_X {K : Type*} [CommRing K] {ι : Type*} (c : Kˣ) (i : ι) :
    scaleVariables c (X i) = C (c : K) * X i := by
  simp [scaleVariables]

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R A] [Algebra.FiniteType R A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Finite type and the actual generic tensor algebra internally construct compatible
injective polynomial coordinates whose generic map is genuinely finite. -/
theorem exists_generic_finite_polynomial_model (hinj : Function.Injective (algebraMap R A)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A)
      (g : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R]
        (FractionRing R ⊗[R] A)),
      Function.Injective f ∧ Function.Injective g ∧ g.Finite ∧
      g.toRingHom.comp (MvPolynomial.map (algebraMap R (FractionRing R))) =
        (algebraMap A (FractionRing R ⊗[R] A)).comp f.toRingHom := by
  classical
  let K := FractionRing R
  let B := K ⊗[R] A
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  have hM : M ≤ nonZeroDivisors A := by
    rintro x ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro h
    exact mem_nonZeroDivisors_iff_ne_zero.mp hr (hinj (by simpa using h))
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite M
    (fun i : Fin n => g (X i))
  obtain ⟨r, hr, he⟩ := m.property
  choose a ha using hm
  have hrK : algebraMap R K r ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
  let c : Kˣ := Units.mk0 (algebraMap R K r) hrK
  let g' := g.comp (scaleVariables (ι := Fin n) c).toAlgHom
  let f : MvPolynomial (Fin n) R →ₐ[R] A := aeval a
  have ha' (i : Fin n) : algebraMap A B (a i) =
      algebraMap K B (algebraMap R K r) * g (X i) := by
    rw [ha i, Algebra.smul_def, ← he,
      ← IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R K B]
  have hcomp : g'.toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      (algebraMap A B).comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro s
      simp only [RingHom.comp_apply, map_C]
      change g' (algebraMap K _ (algebraMap R K s)) =
        algebraMap A B (f (algebraMap R _ s))
      rw [g'.commutes, f.commutes]
      exact (IsScalarTower.algebraMap_apply R K B s).symm.trans
        (IsScalarTower.algebraMap_apply R A B s)
    · intro i
      simpa [g', f, scaleVariables, c] using (ha' i).symm
  have hg' : Function.Injective g' := hg.comp (scaleVariables c).injective
  have hf : Function.Injective f := by
    intro p q hpq
    apply MvPolynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    apply hg'
    rw [show g' ((MvPolynomial.map (algebraMap R K)) p) = algebraMap A B (f p) from
      DFunLike.congr_fun hcomp p,
      show g' ((MvPolynomial.map (algebraMap R K)) q) = algebraMap A B (f q) from
        DFunLike.congr_fun hcomp q, hpq]
  exact ⟨n, f, g', hf, hg', hfin.comp
    (AlgHom.Finite.of_surjective _ (scaleVariables c).surjective), hcomp⟩

end Hironaka.Algebra.RelativeNoetherNormalizationCoordinates
