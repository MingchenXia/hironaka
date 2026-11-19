import Hironaka.Algebra.RelativeNoetherNormalization
import Hironaka.Algebra.RelativeNoetherNormalizationSpreading

/-!
# Actual relative Noether normalization after one principal base localization

An injective finite-type map of domains internally supplies a nonzero base
element and an actual injective finite polynomial map over that localization.
The original finite generators, generic normalization, cleared monic equations,
localized module finiteness, and literal coefficient triangle are constructed.
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.RelativeNoetherNormalizationFinite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}

/-- The actual coefficient-localized polynomial ring is the native principal localization. -/
def polynomialLocalizationEquiv (b : R) :
    Localization.Away (C (σ := Fin n) b) ≃ₐ[MvPolynomial (Fin n) R]
      MvPolynomial (Fin n) (Localization.Away b) := by
  have : IsLocalization (Submonoid.powers (C (σ := Fin n) b))
      (MvPolynomial (Fin n) (Localization.Away b)) := by
    simpa only [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := Fin n) (Submonoid.powers b) (Localization.Away b))
  exact IsLocalization.algEquiv (Submonoid.powers (C (σ := Fin n) b)) _ _

/-- The actual coefficient-localization equivalence preserves every original constant. -/
theorem polynomialLocalizationEquiv_symm_C (b r : R) :
    (polynomialLocalizationEquiv (n := n) b).symm (C (algebraMap R (Localization.Away b) r)) =
      algebraMap (MvPolynomial (Fin n) R) (Localization.Away (C (σ := Fin n) b)) (C r) := by
  simpa only [MvPolynomial.algebraMap_def, MvPolynomial.map_C] using
    (polynomialLocalizationEquiv (n := n) b).symm.commutes (C r)

/-- The actual polynomial map into the principal localization of the original algebra. -/
def polynomialLocalizationMap (f : MvPolynomial (Fin n) R →+* A) (b : R) :
    MvPolynomial (Fin n) (Localization.Away b) →+* Localization.Away (f (C b)) :=
  (Localization.awayMap f (C b)).comp (polynomialLocalizationEquiv b).symm.toRingHom

/-- The whole localized coefficient map is the one induced by the original constants. -/
theorem polynomialLocalizationMap_C (f : MvPolynomial (Fin n) R →+* A) (b : R) :
    (polynomialLocalizationMap f b).comp C = Localization.awayMap (f.comp C) b := by
  apply IsLocalization.ringHom_ext (Submonoid.powers b)
  apply RingHom.ext
  intro r
  change (Localization.awayMap f (C b))
      ((polynomialLocalizationEquiv b).symm (C (algebraMap R (Localization.Away b) r))) =
    (Localization.awayMap (f.comp C) b) (algebraMap R (Localization.Away b) r)
  rw [polynomialLocalizationEquiv_symm_C]
  simp [Localization.awayMap, IsLocalization.Away.map]

/-- Actual injectivity persists through the polynomial coefficient-localization equivalence. -/
theorem polynomialLocalizationMap_injective (f : MvPolynomial (Fin n) R →+* A)
    (hf : Function.Injective f) (b : R) : Function.Injective (polynomialLocalizationMap f b) := by
  have hloc : Function.Injective (Localization.awayMap f (C b)) := by
    apply Localization.awayMap_injective_iff.mpr
    intro a ha
    refine ⟨0, ?_⟩
    simpa only [pow_zero, one_mul] using hf (ha.trans (map_zero f).symm)
  exact hloc.comp (polynomialLocalizationEquiv b).symm.injective

variable [Algebra R A]

/-- Cleared original generator equations make the actual localized polynomial map finite. -/
theorem polynomialLocalizationMap_finite (f : MvPolynomial (Fin n) R →ₐ[R] A)
    (b : R) (s : Finset A) (hs : Algebra.adjoin R (s : Set A) = ⊤)
    (hint : ∀ a ∈ s, f.toRingHom.IsIntegralElem (b • a)) :
    (polynomialLocalizationMap f.toRingHom b).Finite :=
  (RelativeNoetherNormalizationSpreading.awayMap_finite_of_integral_scaled_generators
    f b s hs hint).comp (polynomialLocalizationEquiv b).symm.toRingEquiv.finite

/-- Relative Noether normalization constructs a finite injective polynomial map after one
internally chosen nonzero base localization, with its literal original coefficient triangle. -/
theorem exists_finite_injective_polynomial_map [IsDomain R] [IsDomain A]
    [Algebra.FiniteType R A] (hinj : Function.Injective (algebraMap R A)) :
    ∃ b : R, b ≠ 0 ∧ ∃ (n : ℕ)
      (g : MvPolynomial (Fin n) (Localization.Away b) →+*
        Localization.Away (algebraMap R A b)),
      Function.Injective g ∧ g.Finite ∧
        g.comp C = Localization.awayMap (algebraMap R A) b := by
  obtain ⟨n, f, hf, b, hb, s, hs, hint⟩ :=
    RelativeNoetherNormalization.exists_integral_generating_family R A hinj
  have hC : f.toRingHom.comp C = algebraMap R A := RingHom.ext (fun r => f.commutes r)
  have H : ∃ g : MvPolynomial (Fin n) (Localization.Away b) →+* Localization.Away (f (C b)),
      Function.Injective g ∧ g.Finite ∧ g.comp C = Localization.awayMap (f.toRingHom.comp C) b :=
    ⟨polynomialLocalizationMap f.toRingHom b, polynomialLocalizationMap_injective _ hf b,
      polynomialLocalizationMap_finite f b s hs hint, polynomialLocalizationMap_C _ b⟩
  refine ⟨b, hb, n, ?_⟩
  rw [← hC]
  exact H

/-- The native algebra-map version uses exactly the coefficient algebra induced by the
original localization map; finiteness is the actual `Module.Finite` instance for this map. -/
theorem exists_finite_injective_algHom [IsDomain R] [IsDomain A]
    [Algebra.FiniteType R A] (hinj : Function.Injective (algebraMap R A)) :
    ∃ b : R, b ≠ 0 ∧ ∃ n : ℕ,
      letI : Algebra (Localization.Away b) (Localization.Away (algebraMap R A b)) :=
        (Localization.awayMap (algebraMap R A) b).toAlgebra
      ∃ g : MvPolynomial (Fin n) (Localization.Away b) →ₐ[Localization.Away b]
        Localization.Away (algebraMap R A b), Function.Injective g ∧ g.Finite := by
  obtain ⟨b, hb, n, g, hg, hfin, hC⟩ := exists_finite_injective_polynomial_map hinj
  refine ⟨b, hb, n, ?_⟩
  let : Algebra (Localization.Away b) (Localization.Away (algebraMap R A b)) :=
    (Localization.awayMap (algebraMap R A) b).toAlgebra
  refine ⟨{ g with commutes' := ?_ }, hg, hfin⟩
  intro r
  exact RingHom.congr_fun hC r

end Hironaka.Algebra.RelativeNoetherNormalizationFinite
