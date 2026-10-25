import DeJongAlterations.Algebra.IntegralClosureFiniteType
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Locus

/-!
# A genuine etale localization in a specified separable field extension

The integral closure and its finite presentation are constructed from finite
extension and finite type over the original arbitrary coefficient field.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NormalizationInExtension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped nonZeroDivisors

/-- The actual integral closure in a finite separable extension has a nonzero
principal source localization which is etale over the original coefficient ring. -/
theorem exists_etale_localization (k R K L : Type u) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ c : integralClosure R L, c ≠ 0 ∧ Algebra.Etale R (Localization.Away c) := by
  let C := integralClosure R L
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : Module.Finite R C :=
    IntegralClosureFiniteType.finite_of_isIntegralClosure_of_finiteType k R K L C
  let : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  let : IsFractionRing C (Localization.AtPrime (⊥ : Ideal C)) := by
    change IsLocalization C⁰ (Localization.AtPrime (⊥ : Ideal C))
    convert (inferInstance : IsLocalization (⊥ : Ideal C).primeCompl
      (Localization.AtPrime (⊥ : Ideal C))) using 1
    ext c
    simp only [Ideal.mem_primeCompl_iff, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
  let : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization R⁰
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let : Algebra.FormallyEtale R L := Algebra.FormallyEtale.comp R K L
  let e := (IsLocalization.algEquiv C⁰ L (Localization.AtPrime (⊥ : Ideal C))).restrictScalars R
  let : Algebra.IsEtaleAt R (⊥ : Ideal C) := Algebra.FormallyEtale.of_equiv e
  obtain ⟨c, hc, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal C)
  exact ⟨c, by simpa only [Ideal.mem_bot] using hc, he⟩

end DeJongAlterations.Algebra.NormalizationInExtension
