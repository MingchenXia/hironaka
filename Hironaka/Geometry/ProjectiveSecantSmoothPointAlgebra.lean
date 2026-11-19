import Hironaka.Geometry.ProjectiveSecantSmoothPointChart
import Hironaka.Algebra.ProjectiveSecantPointDescent
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Whole original smooth algebra points over finite separable coefficient fields
-/

noncomputable section

open scoped TensorProduct

namespace Hironaka.Geometry.ProjectiveSecant

open Algebra.ProjectiveSecant

universe u

/-- The actual original smooth local structure internally chooses an etale polynomial chart and hence an actual whole algebra point over the same original separably closed field. -/
theorem exists_algHom_of_smooth_sepClosed
    (K A : Type u) [Field K] [IsSepClosed K] [CommRing A] [Nontrivial A] [Algebra K A]
    [Algebra.Smooth K A] : Nonempty (A →ₐ[K] K) := by
  let P : PrimeSpectrum A := Classical.choice inferInstance
  obtain ⟨f, hf, n, hpoly, htower, hetale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := P.asIdeal)
  let := hpoly
  let := htower
  let := hetale
  have hp : (Ideal.map (algebraMap A (Localization.Away f)) P.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) P.asIdeal P.isPrime
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf)
  let : Nontrivial (Localization.Away f) := PrimeSpectrum.nonempty_iff_nontrivial.mp
    ⟨⟨_, hp⟩⟩
  obtain ⟨χ⟩ := exists_algHom_of_etale_polynomial_sepClosed K (Localization.Away f) n
  exact ⟨χ.comp (IsScalarTower.toAlgHom K A (Localization.Away f))⟩

/-- For every original coefficient field, the entire original nonzero smooth algebra internally produces a whole algebra point in a finite separable intermediate field, without any separability assumption on a chosen closed point. -/
theorem exists_finite_separable_smooth_algebra_point
    (k A : Type u) [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.Smooth k A] :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧
      Algebra.IsSeparable k L ∧ Nonempty (A →ₐ[k] L) := by
  let E := SeparableClosure k
  let B := E ⊗[k] A
  let : Nontrivial B := (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right k E).mpr inferInstance
  obtain ⟨χ⟩ := exists_algHom_of_smooth_sepClosed E B
  let χk : A →ₐ[k] E := (χ.restrictScalars k).comp Algebra.TensorProduct.includeRight
  obtain ⟨L, hfin, hsep, χL, _⟩ := exists_finite_separable_point_descent k A χk
  exact ⟨L, hfin, hsep, ⟨χL⟩⟩

end Hironaka.Geometry.ProjectiveSecant
