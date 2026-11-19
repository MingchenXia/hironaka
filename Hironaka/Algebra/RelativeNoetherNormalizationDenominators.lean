import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Actual common base denominators for generic integral equations

For a finite family integral after localization of the coefficient algebra
at nonzero elements of a domain base, one nonzero base multiplier makes the
entire family integral over the original coefficient algebra. Actual
injective algebra maps reflect the resulting monic equations to the original
algebra. These are denominator-descent producers for relative Noether
normalization, not a claim of the full normalization or fiber-dimension theorem.
-/

noncomputable section

namespace Hironaka.Algebra.RelativeNoetherNormalizationDenominators

universe u v w z

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} {P : Type v} {P_K : Type w} {T : Type z}
  [CommRing R] [IsDomain R] [CommRing P] [CommRing P_K] [CommRing T]
  [Algebra R P] [Algebra P P_K]
  [IsLocalization ((nonZeroDivisors R).map (algebraMap R P)) P_K]
  [Algebra P_K T] [Algebra P T] [IsScalarTower P P_K T]
  [Algebra R T] [IsScalarTower R P T]

/-- Actual monic equations descend simultaneously after multiplication by one nonzero base element. -/
theorem exists_nonzero_integral_smul_family {ι : Type*} [Fintype ι]
    (x : ι → T) (hx : ∀ i, IsIntegral P_K (x i)) :
    ∃ b : R, b ≠ 0 ∧ ∀ i, IsIntegral P (b • x i) := by
  classical
  have hi (i : ι) : ∃ r : R, r ≠ 0 ∧ IsIntegral P (r • x i) := by
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      ((nonZeroDivisors R).map (algebraMap R P)) (x i) (hx i)
    obtain ⟨r, hr, he⟩ := m.property
    refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, ?_⟩
    simpa only [Submonoid.smul_def, Algebra.smul_def, ← he,
      ← IsScalarTower.algebraMap_apply R P T] using hm
  choose r hr hir using hi
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.mpr (fun i _ => hr i), ?_⟩
  intro i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
  simpa only [hc, mul_smul, mul_comm] using IsIntegral.smul c (hir i)

variable {A : Type*} [CommRing A] [Algebra P A] [Algebra R A] [IsScalarTower R P A]

/-- Injectivity reflects the actually cleared monic equations into the original algebra. -/
theorem exists_nonzero_integral_smul_family_of_injective {ι : Type*} [Fintype ι]
    (j : A →ₐ[P] T) (hj : Function.Injective j)
    (a : ι → A) (ha : ∀ i, IsIntegral P_K (j (a i))) :
    ∃ b : R, b ≠ 0 ∧ ∀ i, IsIntegral P (b • a i) := by
  obtain ⟨b, hb, hbi⟩ := exists_nonzero_integral_smul_family
    (R := R) (P := P) (P_K := P_K) (fun i => j (a i)) ha
  refine ⟨b, hb, fun i => (isIntegral_algHom_iff j hj).mp ?_⟩
  rw [show j (b • a i) = b • j (a i) from
    (j.restrictScalars R).toLinearMap.map_smul b (a i)]
  exact hbi i

end Hironaka.Algebra.RelativeNoetherNormalizationDenominators
