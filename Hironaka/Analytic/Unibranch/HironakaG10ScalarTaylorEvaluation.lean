import Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
import Hironaka.Resolution.HironakaActualMultilinearTaylorCoordinates

/-! # Evaluation of the actual scalar Taylor jet in a nilpotent quotient -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10ScalarTaylorEvaluation
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaActualOriginalTaylorPolynomial
  HironakaActualMultilinearTaylorCoordinates
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor

/-- An algebra map which kills the original maximal-ideal power evaluates
  an entire scalar germ by its actual finite coordinate-word Taylor sum. -/
theorem scalar_germ_eq_finite_taylor
    {Γ : Type*} [CommRing Γ] [Algebra ℂ Γ] (d q : ℕ)
    (φ : HolGerm (ComplexModel (0+d)) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+d))) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (g : ComplexModel (0+d) → ℂ)
    (hg : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+d)), DifferentiableAt ℂ g z) :
    φ (HolGerm.mk g hg) =
      ∑ k ∈ Finset.range (q+1), ∑ w : Fin k → Fin d,
        φ (∏ i : Fin k, normalCoordinate 0 d (w i)) *
          algebraMap ℂ Γ ((Nat.factorial k : ℂ)⁻¹ • (iteratedFDeriv ℂ k g 0)
            (fun i => EuclideanSpace.single ((w i).natAdd 0) (1 : ℂ))) := by
  classical
  let p : FormalMultilinearSeries ℂ (ComplexModel (0+d)) ℂ := fun k =>
    (Nat.factorial k : ℂ)⁻¹ • iteratedFDeriv ℂ k g 0
  have hp : HasFPowerSeriesAt g p 0 := has_normalized_powerSeriesAt g hg
  have hrem : φ (HolGerm.mk g hg -
      originalPolynomialEval d (originalTaylorPolynomial d q (HolGerm.mk g hg))) = 0 :=
    hφ (originalTaylorPolynomial_remainder d q (HolGerm.mk g hg))
  have hEq : φ (HolGerm.mk g hg) =
      φ (originalPolynomialEval d (originalTaylorPolynomial d q (HolGerm.mk g hg))) := by
    simpa only [map_sub,sub_eq_zero] using hrem
  rw [hEq, originalTaylorPolynomial_eq_multilinearPartial d q g hg p hp]
  rw [originalPolynomialEval,MvPolynomial.comp_aeval_apply]
  simp only [multilinearPartialPolynomial,multilinearCoordinatePolynomial,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro w hw
  rw [coordinateWordExponent,MvPolynomial.monomial_sum_index]
  have hX (i : Fin d) : (MvPolynomial.monomial (Finsupp.single i 1) (1 : ℂ) :
      MvPolynomial (Fin d) ℂ) = MvPolynomial.X i := rfl
  simp only [map_mul,map_prod,hX,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
    p,smul_apply]
  exact mul_comm _ _

end Hironaka.Analytic.Unibranch.HironakaG10ScalarTaylorEvaluation
