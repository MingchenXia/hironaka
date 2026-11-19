import Hironaka.Resolution.HironakaActualWeightedScaling

/-! Genuine original diagonal pullbacks, their actual inverses and the whole literal rescaling dictionary. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualDiagonalTaylor

noncomputable section

open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
  HironakaActualFormalCoordinatePowerDivision HironakaActualFiniteDegLexWeights

variable {n : ℕ}

def actualDiagonalMap (c : Fin n → ℂ) : ComplexModel n →L[ℂ] ComplexModel n :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => c i • (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ))

theorem actualDiagonalMap_apply (c : Fin n → ℂ) (z : ComplexModel n) (i : Fin n) :
    actualDiagonalMap c z i = c i * z i := rfl

private theorem actualDiagonalMap_inverse (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) (z : ComplexModel n) :
    actualDiagonalMap c (actualDiagonalMap (fun i => (c i)⁻¹) z) = z := by
  ext i
  rw [actualDiagonalMap_apply,actualDiagonalMap_apply,← mul_assoc,mul_inv_cancel₀ (hc i),one_mul]

def actualDiagonalPullback (c : Fin n → ℂ) : HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (actualDiagonalMap c)
    (Eventually.of_forall fun _ => (actualDiagonalMap c).differentiableAt) (map_zero _)

theorem actualDiagonalPullback_const (c : Fin n → ℂ) (a : ℂ) :
    actualDiagonalPullback c (HolGerm.constHom a) = HolGerm.constHom a :=
  (actualDiagonalPullback c).commutes a

theorem actualDiagonalPullback_coordinate (c : Fin n → ℂ) (i : Fin n) :
    actualDiagonalPullback c (coordinateGerm i) = HolGerm.constHom (c i) * coordinateGerm i := by
  unfold actualDiagonalPullback coordinateGerm
  rw [compAlgHom_mk,← HolGerm.mk_const,← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

theorem actualDiagonalPullback_inverse (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (g : HolGerm (ComplexModel n)) :
    actualDiagonalPullback (fun i => (c i)⁻¹) (actualDiagonalPullback c g) = g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold actualDiagonalPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp only [Function.comp_apply,actualDiagonalMap_inverse c hc]

private theorem formalRescale_X (c : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries.rescaleAlgHom c (MvPowerSeries.X i) =
      MvPowerSeries.C (c i) * MvPowerSeries.X i := by
  rw [MvPowerSeries.rescaleAlgHom,MvPowerSeries.substAlgHom_X]
  change c i • (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) = _
  rw [MvPowerSeries.smul_eq_C_mul]

theorem actualTaylor_diagonalPullback (c : Fin n → ℂ) :
    (actualUnshiftedTaylorAlgHom n).comp (actualDiagonalPullback c) =
      (MvPowerSeries.rescaleAlgHom c).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualDiagonalPullback c (coordinateGerm i)) =
      MvPowerSeries.rescaleAlgHom c (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
    rw [actualDiagonalPullback_coordinate,map_mul,actualUnshiftedTaylor_coordinate,
      formalRescale_X]
    exact congrArg (fun a : MvPowerSeries (Fin n) ℂ => a * MvPowerSeries.X i)
      ((actualUnshiftedTaylorAlgHom n).commutes (c i))
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualDiagonalPullback c (coordinateGerm i)) ∈ _
    rw [actualDiagonalPullback_coordinate,map_mul,actualUnshiftedTaylor_coordinate]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,mem_univ _,rfl⟩)

theorem coeff_actualDiagonalPullback (c : Fin n → ℂ) (g : HolGerm (ComplexModel n))
    (b : Fin n →₀ ℕ) :
    MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n (actualDiagonalPullback c g)) =
      (b.prod fun i d => c i ^ d) * MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n g) := by
  have he := congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ => f g)
    (actualTaylor_diagonalPullback c)
  change actualUnshiftedTaylorAlgHom n (actualDiagonalPullback c g) =
    MvPowerSeries.rescaleAlgHom c (actualUnshiftedTaylorAlgHom n g) at he
  rw [he,MvPowerSeries.rescaleAlgHom_apply,MvPowerSeries.coeff_rescale]

theorem weighted_inverse_monomial_scalar (W : Fin n → ℕ) (s : ℂ) (hs : s ≠ 0)
    (a : Fin n →₀ ℕ) :
    s ^ weightedDegree W a * (a.prod fun i d => ((s ^ W i)⁻¹) ^ d) = 1 := by
  have hp : (a.prod fun i d => ((s ^ W i)⁻¹) ^ d) = (s ^ weightedDegree W a)⁻¹ := by
    rw [a.prod_fintype (fun i d => ((s ^ W i)⁻¹) ^ d) (fun _ => pow_zero _)]
    calc
      _ = (∏ i : Fin n, s ^ (W i * a i))⁻¹ := by
        simp only [inv_pow,← pow_mul,Finset.prod_inv_distrib]
      _ = (s ^ weightedDegree W a)⁻¹ := by rw [Finset.prod_pow_eq_pow_sum]; rfl
  rw [hp,mul_inv_cancel₀ (pow_ne_zero _ hs)]

end

end Hironaka.HironakaActualDiagonalTaylor
