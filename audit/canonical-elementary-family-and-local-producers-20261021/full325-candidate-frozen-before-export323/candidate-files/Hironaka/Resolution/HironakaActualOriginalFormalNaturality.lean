/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalFormalHSTransfer
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! Actual centered holomorphic germ pullbacks commute with genuine formal Taylor substitution. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalFormalNaturality
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualOriginalFormalHSTransfer
variable {m n : ℕ}

/-- EVERY original numerator's evaluation is preserved by the ACTUAL centered holomorphic map. -/
theorem compAlgHom_eval (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (g : HolGerm (ComplexModel (0+n))) :
    HolGerm.eval (compAlgHom η hη hη0 g)=HolGerm.eval g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
      rw [compAlgHom_mk]
      change F (η 0)=F 0
      rw [hη0]

/-- The ACTUAL original holomorphic pullback internally maps the WHOLE maximal ideal to the true target one. -/
theorem map_maximalIdeal_compAlgHom_le (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) :
    Ideal.map (compAlgHom η hη hη0).toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))) ≤
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+m))) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro g hg
  apply (HolGerm.mem_maximalIdeal_iff _).mpr
  change HolGerm.eval (compAlgHom η hη hη0 g)=0
  rw [compAlgHom_eval]
  exact (HolGerm.mem_maximalIdeal_iff _).mp hg

/-- EVERY genuine original maximal power is preserved by the actual centered pullback. -/
theorem map_maximal_pow_compAlgHom_le (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) (q : ℕ) :
    Ideal.map (compAlgHom η hη hη0).toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) ≤
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+m))) ^ q := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (map_maximalIdeal_compAlgHom_le η hη hη0) q

/-- The literal true formal Taylor series of the SAME actual original coordinate pullbacks. -/
def actualFormalCoordinateImages (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (i : Fin n) : MvPowerSeries (Fin m) ℂ :=
  originalTaylorAlgHom m (compAlgHom η hη hη0 (normalCoordinate 0 n i))

/-- The ACTUAL original map supplies genuine formal variable-ideal membership internally. -/
theorem actualFormalCoordinateImages_mem_variables (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) (i : Fin n) :
    actualFormalCoordinateImages η hη hη0 i ∈ genuineFormalVariables m := by
  have hc : normalCoordinate 0 n i ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) := by
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    simp [normalCoordinate,coordinateGerm,HolGerm.eval_mk]
  have hp := map_maximalIdeal_compAlgHom_le η hη hη0
    (Ideal.mem_map_of_mem (compAlgHom η hη hη0).toRingHom hc)
  have ht := Ideal.mem_map_of_mem (originalTaylorAlgHom m).toRingHom hp
  rw [map_original_maximalIdeal_eq_formal_variables] at ht
  exact ht

/-- Every SAME actual formal coordinate image has genuine constant coefficient zero. -/
theorem actualFormalCoordinateImages_constant_zero (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) (i : Fin n) :
    MvPowerSeries.constantCoeff (actualFormalCoordinateImages η hη hη0 i)=0 := by
  change MvPowerSeries.coeff 0 (actualFormalCoordinateImages η hη hη0 i)=0
  exact (mem_genuineFormalVariables_pow_iff_coefficients_zero m 1 _).mp
    (by simpa only [pow_one] using actualFormalCoordinateImages_mem_variables η hη hη0 i)
    0 (by simp [normalExponentDegree])

/-- The GENUINE formal complex algebra substitution is internally constructed from the actual original map. -/
def actualFormalPullback (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin m) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalCoordinateImages_constant_zero η hη hη0))

/-- EACH original formal variable retains the Taylor series of its literal actual coordinate pullback. -/
theorem actualFormalPullback_X (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) (i : Fin n) :
    actualFormalPullback η hη hη0 (MvPowerSeries.X i)=actualFormalCoordinateImages η hη hη0 i :=
  MvPowerSeries.substAlgHom_X _ i

/-- Image of the WHOLE genuine formal variable ideal is contained in the actual target variable ideal. -/
theorem map_variables_actualFormalPullback_le (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) :
    Ideal.map (actualFormalPullback η hη hη0).toRingHom (genuineFormalVariables n) ≤ genuineFormalVariables m := by
  change Ideal.map (actualFormalPullback η hη hη0).toRingHom
    (Ideal.span (range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ))) ≤ _
  rw [Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨G,⟨i,rfl⟩,rfl⟩
  change actualFormalPullback η hη hη0 (MvPowerSeries.X i) ∈ genuineFormalVariables m
  rw [actualFormalPullback_X]
  exact actualFormalCoordinateImages_mem_variables η hη hη0 i

/-- EVERY whole genuine formal variable power is preserved by the SAME actual substitution. -/
theorem map_variables_pow_actualFormalPullback_le (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0) (q : ℕ) :
    Ideal.map (actualFormalPullback η hη hη0).toRingHom (genuineFormalVariables n ^ q) ≤
      genuineFormalVariables m ^ q := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (map_variables_actualFormalPullback_le η hη hη0) q

/-- EVERY actual polynomial commutes through literal original coordinate evaluation and genuine formal substitution. -/
theorem originalTaylor_polynomial_pullback (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (P : MvPolynomial (Fin n) ℂ) :
    originalTaylorAlgHom m (compAlgHom η hη hη0 (originalPolynomialEval n P))=
      actualFormalPullback η hη hη0 (P : MvPowerSeries (Fin n) ℂ) := by
  have he : ((originalTaylorAlgHom m).comp (compAlgHom η hη hη0)).comp (originalPolynomialEval n)=
      ((actualFormalPullback η hη hη0).comp (originalTaylorAlgHom n)).comp (originalPolynomialEval n) := by
    apply MvPolynomial.algHom_ext
    intro i
    change originalTaylorAlgHom m (compAlgHom η hη hη0 (originalPolynomialEval n (MvPolynomial.X i)))=
      actualFormalPullback η hη hη0 (originalTaylorAlgHom n (originalPolynomialEval n (MvPolynomial.X i)))
    rw [originalPolynomialEval,MvPolynomial.aeval_X,originalTaylorAlgHom_coordinate,actualFormalPullback_X]
    rfl
  have hp := DFunLike.congr_fun he P
  change originalTaylorAlgHom m (compAlgHom η hη hη0 (originalPolynomialEval n P))=
    actualFormalPullback η hη hη0 (originalTaylorAlgHom n (originalPolynomialEval n P)) at hp
  rwa [originalTaylorAlgHom_polynomialEval] at hp

/-- EVERY actual original numerator commutes with genuine Taylor substitution under the ACTUAL holomorphic pullback. -/
theorem originalTaylor_compAlgHom (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorAlgHom m (compAlgHom η hη hη0 g)=
      actualFormalPullback η hη hη0 (originalTaylorAlgHom n g) := by
  apply MvPowerSeries.ext
  intro α
  let k := normalExponentDegree α
  let P := originalTaylorPolynomial n k g
  let e := g-originalPolynomialEval n P
  have he : e ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) :=
    originalTaylorPolynomial_remainder n k g
  have hp := map_maximal_pow_compAlgHom_le η hη hη0 (k+1)
    (Ideal.mem_map_of_mem (compAlgHom η hη hη0).toRingHom he)
  have hTe : originalTaylorAlgHom m (compAlgHom η hη hη0 e) ∈ genuineFormalVariables m ^ (k+1) := by
    have ht := Ideal.mem_map_of_mem (originalTaylorAlgHom m).toRingHom hp
    rw [map_original_maximal_pow_eq_formal_variables_pow] at ht
    exact ht
  have hse : originalTaylorAlgHom n e ∈ genuineFormalVariables n ^ (k+1) := by
    have ht := Ideal.mem_map_of_mem (originalTaylorAlgHom n).toRingHom he
    rw [map_original_maximal_pow_eq_formal_variables_pow] at ht
    exact ht
  have hFe : actualFormalPullback η hη hη0 (originalTaylorAlgHom n e) ∈
      genuineFormalVariables m ^ (k+1) :=
    map_variables_pow_actualFormalPullback_le η hη hη0 (k+1)
      (Ideal.mem_map_of_mem (actualFormalPullback η hη hη0).toRingHom hse)
  have hα : normalExponentDegree α < k+1 := by dsimp [k]; omega
  have h1 := (mem_genuineFormalVariables_pow_iff_coefficients_zero m (k+1) _).mp hTe α hα
  have h2 := (mem_genuineFormalVariables_pow_iff_coefficients_zero m (k+1) _).mp hFe α hα
  have he1 : originalTaylorAlgHom m (compAlgHom η hη hη0 e)=
      originalTaylorAlgHom m (compAlgHom η hη hη0 g)-
        originalTaylorAlgHom m (compAlgHom η hη hη0 (originalPolynomialEval n P)) := by
    dsimp only [e]
    rw [map_sub,map_sub]
  have he2 : actualFormalPullback η hη hη0 (originalTaylorAlgHom n e)=
      actualFormalPullback η hη hη0 (originalTaylorAlgHom n g)-
        actualFormalPullback η hη hη0 (originalTaylorAlgHom n (originalPolynomialEval n P)) := by
    dsimp only [e]
    rw [map_sub,map_sub]
  rw [he1,map_sub,sub_eq_zero] at h1
  rw [he2,map_sub,sub_eq_zero] at h2
  have hpoly := originalTaylor_polynomial_pullback η hη hη0 P
  rw [← originalTaylorAlgHom_polynomialEval n P] at hpoly
  exact h1.trans ((congrArg (MvPowerSeries.coeff α) hpoly).trans h2.symm)

/-- BOTH WHOLE ideal extensions commute through the SAME actual original map and genuine formal substitution. -/
theorem map_whole_original_ideal_formal_pullback (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    Ideal.map (actualFormalPullback η hη hη0).toRingHom (Ideal.map (originalTaylorAlgHom n).toRingHom I)=
      Ideal.map (originalTaylorAlgHom m).toRingHom (Ideal.map (compAlgHom η hη hη0).toRingHom I) := by
  rw [Ideal.map_map,Ideal.map_map]
  apply congrArg (fun f : HolGerm (ComplexModel (0+n)) →+* MvPowerSeries (Fin m) ℂ => Ideal.map f I)
  apply RingHom.ext
  intro g
  exact (originalTaylor_compAlgHom η hη hη0 g).symm

end
end Hironaka.HironakaActualOriginalFormalNaturality
