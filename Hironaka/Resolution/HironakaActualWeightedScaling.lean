import Hironaka.Resolution.HironakaActualFiniteDegLexWeights
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-!
# Genuine weighted polynomial scaling and the extra analytic parameter factor

The whole formal coefficient formula and extra parameter power are produced
from literal substitution and actual leading data. Genuine analytic/formal
normal-power contraction then produces the actual analytic factor.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualWeightedScaling

noncomputable section

open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
  HironakaActualFormalCoordinatePowerDivision HironakaActualAnalyticFormalNormalPowers
  HironakaActualFormalInitialDiagram HironakaActualFiniteDegLexWeights

variable {n : ℕ}

def parameterIndex (n : ℕ) : Fin (n+1) := (0 : Fin 1).natAdd n

private theorem parameterIndex_ne_base (i : Fin n) : parameterIndex n ≠ i.castAdd 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [parameterIndex,Fin.val_natAdd,Fin.val_zero,Fin.val_castAdd] at hv
  omega

def weightedExponent (W : Fin n → ℕ) (a : Fin n →₀ ℕ) : Fin (n+1) →₀ ℕ :=
  actualJoinedExponent a (Finsupp.single (0 : Fin 1) (weightedDegree W a))

private theorem weightedExponent_base (W : Fin n → ℕ) (a : Fin n →₀ ℕ) (i : Fin n) :
    weightedExponent W a (i.castAdd 1) = a i := by
  simp [weightedExponent,actualJoinedExponent]

private theorem weightedExponent_parameter (W : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    weightedExponent W a (parameterIndex n) = weightedDegree W a := by
  simp [weightedExponent,actualJoinedExponent,parameterIndex]

private theorem tangent_weightedExponent (W : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    actualTangentExponent (weightedExponent W a) = a := by
  ext i
  simp [actualTangentExponent,weightedExponent_base]

private theorem weightedExponent_eq_of_parameter (W : Fin n → ℕ) (c : Fin (n+1) →₀ ℕ) :
    weightedExponent W (actualTangentExponent c) = c ↔
      c (parameterIndex n) = weightedDegree W (actualTangentExponent c) := by
  constructor
  · intro he
    simpa only [weightedExponent_parameter] using (DFunLike.congr_fun he (parameterIndex n)).symm
  · intro hc
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [weightedExponent_base,actualTangentExponent]
    · have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact (weightedExponent_parameter W _).trans hc.symm

private theorem weightedExponent_eq_sum (W : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    weightedExponent W a = ∑ i : Fin n,
      (Finsupp.single (parameterIndex n) (W i * a i) + Finsupp.single (i.castAdd 1) (a i)) := by
  ext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp [weightedExponent_base,Finsupp.finsetSum_apply,Finsupp.single_apply,
      parameterIndex_ne_base,Fin.castAdd_inj]
  · have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    change weightedExponent W a (parameterIndex n) =
      (∑ i : Fin n, (Finsupp.single (parameterIndex n) (W i * a i) +
        Finsupp.single (i.castAdd 1) (a i))) (parameterIndex n)
    rw [weightedExponent_parameter]
    simp only [Finsupp.finsetSum_apply,Finsupp.add_apply,Finsupp.single_eq_same,
      Finsupp.single_apply,weightedDegree]
    apply Finset.sum_congr rfl
    intro i _
    rw [if_neg (parameterIndex_ne_base i).symm,add_zero]

def weightedFormalCoordinates (W : Fin n → ℕ) (i : Fin n) : MvPowerSeries (Fin (n+1)) ℂ :=
  MvPowerSeries.X (parameterIndex n) ^ W i * MvPowerSeries.X (i.castAdd 1)

private theorem weightedFormalCoordinates_constant_zero (W : Fin n → ℕ) (i : Fin n) :
    MvPowerSeries.constantCoeff (weightedFormalCoordinates W i) = 0 := by
  simp [weightedFormalCoordinates]

def weightedFormalScaling (W : Fin n → ℕ) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin (n+1)) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (weightedFormalCoordinates_constant_zero W))

/-- Genuine finite monomial multiplication produces the entire exponent lift. -/
theorem weightedFormalCoordinates_prod (W : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    a.prod (fun i d => weightedFormalCoordinates W i ^ d) =
      MvPowerSeries.monomial (weightedExponent W a) 1 := by
  rw [a.prod_fintype (fun i d => weightedFormalCoordinates W i ^ d) (fun _ => pow_zero _)]
  simp_rw [weightedFormalCoordinates,mul_pow,← pow_mul,MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial,one_mul]
  rw [MvPowerSeries.prod_monomial]
  simp only [Finset.prod_const_one]
  rw [← weightedExponent_eq_sum]

/-- The formal substitution coefficient is computed internally for EVERY whole exponent. -/
theorem coeff_weightedFormalScaling (W : Fin n → ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (c : Fin (n+1) →₀ ℕ) :
    MvPowerSeries.coeff c (weightedFormalScaling W F) =
      if c (parameterIndex n) = weightedDegree W (actualTangentExponent c)
      then MvPowerSeries.coeff (actualTangentExponent c) F else 0 := by
  rw [weightedFormalScaling,MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (weightedFormalCoordinates_constant_zero W)),
    finsum_eq_single _ (actualTangentExponent c)]
  · rw [weightedFormalCoordinates_prod]
    by_cases hc : c (parameterIndex n) = weightedDegree W (actualTangentExponent c)
    · have he := (weightedExponent_eq_of_parameter W c).mpr hc
      rw [he,MvPowerSeries.coeff_monomial_same,smul_eq_mul,mul_one,if_pos hc]
    · have he : c ≠ weightedExponent W (actualTangentExponent c) := by
        intro he
        exact hc ((weightedExponent_eq_of_parameter W c).mp he.symm)
      rw [MvPowerSeries.coeff_monomial,if_neg he,smul_zero,if_neg hc]
  · intro b hb
    rw [weightedFormalCoordinates_prod]
    have hne : c ≠ weightedExponent W b := by
      intro he
      have ht := congrArg actualTangentExponent he
      rw [tangent_weightedExponent] at ht
      exact hb ht.symm
    rw [MvPowerSeries.coeff_monomial,if_neg hne,smul_zero]

def actualWeightedScalingMap (W : Fin n → ℕ) : ComplexModel (n+1) → ComplexModel n :=
  fun z => (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => z (parameterIndex n) ^ W i * z (i.castAdd 1))

theorem differentiable_actualWeightedScalingMap (W : Fin n → ℕ) :
    Differentiable ℂ (actualWeightedScalingMap W) := by
  have hp (i : Fin (n+1)) : Differentiable ℂ (fun z : ComplexModel (n+1) => z i) :=
    (EuclideanSpace.proj i : ComplexModel (n+1) →L[ℂ] ℂ).differentiable
  exact (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.differentiable.comp
    (differentiable_pi.mpr fun i => ((hp (parameterIndex n)).pow (W i)).mul (hp (i.castAdd 1)))

private theorem actualWeightedScalingMap_zero (W : Fin n → ℕ) :
    actualWeightedScalingMap W 0 = 0 := by
  ext i
  simp [actualWeightedScalingMap]

def actualWeightedScalingPullback (W : Fin n → ℕ) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel (n+1)) :=
  compAlgHom (actualWeightedScalingMap W)
    (Eventually.of_forall fun _ => (differentiable_actualWeightedScalingMap W).differentiableAt)
    (actualWeightedScalingMap_zero W)

theorem actualWeightedScalingPullback_coordinate (W : Fin n → ℕ) (i : Fin n) :
    actualWeightedScalingPullback W (coordinateGerm i) =
      coordinateGerm (parameterIndex n) ^ W i * coordinateGerm (i.castAdd 1) := by
  unfold actualWeightedScalingPullback coordinateGerm
  rw [compAlgHom_mk]
  have hp : OkaRelationSheaf.HolAt (fun z : ComplexModel (n+1) => z (parameterIndex n)) 0 :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (parameterIndex n) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt
  have hb : OkaRelationSheaf.HolAt (fun z : ComplexModel (n+1) => z (i.castAdd 1)) 0 :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (i.castAdd 1) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt
  change HolGerm.mk (fun z : ComplexModel (n+1) => z (parameterIndex n) ^ W i * z (i.castAdd 1))
    (eventually_differentiableAt_mul (eventually_differentiableAt_pow hp (W i)) hb) = _
  rw [HolGerm.mk_mul _ _ (eventually_differentiableAt_pow hp (W i)) hb,HolGerm.mk_pow _ hp (W i)]

theorem actualTaylor_weightedScalingPullback (W : Fin n → ℕ) :
    (actualUnshiftedTaylorAlgHom (n+1)).comp (actualWeightedScalingPullback W) =
      (weightedFormalScaling W).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro i
    change actualUnshiftedTaylorAlgHom (n+1) (actualWeightedScalingPullback W (coordinateGerm i)) =
      weightedFormalScaling W (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
    rw [actualWeightedScalingPullback_coordinate,map_mul,map_pow,
      actualUnshiftedTaylor_coordinate,actualUnshiftedTaylor_coordinate,
      actualUnshiftedTaylor_coordinate]
    exact (MvPowerSeries.substAlgHom_X (R := ℂ)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (weightedFormalCoordinates_constant_zero W)) i).symm
  · intro i
    change actualUnshiftedTaylorAlgHom (n+1) (actualWeightedScalingPullback W (coordinateGerm i)) ∈ _
    rw [actualWeightedScalingPullback_coordinate,map_mul,map_pow,
      actualUnshiftedTaylor_coordinate,actualUnshiftedTaylor_coordinate]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i.castAdd 1,mem_univ _,rfl⟩)

/-- Ordinary actual initial-exponent data, not a supplied tail support, produce the extra S power. -/
theorem weightedFormalTail_divisible (M : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ≠ 0) (a : Fin n →₀ ℕ)
    (hinit : actualInitialExponent MonomialOrder.degLex F hF = a)
    (hmonic : MvPowerSeries.coeff a F = 1) (hdeg : normalExponentDegree a ≤ M) :
    (MvPowerSeries.X (parameterIndex n) : MvPowerSeries (Fin (n+1)) ℂ) ^
      (weightedDegree (degLexWeight n M) a + 1) ∣
        weightedFormalScaling (degLexWeight n M) F -
          MvPowerSeries.monomial (weightedExponent (degLexWeight n M) a) 1 := by
  let W := degLexWeight n M
  apply MvPowerSeries.X_pow_dvd_iff.mpr
  intro c hc
  change c (parameterIndex n) < weightedDegree W a + 1 at hc
  rw [map_sub,coeff_weightedFormalScaling]
  by_cases hmatch : c (parameterIndex n) = weightedDegree W (actualTangentExponent c)
  · rw [if_pos hmatch]
    rcases lt_trichotomy (MonomialOrder.degLex.toSyn (actualTangentExponent c))
      (MonomialOrder.degLex.toSyn a) with hlt | heq | hgt
    · have hlower : MvPowerSeries.coeff (actualTangentExponent c) F = 0 := by
        apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex F hF
        simpa only [hinit] using hlt
      have hne : c ≠ weightedExponent W a := by
        intro he
        have ht := congrArg actualTangentExponent he
        rw [tangent_weightedExponent] at ht
        exact (ne_of_lt hlt) (congrArg MonomialOrder.degLex.toSyn ht)
      rw [hlower,MvPowerSeries.coeff_monomial,if_neg hne,sub_self]
    · have he : actualTangentExponent c = a := MonomialOrder.degLex.toSyn.injective heq
      have hceq : c = weightedExponent W a := by
        rw [← he]
        exact ((weightedExponent_eq_of_parameter W c).mpr hmatch).symm
      rw [he,hmonic,hceq,MvPowerSeries.coeff_monomial_same,sub_self]
    · have hw := weightedDegree_strict_of_degLex M a (actualTangentExponent c) hdeg hgt
      change weightedDegree W a < weightedDegree W (actualTangentExponent c) at hw
      omega
  · rw [if_neg hmatch]
    have hne : c ≠ weightedExponent W a := by
      intro he
      apply hmatch
      rw [he,weightedExponent_parameter,tangent_weightedExponent]
    rw [MvPowerSeries.coeff_monomial,if_neg hne,sub_self]

def actualScaledMonomialGerm (W : Fin n → ℕ) (a : Fin n →₀ ℕ) : HolGerm (ComplexModel (n+1)) :=
  ∏ i : Fin n, (coordinateGerm (parameterIndex n) ^ W i * coordinateGerm (i.castAdd 1)) ^ a i

theorem actualTaylor_scaledMonomialGerm (W : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    actualUnshiftedTaylorAlgHom (n+1) (actualScaledMonomialGerm W a) =
      MvPowerSeries.monomial (weightedExponent W a) 1 := by
  rw [actualScaledMonomialGerm,map_prod]
  simp only [map_pow,map_mul,actualUnshiftedTaylor_coordinate]
  change (∏ i : Fin n, weightedFormalCoordinates W i ^ a i) = _
  rw [← a.prod_fintype (fun i d => weightedFormalCoordinates W i ^ d) (fun _ => pow_zero _)]
  exact weightedFormalCoordinates_prod W a

private theorem formalParameterIdeal_eq :
    actualFormalCoordinateIdeal (n+1) (actualTangentCentreVariables n 1) =
      Ideal.span {(MvPowerSeries.X (parameterIndex n) : MvPowerSeries (Fin (n+1)) ℂ)} := by
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨j,⟨i,rfl⟩,rfl⟩
    apply Set.mem_singleton_iff.mpr
    exact congrArg (fun i : Fin 1 => (MvPowerSeries.X (i.natAdd n) : MvPowerSeries (Fin (n+1)) ℂ))
      (Subsingleton.elim i 0)
  · intro hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact ⟨parameterIndex n,⟨0,rfl⟩,rfl⟩

private theorem analyticParameterIdeal_eq :
    normalIdeal n 1 = Ideal.span {(coordinateGerm (parameterIndex n) : HolGerm (ComplexModel (n+1)))} := by
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    apply Set.mem_singleton_iff.mpr
    exact congrArg (normalCoordinate n 1) (Subsingleton.elim i 0)
  · intro hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact ⟨0,rfl⟩

/-- The extra formal parameter power contracts to an actual analytic factor; no desired factor is an input. -/
theorem exists_actualWeightedTail_factor (M : ℕ) (g : HolGerm (ComplexModel n))
    (hne : actualUnshiftedTaylorAlgHom n g ≠ 0) (a : Fin n →₀ ℕ)
    (hinit : actualInitialExponent MonomialOrder.degLex (actualUnshiftedTaylorAlgHom n g) hne = a)
    (hmonic : MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n g) = 1)
    (hdeg : normalExponentDegree a ≤ M) :
    ∃ A : HolGerm (ComplexModel (n+1)),
      actualWeightedScalingPullback (degLexWeight n M) g - actualScaledMonomialGerm (degLexWeight n M) a =
        coordinateGerm (parameterIndex n) ^ (weightedDegree (degLexWeight n M) a + 1) * A := by
  let W := degLexWeight n M
  let H := actualWeightedScalingPullback W g - actualScaledMonomialGerm W a
  have hmap := congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ]
      MvPowerSeries (Fin (n+1)) ℂ => f g) (actualTaylor_weightedScalingPullback W)
  change actualUnshiftedTaylorAlgHom (n+1) (actualWeightedScalingPullback W g) =
    weightedFormalScaling W (actualUnshiftedTaylorAlgHom n g) at hmap
  have hformal : actualUnshiftedTaylorAlgHom (n+1) H ∈
      actualFormalCoordinateIdeal (n+1) (actualTangentCentreVariables n 1) ^ (weightedDegree W a + 1) := by
    rw [formalParameterIdeal_eq,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
    dsimp only [H]
    rw [map_sub,hmap,actualTaylor_scaledMonomialGerm]
    exact weightedFormalTail_divisible M _ hne a hinit hmonic hdeg
  have hanalytic := (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow
    n 1 (weightedDegree W a + 1) H).mpr hformal
  rw [analyticParameterIdeal_eq,Ideal.span_singleton_pow] at hanalytic
  obtain ⟨A,hA⟩ := Ideal.mem_span_singleton'.mp hanalytic
  refine ⟨A,?_⟩
  change H = coordinateGerm (parameterIndex n) ^ (weightedDegree W a + 1) * A
  simpa only [mul_comm] using hA.symm

end

end Hironaka.HironakaActualWeightedScaling
