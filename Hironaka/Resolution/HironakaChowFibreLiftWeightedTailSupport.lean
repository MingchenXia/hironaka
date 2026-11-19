import Hironaka.Resolution.HironakaChowFibreLiftUniformTails

/-! Strict whole weighted Taylor support for the SAME actual original lifts.
The genuine product-ball identity supplies the analytic factor internally.
No support, continuity, or extended-ideal certificate is an input. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowFibreLiftWeightedTailSupport
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualWeightedScaling HironakaActualWeightedVertexSmallTails
  HironakaActualFiniteDegLexWeights HironakaActualCoefficientPresentationCentrePower
  HironakaChowFibreLiftWeightedFactors HironakaActualJointBaseFibre
  HironakaActualCauchyCoordinateDivision HironakaChowFibreLiftUniformTails

/- Elementary finite-coordinate and germ-product readbacks are private,
reused verbatim from the inherited uniform-tail mother at zero extra credit. -/
private theorem jointPoint_base {n : ℕ} (p : CoordinateSpace n × ℂ) (i : Fin n) :
    jointPoint n p (i.castAdd 1) = p.1 i := by
  change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
    (fun j : Fin n => (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
    (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) (i.castAdd 1)) p = p.1 i
  rw [Fin.addCases_left]
  rfl

private theorem jointPoint_parameter {n : ℕ} (p : CoordinateSpace n × ℂ) :
    jointPoint n p (parameterIndex n) = p.2 := by
  change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
    (fun j : Fin n => (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
    (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) ((0 : Fin 1).natAdd n)) p = p.2
  rw [Fin.addCases_right]
  rfl

private def scaledMonomialFunction {n : ℕ} (W : Fin n → ℕ) (a : Fin n →₀ ℕ)
    (z : ComplexModel (n+1)) : ℂ :=
  ∏ i : Fin n, (z (parameterIndex n) ^ W i * z (i.castAdd 1)) ^ a i

private theorem differentiable_scaledMonomialFunction {n : ℕ} (W : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    Differentiable ℂ (scaledMonomialFunction W a) := by
  intro z
  exact (HasFDerivAt.finsetProd (u := Finset.univ) fun i _ =>
    ((((EuclideanSpace.proj (parameterIndex n) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt.pow (W i)).mul
      (EuclideanSpace.proj (i.castAdd 1) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt).pow (a i)).hasFDerivAt).differentiableAt

private theorem holAt_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i, OkaRelationSheaf.HolAt (f i) 0) :
    OkaRelationSheaf.HolAt (fun z => ∏ i ∈ s, f i z) 0 := by
  classical
  exact ((eventually_all_finset s).mpr fun i _ => hf i).mono fun _ h =>
    (HasFDerivAt.finsetProd (u := s) fun i hi => (h i hi).hasFDerivAt).differentiableAt

private theorem mk_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i, OkaRelationSheaf.HolAt (f i) 0) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (holAt_prod s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk,SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have he := map_prod (Germ.coeRingHom (nhds (0 : E)) : (E → ℂ) →+* Germ (nhds (0 : E)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at he
  rw [← he,Finset.prod_fn]

private theorem scaledMonomialGerm_eq_mk {n : ℕ} (W : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    actualScaledMonomialGerm W a = HolGerm.mk (scaledMonomialFunction W a)
      (Eventually.of_forall fun _ => (differentiable_scaledMonomialFunction W a).differentiableAt) := by
  have ht (i : Fin n) : OkaRelationSheaf.HolAt
      (fun z : ComplexModel (n+1) => (z (parameterIndex n) ^ W i * z (i.castAdd 1)) ^ a i) 0 :=
    Eventually.of_forall fun z =>
      (((EuclideanSpace.proj (parameterIndex n) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt.pow (W i)).mul
        (EuclideanSpace.proj (i.castAdd 1) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt).pow (a i)
  change _ = HolGerm.mk (fun z : ComplexModel (n+1) =>
    ∏ i : Fin n, (z (parameterIndex n) ^ W i * z (i.castAdd 1)) ^ a i) _
  rw [mk_prod Finset.univ _ ht]
  apply Finset.prod_congr rfl
  intro i _
  have hp : OkaRelationSheaf.HolAt (fun z : ComplexModel (n+1) => z (parameterIndex n)) 0 :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (parameterIndex n) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt
  have hb : OkaRelationSheaf.HolAt (fun z : ComplexModel (n+1) => z (i.castAdd 1)) 0 :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (i.castAdd 1) : ComplexModel (n+1) →L[ℂ] ℂ).differentiableAt
  rw [HolGerm.mk_pow _ (eventually_differentiableAt_mul (eventually_differentiableAt_pow hp (W i)) hb) (a i),
    HolGerm.mk_mul _ _ (eventually_differentiableAt_pow hp (W i)) hb,HolGerm.mk_pow _ hp (W i)]
  rfl

private theorem scaledMonomialFunction_joint {n : ℕ} (W : Fin n → ℕ) (a : Fin n →₀ ℕ)
    (p : CoordinateSpace n × ℂ) :
    scaledMonomialFunction W a (jointPoint n p) = p.2 ^ weightedDegree W a * coordinateMonomial a p.1 := by
  simp only [scaledMonomialFunction,jointPoint_parameter,jointPoint_base,mul_pow,← pow_mul]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rfl


private theorem weighted_head (d t L : ℕ) (w : Fin t → ℕ) (a : Fin t →₀ ℕ) :
    weightedDegree (extendedWeight d t L w) (actualJoinedExponent (0 : Fin d →₀ ℕ) a) =
      weightedDegree w a := by
  simp [weightedDegree, Fin.sum_univ_add, extendedWeight, actualJoinedExponent]

private def jointCoordinates (n : ℕ) :
    ComplexModel (n+1) →L[ℂ] CoordinateSpace n × ℂ :=
  (ContinuousLinearMap.pi fun i : Fin n =>
    (EuclideanSpace.proj (i.castAdd 1) : ComplexModel (n+1) →L[ℂ] ℂ)).prod
    (EuclideanSpace.proj (parameterIndex n) : ComplexModel (n+1) →L[ℂ] ℂ)

private theorem jointPoint_jointCoordinates (n : ℕ) (z : ComplexModel (n+1)) :
    jointPoint n (jointCoordinates n z) = z := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [jointPoint_base]
    rfl
  · have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [show (0 : Fin 1).natAdd n = parameterIndex n from rfl, jointPoint_parameter]
    rfl

private theorem exists_same_lift_parameter_factor {d t : ℕ}
    {I : Ideal (HolGerm (ComplexModel (d+t)))}
    (P : FibreLiftUniformTailData d t I)
    (a : ActualVertexIndex t (Ideal.map (jointBaseZeroTrace d t).toRingHom I)) :
    let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
    let head := actualJoinedExponent (0 : Fin d →₀ ℕ) a.val
    ∃ B : HolGerm (ComplexModel ((d+t)+1)),
      actualWeightedScalingPullback W (P.lift a) - actualScaledMonomialGerm W head =
        coordinateGerm (parameterIndex (d+t)) ^ (weightedDegree W head + 1) * B := by
  let n := d+t
  let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
  let head := actualJoinedExponent (0 : Fin d →₀ ℕ) a.val
  let V := ball (0 : CoordinateSpace n) P.radius ×ˢ ball (0 : ℂ) P.radius
  have hVopen : IsOpen V := isOpen_ball.prod isOpen_ball
  have hV0 : (0 : CoordinateSpace n × ℂ) ∈ V := by
    exact ⟨mem_ball_self P.radius_pos, mem_ball_self P.radius_pos⟩
  have hV : V ∈ nhds (0 : CoordinateSpace n × ℂ) := hVopen.mem_nhds hV0
  have hBhol : OkaRelationSheaf.HolAt (P.tailFactor a) 0 := by
    filter_upwards [hV] with p hp
    exact (P.factor_hol a p hp).differentiableAt (hVopen.mem_nhds hp)
  let Bfun : ComplexModel (n+1) → ℂ := P.tailFactor a ∘ jointCoordinates n
  have hBh : OkaRelationSheaf.HolAt Bfun 0 :=
    eventually_differentiableAt_comp_clm (jointCoordinates n) hBhol
  refine ⟨HolGerm.mk Bfun hBh, ?_⟩
  change actualWeightedScalingPullback W (P.lift a) - actualScaledMonomialGerm W head =
    coordinateGerm (parameterIndex n) ^ (weightedDegree W head + 1) * HolGerm.mk Bfun hBh
  rw [← P.representative_eq a]
  unfold actualWeightedScalingPullback
  rw [compAlgHom_mk, scaledMonomialGerm_eq_mk]
  change HolGerm.mk (P.representative a ∘ actualWeightedScalingMap W) _ -
    HolGerm.mk (scaledMonomialFunction W head) _ =
    (HolGerm.mk (fun z : ComplexModel (n+1) => z (parameterIndex n)) _) ^
      (weightedDegree W head + 1) * HolGerm.mk Bfun hBh
  rw [← HolGerm.mk_sub, ← HolGerm.mk_pow, ← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hj : Tendsto (jointCoordinates n) (nhds (0 : ComplexModel (n+1)))
      (nhds (0 : CoordinateSpace n × ℂ)) := by
    simpa only [map_zero] using (jointCoordinates n).continuous.tendsto (0 : ComplexModel (n+1))
  filter_upwards [hj.eventually hV] with z hz
  have he := P.weighted_identity a (jointCoordinates n z) hz
  rw [jointPoint_jointCoordinates] at he
  have hs := scaledMonomialFunction_joint W head (jointCoordinates n z)
  rw [jointPoint_jointCoordinates] at hs
  have hhead : weightedDegree W head =
      weightedDegree (degLexWeight t P.fibre.degreeBound) a.val :=
    weighted_head d t P.baseWeight _ a.val
  change P.representative a (actualWeightedScalingMap W z) - scaledMonomialFunction W head z =
    z (parameterIndex n) ^ (weightedDegree W head + 1) * Bfun z
  rw [hs, hhead, pow_succ]
  change P.representative a (actualWeightedScalingMap W z) -
      (jointCoordinates n z).2 ^ weightedDegree (degLexWeight t P.fibre.degreeBound) a.val *
        coordinateMonomial head (jointCoordinates n z).1 =
    (jointCoordinates n z).2 ^ weightedDegree (degLexWeight t P.fibre.degreeBound) a.val *
      (jointCoordinates n z).2 * P.tailFactor a (jointCoordinates n z)
  linear_combination he

private theorem tangent_weightedExponent {n : ℕ} (W : Fin n → ℕ) (β : Fin n →₀ ℕ) :
    actualTangentExponent (weightedExponent W β) = β := by
  ext i
  simp [actualTangentExponent, weightedExponent, actualJoinedExponent]

private theorem parameter_weightedExponent {n : ℕ} (W : Fin n → ℕ) (β : Fin n →₀ ℕ) :
    weightedExponent W β (parameterIndex n) = weightedDegree W β := by
  simp [weightedExponent, actualJoinedExponent, parameterIndex]

private theorem weightedExponent_injective {n : ℕ} (W : Fin n → ℕ) :
    Function.Injective (weightedExponent W) := by
  intro a b h
  simpa only [tangent_weightedExponent] using congrArg actualTangentExponent h

private theorem coeff_tail_eq_zero_of_parameter_factor {n : ℕ}
    (W : Fin n → ℕ) (F : HolGerm (ComplexModel n)) (head β : Fin n →₀ ℕ)
    (hβ : weightedDegree W β ≤ weightedDegree W head)
    (hFactor : ∃ B : HolGerm (ComplexModel (n+1)),
      actualWeightedScalingPullback W F - actualScaledMonomialGerm W head =
        coordinateGerm (parameterIndex n) ^ (weightedDegree W head + 1) * B) :
    MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n F - MvPowerSeries.monomial head 1) = 0 := by
  obtain ⟨B,hB⟩ := hFactor
  have hscale := DFunLike.congr_fun (actualTaylor_weightedScalingPullback W) F
  change actualUnshiftedTaylorAlgHom (n+1) (actualWeightedScalingPullback W F) =
    weightedFormalScaling W (actualUnshiftedTaylorAlgHom n F) at hscale
  have hformal := congrArg (actualUnshiftedTaylorAlgHom (n+1)) hB
  rw [map_sub, hscale, actualTaylor_scaledMonomialGerm, map_mul, map_pow,
    actualUnshiftedTaylor_coordinate] at hformal
  have hdiv : (MvPowerSeries.X (parameterIndex n) : MvPowerSeries (Fin (n+1)) ℂ) ^
      (weightedDegree W head + 1) ∣
      weightedFormalScaling W (actualUnshiftedTaylorAlgHom n F) -
        MvPowerSeries.monomial (weightedExponent W head) 1 := ⟨_,hformal⟩
  have hlt : weightedExponent W β (parameterIndex n) < weightedDegree W head + 1 := by
    rw [parameter_weightedExponent]
    omega
  have hz := MvPowerSeries.X_pow_dvd_iff.mp hdiv (weightedExponent W β) hlt
  rw [map_sub, coeff_weightedFormalScaling, tangent_weightedExponent,
    parameter_weightedExponent, if_pos rfl] at hz
  by_cases he : β = head
  · subst β
    simpa only [map_sub, MvPowerSeries.coeff_monomial_same] using hz
  · have hne : weightedExponent W β ≠ weightedExponent W head :=
      fun h => he (weightedExponent_injective W h)
    simpa only [map_sub, MvPowerSeries.coeff_monomial, if_neg he, if_neg hne, sub_zero] using hz

/-- Every full joint coefficient of the SAME lift tail below or at its head weight vanishes. -/
theorem coeff_lift_tail_eq_zero_of_weight_le {d t : ℕ}
    {I : Ideal (HolGerm (ComplexModel (d+t)))}
    (P : FibreLiftUniformTailData d t I)
    (a : ActualVertexIndex t (Ideal.map (jointBaseZeroTrace d t).toRingHom I))
    (β : Fin (d+t) →₀ ℕ)
    (hβ : weightedDegree (extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)) β ≤
      weightedDegree (extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound))
        (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val)) :
    MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (P.lift a) -
      MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val) 1) = 0 := by
  exact coeff_tail_eq_zero_of_parameter_factor _ _ _ _ hβ (exists_same_lift_parameter_factor P a)

end
end Hironaka.HironakaChowFibreLiftWeightedTailSupport
