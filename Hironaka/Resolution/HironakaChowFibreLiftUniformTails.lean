import Hironaka.Resolution.HironakaChowFibreLiftWeightedFactors
import Hironaka.Resolution.HironakaActualInheritedSmallTails

/-! Actual common representatives and bounds for the SAME original fibre
lifts with their unchanged genuine normal weights. No Neumann or division
certificate is an input. Blueprint first; all-germ division remains next. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowFibreLiftUniformTails
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualWeightedScaling HironakaActualWeightedVertexSmallTails
  HironakaActualFiniteDegLexWeights HironakaActualCoefficientPresentationCentrePower
  HironakaChowFibreLiftWeightedFactors HironakaActualJointBaseFibre
  HironakaActualCauchyCoordinateDivision

/- The following elementary joint-coordinate and finite-germ-product formulas
are restated because the inherited mother keeps them private. They receive
zero separate mathematical credit. -/
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

private abbrev fibreIdeal (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  Ideal.map (jointBaseZeroTrace d t).toRingHom I

/-- All actual uniform tail data produced from the ORIGINAL ideal alone. -/
structure FibreLiftUniformTailData (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) where
  fibre : ActualWeightedVertexGermData t (fibreIdeal d t I)
  lift : ActualVertexIndex t (fibreIdeal d t I) → HolGerm (ComplexModel (d+t))
  member_trace : ∀ a, lift a ∈ I ∧ jointBaseZeroTrace d t (lift a) = fibre.generator a
  baseWeight : ℕ
  baseWeight_pos : 0 < baseWeight
  head_lt : ∀ a : ActualVertexIndex t (fibreIdeal d t I),
    weightedDegree (degLexWeight t fibre.degreeBound) a.val < baseWeight
  representative : ActualVertexIndex t (fibreIdeal d t I) → ComplexModel (d+t) → ℂ
  representative_hol : ∀ a, OkaRelationSheaf.HolAt (representative a) 0
  representative_eq : ∀ a, HolGerm.mk (representative a) (representative_hol a) = lift a
  tailFactor : ActualVertexIndex t (fibreIdeal d t I) → CoordinateSpace (d+t) × ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_pos : 0 < bound
  factor_hol : ∀ a, DifferentiableOn ℂ (tailFactor a)
    (ball (0 : CoordinateSpace (d+t)) radius ×ˢ ball (0 : ℂ) radius)
  scaled_hol : ∀ a, DifferentiableOn ℂ
    (fun p : CoordinateSpace (d+t) × ℂ => representative a
      (actualWeightedScalingMap (extendedWeight d t baseWeight (degLexWeight t fibre.degreeBound))
        (jointPoint (d+t) p)))
    (ball (0 : CoordinateSpace (d+t)) radius ×ˢ ball (0 : ℂ) radius)
  factor_bound : ∀ a, ∀ p ∈ ball (0 : CoordinateSpace (d+t)) radius ×ˢ ball (0 : ℂ) radius,
    ‖tailFactor a p‖ ≤ bound
  weighted_identity : ∀ a, ∀ p ∈ ball (0 : CoordinateSpace (d+t)) radius ×ˢ ball (0 : ℂ) radius,
    representative a
      (actualWeightedScalingMap (extendedWeight d t baseWeight (degLexWeight t fibre.degreeBound))
        (jointPoint (d+t) p)) =
      p.2 ^ weightedDegree (degLexWeight t fibre.degreeBound) a.val *
        (coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val) p.1 + p.2 * tailFactor a p)

/-- ONE original fibre family/lift tuple/normal weight and real domain precede all later numerators. -/
theorem exists_original_fibre_lift_uniform_tails (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) : Nonempty (FibreLiftUniformTailData d t I) := by
  obtain ⟨P,F,hF,L,hLpos,hL,hFactors⟩ := exists_original_fibre_lift_weighted_factors d t I
  choose A hA using hFactors
  let w := degLexWeight t P.degreeBound
  let W := extendedWeight d t L w
  choose f hf hfEq using fun a => HolGerm.exists_eq_mk (F a)
  choose B hB hBEq using fun a => HolGerm.exists_eq_mk (A a)
  let Fscaled (a : ActualVertexIndex t (fibreIdeal d t I)) (p : CoordinateSpace (d+t) × ℂ) :=
    f a (actualWeightedScalingMap W (jointPoint (d+t) p))
  let Af (a : ActualVertexIndex t (fibreIdeal d t I)) (p : CoordinateSpace (d+t) × ℂ) :=
    B a (jointPoint (d+t) p)
  have hFscaled (a : ActualVertexIndex t (fibreIdeal d t I)) : OkaRelationSheaf.HolAt (Fscaled a) 0 := by
    have hψ : ∀ᶠ z in nhds (0 : ComplexModel ((d+t)+1)),
        DifferentiableAt ℂ (actualWeightedScalingMap W) z :=
      Eventually.of_forall fun _ => (differentiable_actualWeightedScalingMap W).differentiableAt
    have hψ0 : actualWeightedScalingMap W 0 = 0 := by ext i; simp [actualWeightedScalingMap]
    exact eventually_differentiableAt_comp_clm (jointPoint (d+t))
      (holomorphic_comp (actualWeightedScalingMap W) hψ hψ0 (hf a))
  have hAf (a : ActualVertexIndex t (fibreIdeal d t I)) : OkaRelationSheaf.HolAt (Af a) 0 :=
    eventually_differentiableAt_comp_clm (jointPoint (d+t)) (hB a)
  have hjoint : Tendsto (jointPoint (d+t)) (nhds (0 : CoordinateSpace (d+t) × ℂ))
      (nhds (0 : ComplexModel ((d+t)+1))) := by
    simpa only [map_zero] using (jointPoint (d+t)).continuous.tendsto (0 : CoordinateSpace (d+t) × ℂ)
  have hidentity (a : ActualVertexIndex t (fibreIdeal d t I)) :
      ∀ᶠ p in nhds (0 : CoordinateSpace (d+t) × ℂ),
        Fscaled a p = p.2 ^ weightedDegree w a.val *
          (coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val) p.1 + p.2 * Af a p) := by
    have hHead : weightedDegree W (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val) =
        weightedDegree w a.val := weighted_head d t L w a.val
    have he := hA a
    rw [hfEq a,hBEq a] at he
    unfold actualWeightedScalingPullback at he
    rw [compAlgHom_mk,scaledMonomialGerm_eq_mk] at he
    change HolGerm.mk (f a ∘ actualWeightedScalingMap W) _ -
      HolGerm.mk (scaledMonomialFunction W (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val)) _ =
      (HolGerm.mk (fun z : ComplexModel ((d+t)+1) => z (parameterIndex (d+t))) _) ^
        (weightedDegree w a.val + 1) * HolGerm.mk (B a) _ at he
    rw [← HolGerm.mk_sub,← HolGerm.mk_pow,← HolGerm.mk_mul] at he
    have heq := HolGerm.mk_eq_mk_iff.mp he
    filter_upwards [hjoint.eventually heq] with p hp
    change Fscaled a p - scaledMonomialFunction W
      (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val) (jointPoint (d+t) p) =
        jointPoint (d+t) p (parameterIndex (d+t)) ^ (weightedDegree w a.val + 1) * Af a p at hp
    rw [scaledMonomialFunction_joint,jointPoint_parameter,hHead,pow_succ] at hp
    linear_combination hp
  let C := 1 + ∑ a : ActualVertexIndex t (fibreIdeal d t I), ‖Af a 0‖
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ a : ActualVertexIndex t (fibreIdeal d t I), ‖Af a 0‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    dsimp only [C]
    linarith
  have hBound (a : ActualVertexIndex t (fibreIdeal d t I)) :
      ∀ᶠ p in nhds (0 : CoordinateSpace (d+t) × ℂ), ‖Af a p‖ ≤ C := by
    have ht := (hAf a).self_of_nhds.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖Af a 0‖))
    have hle : ‖Af a 0‖ ≤ ∑ b : ActualVertexIndex t (fibreIdeal d t I), ‖Af b 0‖ :=
      Finset.single_le_sum (f := fun b : ActualVertexIndex t (fibreIdeal d t I) => ‖Af b 0‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    filter_upwards [ht] with p hp
    dsimp only [C]
    linarith
  have hall : ∀ᶠ p in nhds (0 : CoordinateSpace (d+t) × ℂ),
      ∀ a : ActualVertexIndex t (fibreIdeal d t I),
        DifferentiableAt ℂ (Af a) p ∧ DifferentiableAt ℂ (Fscaled a) p ∧
        Fscaled a p = p.2 ^ weightedDegree w a.val *
          (coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val) p.1 + p.2 * Af a p) ∧
        ‖Af a p‖ ≤ C :=
    eventually_all.mpr fun a => (hAf a).and ((hFscaled a).and ((hidentity a).and (hBound a)))
  obtain ⟨R,hR,hallR⟩ := Metric.eventually_nhds_iff_ball.mp hall
  have hProd (p : CoordinateSpace (d+t) × ℂ)
      (hp : p ∈ ball (0 : CoordinateSpace (d+t)) R ×ˢ ball (0 : ℂ) R) : p ∈ ball 0 R := by
    rw [mem_ball_zero_iff,Prod.norm_mk]
    exact max_lt (mem_ball_zero_iff.mp hp.1) (mem_ball_zero_iff.mp hp.2)
  exact ⟨{
    fibre := P
    lift := F
    member_trace := hF
    baseWeight := L
    baseWeight_pos := hLpos
    head_lt := hL
    representative := f
    representative_hol := hf
    representative_eq := fun a => (hfEq a).symm
    tailFactor := Af
    radius := R
    radius_pos := hR
    bound := C
    bound_pos := hC
    factor_hol := fun a p hp => ((hallR p (hProd p hp)) a).1.differentiableWithinAt
    scaled_hol := fun a p hp => ((hallR p (hProd p hp)) a).2.1.differentiableWithinAt
    factor_bound := fun a p hp => ((hallR p (hProd p hp)) a).2.2.2
    weighted_identity := fun a p hp => ((hallR p (hProd p hp)) a).2.2.1 }⟩

end
end Hironaka.HironakaChowFibreLiftUniformTails
