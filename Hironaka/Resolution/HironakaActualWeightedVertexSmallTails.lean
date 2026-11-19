import Hironaka.Resolution.HironakaActualWeightedScaling
import Hironaka.Resolution.HironakaActualAnalyticCentreVertexFamily
import Hironaka.Resolution.HironakaActualCauchyCoordinateDivision

/-!
# Actual weighted small tails produced from the original analytic ideal

The only input to the final producer is the original analytic ideal. The real
analytic vertex family, true finite diagram bound, positive integer weights,
actual joint factors, representatives, common domain and uniform tail bound
are produced internally. No desired tail/support/convergence input occurs.
-/

set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualWeightedVertexSmallTails

noncomputable section

open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedFormalStandardBasis HironakaActualAnalyticCentreVertexFamily
  HironakaActualFiniteDegLexWeights HironakaActualWeightedScaling HironakaActualCauchyCoordinateDivision

abbrev ActualVertexIndex (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :=
  {a : Fin n →₀ ℕ // a ∈ actualInitialVertices MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)}

structure ActualWeightedVertexGermData (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) where
  degreeBound : ℕ
  degree_le : ∀ a : ActualVertexIndex n I, normalExponentDegree a.val ≤ degreeBound
  generator : ActualVertexIndex n I → HolGerm (ComplexModel n)
  member : ∀ a, generator a ∈ I
  nonzero : ∀ a, actualUnshiftedTaylorAlgHom n (generator a) ≠ 0
  initial : ∀ a, actualInitialExponent MonomialOrder.degLex
    (actualUnshiftedTaylorAlgHom n (generator a)) (nonzero a) = a.val
  monic : ∀ a, MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (generator a)) = 1
  generates : Ideal.span (range generator) = I
  factor : ActualVertexIndex n I → HolGerm (ComplexModel (n+1))
  factor_spec : ∀ a, actualWeightedScalingPullback (degLexWeight n degreeBound) (generator a) -
      actualScaledMonomialGerm (degLexWeight n degreeBound) a.val =
    coordinateGerm (parameterIndex n) ^ (weightedDegree (degLexWeight n degreeBound) a.val + 1) * factor a

/-- The actual analytic family, true degree bound and actual joint factors all come from I. -/
theorem nonempty_actualWeightedVertexGermData (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    Nonempty (ActualWeightedVertexGermData n I) := by
  let J := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  have hempty (a : actualInitialVertices MonomialOrder.degLex J) :
      actualReducedVertexSeries MonomialOrder.degLex J a ∈ actualFormalCoordinateIdeal n ∅ ^
        Finsupp.weight (actualCoordinateWeight ∅) a.val := by
    simp [actualCoordinateWeight,Finsupp.weight_eq_sum]
  obtain ⟨G,hG,hspan⟩ := exists_actual_analytic_centre_vertex_family n I ∅ hempty
  let M := ∑ a : ActualVertexIndex n I, normalExponentDegree a.val
  have hdeg (a : ActualVertexIndex n I) : normalExponentDegree a.val ≤ M :=
    Finset.single_le_sum
      (f := fun b : ActualVertexIndex n I => normalExponentDegree b.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  choose A hA using fun a : ActualVertexIndex n I =>
    exists_actualWeightedTail_factor M (G a) (hG a).2.2.choose a.val
      (hG a).2.2.choose_spec.1 (hG a).2.2.choose_spec.2 (hdeg a)
  exact ⟨{
    degreeBound := M
    degree_le := hdeg
    generator := G
    member := fun a => (hG a).1
    nonzero := fun a => (hG a).2.2.choose
    initial := fun a => (hG a).2.2.choose_spec.1
    monic := fun a => (hG a).2.2.choose_spec.2
    generates := hspan
    factor := A
    factor_spec := hA }⟩

/-- The genuine continuous-linear joint coordinate map from the Cauchy product model. -/
def jointPoint (n : ℕ) : CoordinateSpace n × ℂ →L[ℂ] ComplexModel (n+1) :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin (n+1))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Fin.addCases
      (fun i : Fin n => (ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ)))

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

def coordinateMonomial {n : ℕ} (a : Fin n →₀ ℕ) (z : CoordinateSpace n) : ℂ :=
  ∏ i, z i ^ a i

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

structure ActualWeightedVertexSmallTailData (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) where
  germs : ActualWeightedVertexGermData n I
  representative : ActualVertexIndex n I → ComplexModel n → ℂ
  representative_hol : ∀ a, OkaRelationSheaf.HolAt (representative a) 0
  representative_eq : ∀ a, HolGerm.mk (representative a) (representative_hol a) = germs.generator a
  tailFactor : ActualVertexIndex n I → CoordinateSpace n × ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_pos : 0 < bound
  factor_hol : ∀ a, DifferentiableOn ℂ (tailFactor a)
    (ball (0 : CoordinateSpace n) radius ×ˢ ball (0 : ℂ) radius)
  scaled_hol : ∀ a, DifferentiableOn ℂ
    (fun p : CoordinateSpace n × ℂ => representative a
      (actualWeightedScalingMap (degLexWeight n germs.degreeBound) (jointPoint n p)))
    (ball (0 : CoordinateSpace n) radius ×ˢ ball (0 : ℂ) radius)
  factor_bound : ∀ a, ∀ p ∈ ball (0 : CoordinateSpace n) radius ×ˢ ball (0 : ℂ) radius,
    ‖tailFactor a p‖ ≤ bound
  weighted_identity : ∀ a, ∀ p ∈ ball (0 : CoordinateSpace n) radius ×ˢ ball (0 : ℂ) radius,
    representative a (actualWeightedScalingMap (degLexWeight n germs.degreeBound) (jointPoint n p)) =
      p.2 ^ weightedDegree (degLexWeight n germs.degreeBound) a.val *
        (coordinateMonomial a.val p.1 + p.2 * tailFactor a p)

private theorem mem_joint_ball_of_product {n : ℕ} {r : ℝ} {p : CoordinateSpace n × ℂ}
    (hp : p ∈ ball (0 : CoordinateSpace n) r ×ˢ ball (0 : ℂ) r) : p ∈ ball 0 r := by
  rw [mem_ball_zero_iff,Prod.norm_mk]
  exact max_lt (mem_ball_zero_iff.mp hp.1) (mem_ball_zero_iff.mp hp.2)

/-- The original ideal alone produces the actual representatives, one domain and a uniform bound. -/
theorem nonempty_actualWeightedVertexSmallTailData (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    Nonempty (ActualWeightedVertexSmallTailData n I) := by
  obtain ⟨P⟩ := nonempty_actualWeightedVertexGermData n I
  let W := degLexWeight n P.degreeBound
  choose g hg hgEq using fun a => HolGerm.exists_eq_mk (P.generator a)
  choose A hA hAEq using fun a => HolGerm.exists_eq_mk (P.factor a)
  let F (a : ActualVertexIndex n I) (p : CoordinateSpace n × ℂ) :=
    g a (actualWeightedScalingMap W (jointPoint n p))
  let Af (a : ActualVertexIndex n I) (p : CoordinateSpace n × ℂ) := A a (jointPoint n p)
  have hF (a : ActualVertexIndex n I) : OkaRelationSheaf.HolAt (F a) 0 := by
    have hψ : ∀ᶠ z in nhds (0 : ComplexModel (n+1)), DifferentiableAt ℂ (actualWeightedScalingMap W) z :=
      Eventually.of_forall fun _ => (differentiable_actualWeightedScalingMap W).differentiableAt
    have hψ0 : actualWeightedScalingMap W 0 = 0 := by ext i; simp [actualWeightedScalingMap]
    exact eventually_differentiableAt_comp_clm (jointPoint n)
      (holomorphic_comp (actualWeightedScalingMap W) hψ hψ0 (hg a))
  have hAf (a : ActualVertexIndex n I) : OkaRelationSheaf.HolAt (Af a) 0 :=
    eventually_differentiableAt_comp_clm (jointPoint n) (hA a)
  have hjoint : Tendsto (jointPoint n) (nhds (0 : CoordinateSpace n × ℂ))
      (nhds (0 : ComplexModel (n+1))) := by
    simpa only [map_zero] using (jointPoint n).continuous.tendsto (0 : CoordinateSpace n × ℂ)
  have hidentity (a : ActualVertexIndex n I) : ∀ᶠ p in nhds (0 : CoordinateSpace n × ℂ),
      F a p = p.2 ^ weightedDegree W a.val * (coordinateMonomial a.val p.1 + p.2 * Af a p) := by
    have he := P.factor_spec a
    rw [hgEq a,hAEq a] at he
    unfold actualWeightedScalingPullback at he
    rw [compAlgHom_mk,scaledMonomialGerm_eq_mk] at he
    change HolGerm.mk (g a ∘ actualWeightedScalingMap W) _ -
      HolGerm.mk (scaledMonomialFunction W a.val) _ =
      (HolGerm.mk (fun z : ComplexModel (n+1) => z (parameterIndex n)) _) ^
        (weightedDegree W a.val + 1) * HolGerm.mk (A a) _ at he
    rw [← HolGerm.mk_sub,← HolGerm.mk_pow,← HolGerm.mk_mul] at he
    have heq := HolGerm.mk_eq_mk_iff.mp he
    filter_upwards [hjoint.eventually heq] with p hp
    change F a p - scaledMonomialFunction W a.val (jointPoint n p) =
      jointPoint n p (parameterIndex n) ^ (weightedDegree W a.val + 1) * Af a p at hp
    rw [scaledMonomialFunction_joint,jointPoint_parameter,pow_succ] at hp
    linear_combination hp
  let B := 1 + ∑ a : ActualVertexIndex n I, ‖Af a 0‖
  have hB : 0 < B := by
    have hs : 0 ≤ ∑ a : ActualVertexIndex n I, ‖Af a 0‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    dsimp only [B]
    linarith
  have hlocalBound (a : ActualVertexIndex n I) : ∀ᶠ p in nhds (0 : CoordinateSpace n × ℂ), ‖Af a p‖ ≤ B := by
    have ht := (hAf a).self_of_nhds.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖Af a 0‖))
    have hle : ‖Af a 0‖ ≤ ∑ b : ActualVertexIndex n I, ‖Af b 0‖ :=
      Finset.single_le_sum (f := fun b : ActualVertexIndex n I => ‖Af b 0‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    filter_upwards [ht] with p hp
    dsimp only [B]
    linarith
  have hall : ∀ᶠ p in nhds (0 : CoordinateSpace n × ℂ), ∀ a : ActualVertexIndex n I,
      DifferentiableAt ℂ (Af a) p ∧ DifferentiableAt ℂ (F a) p ∧
      F a p = p.2 ^ weightedDegree W a.val * (coordinateMonomial a.val p.1 + p.2 * Af a p) ∧ ‖Af a p‖ ≤ B :=
    eventually_all.mpr fun a => (hAf a).and ((hF a).and ((hidentity a).and (hlocalBound a)))
  obtain ⟨r,hr,hrall⟩ := Metric.eventually_nhds_iff_ball.mp hall
  exact ⟨{
    germs := P
    representative := g
    representative_hol := hg
    representative_eq := fun a => (hgEq a).symm
    tailFactor := Af
    radius := r
    radius_pos := hr
    bound := B
    bound_pos := hB
    factor_hol := fun a p hp => ((hrall p (mem_joint_ball_of_product hp)) a).1.differentiableWithinAt
    scaled_hol := fun a p hp => ((hrall p (mem_joint_ball_of_product hp)) a).2.1.differentiableWithinAt
    factor_bound := fun a p hp => ((hrall p (mem_joint_ball_of_product hp)) a).2.2.2
    weighted_identity := fun a p hp => ((hrall p (mem_joint_ball_of_product hp)) a).2.2.1 }⟩

def normalizedScaledRepresentative {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
    (P : ActualWeightedVertexSmallTailData n I) (a : ActualVertexIndex n I) (s : ℂ)
    (z : CoordinateSpace n) : ℂ :=
  P.representative a (actualWeightedScalingMap (degLexWeight n P.germs.degreeBound) (jointPoint n (z,s))) /
    s ^ weightedDegree (degLexWeight n P.germs.degreeBound) a.val

theorem exists_smallParameter {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
    (P : ActualWeightedVertexSmallTailData n I) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℂ, s ≠ 0 ∧ s ∈ ball 0 P.radius ∧
      (∀ a, DifferentiableOn ℂ (normalizedScaledRepresentative P a s) (ball 0 P.radius)) ∧
      ∀ a, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
        normalizedScaledRepresentative P a s z - coordinateMonomial a.val z = s * P.tailFactor a (z,s) ∧
          ‖s * P.tailFactor a (z,s)‖ < ε := by
  let t := min (P.radius / 2) (ε / (2 * P.bound))
  have ht : 0 < t := lt_min (half_pos P.radius_pos)
    (div_pos hε (mul_pos (by norm_num) P.bound_pos))
  have htr : t < P.radius := (min_le_left _ _).trans_lt (half_lt_self P.radius_pos)
  have hnorm : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real,abs_of_nonneg ht.le]
  have hs0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hs : (t : ℂ) ∈ ball 0 P.radius := by rw [mem_ball_zero_iff,hnorm]; exact htr
  have htB : t * P.bound ≤ ε / 2 := by
    calc
      _ ≤ (ε / (2 * P.bound)) * P.bound := mul_le_mul_of_nonneg_right (min_le_right _ _) P.bound_pos.le
      _ = (ε * P.bound) / (2 * P.bound) := by ring
      _ = ε / 2 := mul_div_mul_right ε 2 P.bound_pos.ne'
  refine ⟨(t : ℂ),hs0,hs,?_,?_⟩
  · intro a
    have hgraph : Differentiable ℂ (fun z : CoordinateSpace n => (z,(t : ℂ))) :=
      differentiable_id.prodMk (differentiable_const _)
    have hd := (P.scaled_hol a).comp hgraph.differentiableOn (fun z hz => ⟨hz,hs⟩)
    unfold normalizedScaledRepresentative
    simp only [div_eq_mul_inv]
    exact hd.mul_const (((t : ℂ) ^ weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹)
  · intro a z hz
    have he := P.weighted_identity a (z,(t : ℂ)) ⟨hz,hs⟩
    have hpow : (t : ℂ) ^ weightedDegree (degLexWeight n P.germs.degreeBound) a.val ≠ 0 := pow_ne_zero _ hs0
    have hidentity : normalizedScaledRepresentative P a (t : ℂ) z =
        coordinateMonomial a.val z + (t : ℂ) * P.tailFactor a (z,(t : ℂ)) := by
      unfold normalizedScaledRepresentative
      rw [he,mul_div_cancel_left₀ _ hpow]
    refine ⟨by rw [hidentity]; ring,?_⟩
    calc
      _ = t * ‖P.tailFactor a (z,(t : ℂ))‖ := by rw [norm_mul,hnorm]
      _ ≤ t * P.bound := mul_le_mul_of_nonneg_left (P.factor_bound a _ ⟨hz,hs⟩) ht.le
      _ ≤ ε / 2 := htB
      _ < ε := half_lt_self hε

/-- Final original-only API: every item of the small-tail data and the nonzero parameter is produced from I. -/
theorem exists_actualWeightedVertexSmallTails (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ P : ActualWeightedVertexSmallTailData n I, ∀ ε > 0,
      ∃ s : ℂ, s ≠ 0 ∧ s ∈ ball 0 P.radius ∧
        (∀ a, DifferentiableOn ℂ (normalizedScaledRepresentative P a s) (ball 0 P.radius)) ∧
        ∀ a, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
          normalizedScaledRepresentative P a s z - coordinateMonomial a.val z = s * P.tailFactor a (z,s) ∧
            ‖s * P.tailFactor a (z,s)‖ < ε := by
  obtain ⟨P⟩ := nonempty_actualWeightedVertexSmallTailData n I
  exact ⟨P,exists_smallParameter P⟩

end

end Hironaka.HironakaActualWeightedVertexSmallTails
