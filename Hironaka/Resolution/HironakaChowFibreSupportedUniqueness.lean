import Hironaka.Resolution.HironakaChowOriginalFibreSupportedDivision
import Hironaka.Resolution.HironakaActualBoundedSupportedNeumannUniqueness

/-! Unique supported division for the SAME ORIGINAL fibre lifts.
All physical domains/bounds/scales for an original zero relation are
derived internally. Assigned quotient space is not the entire lift ideal. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowFibreSupportedUniqueness
noncomputable section
open HolGerm HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
 HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedScaling
 HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
 HironakaChowFibreLiftWeightedFactors HironakaChowFibreLiftUniformTails
 HironakaActualJointBaseFibre HironakaActualCauchyCoordinateDivision
 HironakaActualCauchyMonomialDivision HironakaActualCauchyEnumeratedPartition
 HironakaActualCauchyDiagramPartition
 HironakaActualCauchyTaylorSupport HironakaActualCauchyNeumannDivision HironakaActualDiagonalTaylor

open HironakaChowOriginalFibreSupportedDivision HironakaActualBoundedSupportedNeumannUniqueness

/- Elementary model-germ operations kept private in the existing mother;
restated with zero separate mathematical credit. -/
variable {n k : ℕ}
private theorem modelGerm_eq_of_eqOn {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (he : EqOn f g (ball 0 R)) : modelGerm hR hf = modelGerm hR hg := by
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  have ht : Tendsto e (𝓝 (0 : ComplexModel n)) (𝓝 (0 : CoordinateSpace n)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hR))] with z hz
  exact he hz


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


private theorem scaled_joint_diagonal (W : Fin n → ℕ) (s : ℂ) (z : ComplexModel n) :
    actualWeightedScalingMap W (jointPoint n ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)) z,s)) =
      actualDiagonalMap (fun i => s ^ W i) z := by
  ext i
  change (jointPoint n ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)) z,s)) (parameterIndex n) ^ W i *
      (jointPoint n ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)) z,s)) (i.castAdd 1) = _
  rw [jointPoint_parameter,jointPoint_base,actualDiagonalMap_apply]
  rfl

private theorem modelGerm_scaled (W : Fin n → ℕ) (s : ℂ)
    (f : ComplexModel n → ℂ) (hf : OkaRelationSheaf.HolAt f 0)
    {R : ℝ} (hR : 0 < R)
    (h : DifferentiableOn ℂ (fun z : CoordinateSpace n =>
      f (actualWeightedScalingMap W (jointPoint n (z,s)) )) (ball 0 R)) :
    modelGerm hR h = actualDiagonalPullback (fun i => s ^ W i) (HolGerm.mk f hf) := by
  unfold actualDiagonalPullback
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => congrArg f (scaled_joint_diagonal W s z)

private theorem const_diagonal_eq_zero (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (a : ℂ) (ha : a ≠ 0) (g : HolGerm (ComplexModel n))
    (hz : HolGerm.constHom a * actualDiagonalPullback c g = 0) : g = 0 := by
  have hi := congrArg (actualDiagonalPullback (fun i => (c i)⁻¹)) hz
  rw [map_mul,actualDiagonalPullback_const,actualDiagonalPullback_inverse c hc,map_zero] at hi
  have he := congrArg (fun z : HolGerm (ComplexModel n) => HolGerm.constHom a⁻¹ * z) hi
  rw [← mul_assoc,← map_mul,inv_mul_cancel₀ ha,map_one,one_mul,mul_zero] at he
  exact he

private theorem diagonal_const_support (c : Fin n → ℂ) (a : ℂ)
    (g : HolGerm (ComplexModel n)) (β : Fin n →₀ ℕ)
    (hz : MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n g) = 0) :
    MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
      (HolGerm.constHom a * actualDiagonalPullback c g)) = 0 := by
  have hConst : actualUnshiftedTaylorAlgHom n (HolGerm.constHom a) = MvPowerSeries.C a :=
    (actualUnshiftedTaylorAlgHom n).commutes a
  rw [map_mul,hConst,MvPowerSeries.coeff_C_mul,coeff_actualDiagonalPullback,hz,mul_zero,mul_zero]

private theorem modelGerm_const_mul {R : ℝ} (hR : 0 < R) (a : ℂ)
    {f : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R)) :
    modelGerm hR (hf.const_mul a) = HolGerm.constHom a * modelGerm hR hf := by
  change HolGerm.mk (fun z : ComplexModel n => a * modelFunction f z) _ =
    HolGerm.constHom a * HolGerm.mk (modelFunction f) (modelFunction_holAt hR hf)
  simpa only [HolGerm.mk_const] using HolGerm.mk_mul (fun _ : ComplexModel n => a)
    (modelFunction f) (eventually_differentiableAt_const a) (modelFunction_holAt hR hf)

private theorem modelGerm_zero {R : ℝ} (hR : 0 < R)
    {f : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hz : ∀ z ∈ ball (0 : CoordinateSpace n) R, f z = 0) : modelGerm hR hf = 0 := by
  have he := modelGerm_eq_of_eqOn hR hf (differentiableOn_const (c := (0 : ℂ))) hz
  exact he.trans rfl

private theorem zero_relation_domain (W : Fin n → ℕ)
    (F : Fin k → ComplexModel n → ℂ) (hF : ∀ j, OkaRelationSheaf.HolAt (F j) 0)
    (q : Fin k → HolGerm (ComplexModel n)) (r : HolGerm (ComplexModel n))
    (hzero : (∑ j, q j * HolGerm.mk (F j) (hF j)) + r = 0)
    (a : ℝ) (ha : 0 < a) :
    ∃ (Q : Fin k → ComplexModel n → ℂ) (hQ : ∀ j, OkaRelationSheaf.HolAt (Q j) 0)
      (T : ComplexModel n → ℂ) (hT : OkaRelationSheaf.HolAt T 0),
      (∀ j, HolGerm.mk (Q j) (hQ j) = q j) ∧ HolGerm.mk T hT = r ∧
      ∃ (R M : ℝ), 0 < R ∧ R < a ∧ 0 ≤ M ∧
        ∀ p ∈ ball (0 : CoordinateSpace n) R ×ˢ ball (0 : ℂ) R,
          (∀ j, DifferentiableAt ℂ (fun v : CoordinateSpace n × ℂ =>
            Q j (actualWeightedScalingMap W (jointPoint n v))) p ∧
            ‖Q j (actualWeightedScalingMap W (jointPoint n p))‖ ≤ M) ∧
          DifferentiableAt ℂ (fun v : CoordinateSpace n × ℂ =>
            T (actualWeightedScalingMap W (jointPoint n v))) p ∧
          (∑ j, Q j (actualWeightedScalingMap W (jointPoint n p)) *
            F j (actualWeightedScalingMap W (jointPoint n p))) +
              T (actualWeightedScalingMap W (jointPoint n p)) = 0 := by
  choose Q hQ hQeq using fun j => HolGerm.exists_eq_mk (q j)
  obtain ⟨T,hT,hTeq⟩ := HolGerm.exists_eq_mk r
  have hRel : ∀ᶠ z in nhds (0 : ComplexModel n), (∑ j, Q j z * F j z) + T z = 0 := by
    have hm : HolGerm.mk (fun z : ComplexModel n => (∑ j, Q j z * F j z) + T z)
        (eventually_differentiableAt_add (eventually_differentiableAt_sum Finset.univ fun j =>
          eventually_differentiableAt_mul (hQ j) (hF j)) hT) = 0 := by
      rw [HolGerm.mk_add (fun z : ComplexModel n => ∑ j, Q j z * F j z) T
        (eventually_differentiableAt_sum Finset.univ fun j =>
          eventually_differentiableAt_mul (hQ j) (hF j)) hT,
        HolGerm.mk_sum Finset.univ (fun (j : Fin k) (z : ComplexModel n) => Q j z * F j z)
          (fun j => eventually_differentiableAt_mul (hQ j) (hF j))]
      have hp (j : Fin k) : HolGerm.mk (fun z : ComplexModel n => Q j z * F j z)
          (eventually_differentiableAt_mul (hQ j) (hF j)) = q j * HolGerm.mk (F j) (hF j) := by
        exact (HolGerm.mk_mul (Q j) (F j) (hQ j) (hF j)).trans
          (congrArg (fun u : HolGerm (ComplexModel n) => u * HolGerm.mk (F j) (hF j)) (hQeq j).symm)
      simp_rw [hp,← hTeq]
      exact hzero
    exact HolGerm.mk_eq_mk_iff.mp (hm.trans (HolGerm.mk_const (0 : ℂ)).symm)
  let σ := fun p : CoordinateSpace n × ℂ => actualWeightedScalingMap W (jointPoint n p)
  have hψ0 : actualWeightedScalingMap W 0 = 0 := by ext i; simp [actualWeightedScalingMap]
  have hσ0 : σ 0 = 0 := by dsimp only [σ]; rw [map_zero,hψ0]
  have hσ : Continuous σ := (differentiable_actualWeightedScalingMap W).continuous.comp (jointPoint n).continuous
  have hRel' : ∀ᶠ p in nhds (0 : CoordinateSpace n × ℂ),
      (∑ j, Q j (σ p) * F j (σ p)) + T (σ p) = 0 := by
    have ht : Tendsto σ (nhds (0 : CoordinateSpace n × ℂ)) (nhds (0 : ComplexModel n)) := by
      simpa only [hσ0] using hσ.tendsto (0 : CoordinateSpace n × ℂ)
    exact ht.eventually hRel
  have hComp (f : ComplexModel n → ℂ) (hf : OkaRelationSheaf.HolAt f 0) :
      OkaRelationSheaf.HolAt (fun p : CoordinateSpace n × ℂ => f (σ p)) 0 :=
    eventually_differentiableAt_comp_clm (jointPoint n)
      (holomorphic_comp (actualWeightedScalingMap W)
        (Eventually.of_forall fun _ => (differentiable_actualWeightedScalingMap W).differentiableAt) hψ0 hf)
  let M := 1 + ∑ j, ‖Q j (σ 0)‖
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hb (j : Fin k) : ∀ᶠ p in nhds (0 : CoordinateSpace n × ℂ), ‖Q j (σ p)‖ ≤ M := by
    have ht := (hComp (Q j) (hQ j)).self_of_nhds.continuousAt.norm.eventually
      (gt_mem_nhds (lt_add_one ‖Q j (σ 0)‖))
    have hs : ‖Q j (σ 0)‖ ≤ ∑ i, ‖Q i (σ 0)‖ :=
      Finset.single_le_sum (f := fun i : Fin k => ‖Q i (σ 0)‖)
        (fun i _ => norm_nonneg _) (Finset.mem_univ j)
    filter_upwards [ht] with p hp
    dsimp only [M]
    linarith
  have hall : ∀ᶠ p in nhds (0 : CoordinateSpace n × ℂ),
      (∀ j, DifferentiableAt ℂ (fun v : CoordinateSpace n × ℂ => Q j (σ v)) p ∧ ‖Q j (σ p)‖ ≤ M) ∧
      DifferentiableAt ℂ (fun v : CoordinateSpace n × ℂ => T (σ v)) p ∧
      (∑ j, Q j (σ p) * F j (σ p)) + T (σ p) = 0 :=
    (eventually_all.mpr fun j => (hComp (Q j) (hQ j)).and (hb j)).and ((hComp T hT).and hRel')
  obtain ⟨R₀,hR₀,hAll⟩ := Metric.eventually_nhds_iff_ball.mp hall
  let R := min (R₀/2) (a/2)
  have hR : 0 < R := lt_min (half_pos hR₀) (half_pos ha)
  have hRold : R < R₀ := (min_le_left _ _).trans_lt (half_lt_self hR₀)
  refine ⟨Q,hQ,T,hT,fun j => (hQeq j).symm,hTeq.symm,R,M,hR,
    (min_le_right _ _).trans_lt (half_lt_self ha),hM,?_⟩
  intro p hp
  apply hAll p
  rw [mem_ball_zero_iff,Prod.norm_mk]
  exact (max_lt (mem_ball_zero_iff.mp hp.1) (mem_ball_zero_iff.mp hp.2)).trans hRold

private abbrev LiftIndex (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  ActualVertexIndex t (Ideal.map (jointBaseZeroTrace d t).toRingHom I)

theorem supported_zero_for_original_data (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (q : Fin (Fintype.card (LiftIndex d t I)) → HolGerm (ComplexModel (d+t)))
    (r : HolGerm (ComplexModel (d+t)))
    (hzero : (∑ j, q j * P.lift (fibreEnumeration d t I j)) + r = 0)
    (hq : ∀ j β, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
      (β + wordExponent (fibreHeadWords d t I j)) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (q j)) = 0)
    (hr : ∀ β, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) β →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) r) = 0) :
    (∀ j, q j = 0) ∧ r = 0 := by
  let e := fibreEnumeration d t I
  let w := fibreHeadWords d t I
  let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
  let h := fun j => weightedDegree (degLexWeight t P.fibre.degreeBound) (e j).val
  have hz : (∑ j, q j * HolGerm.mk (P.representative (e j)) (P.representative_hol (e j))) + r = 0 := by
    simp_rw [P.representative_eq]
    exact hzero
  obtain ⟨Q,hQ,T,hT,hQeq,hTeq,R,M,hR,hRP,hM,hData⟩ :=
    zero_relation_domain W (fun j => P.representative (e j))
      (fun j => P.representative_hol (e j)) q r hz P.radius P.radius_pos
  obtain ⟨D⟩ := nonempty_concreteNeumannData R hR w
  let τ := min (R/2) (D.epsilon/(2*P.bound))
  have hτ : 0 < τ := lt_min (half_pos hR) (div_pos D.epsilon_pos (mul_pos (by norm_num) P.bound_pos))
  have hτR : τ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hs0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hsR : (τ : ℂ) ∈ ball 0 R := by simpa [mem_ball_zero_iff,Complex.norm_real,abs_of_pos hτ] using hτR
  have hsP : (τ : ℂ) ∈ ball 0 P.radius := (ball_subset_ball hRP.le) hsR
  have hτB : τ*P.bound ≤ D.epsilon/2 := by
    calc
      _ ≤ (D.epsilon/(2*P.bound))*P.bound := mul_le_mul_of_nonneg_right (min_le_right _ _) P.bound_pos.le
      _ = (D.epsilon*P.bound)/(2*P.bound) := by ring
      _ = D.epsilon/2 := mul_div_mul_right D.epsilon 2 P.bound_pos.ne'
  let H := fun j (z : CoordinateSpace (d+t)) => (τ : ℂ)*P.tailFactor (e j) (z,(τ : ℂ))
  let Qs := fun j (z : CoordinateSpace (d+t)) => Q j (actualWeightedScalingMap W (jointPoint (d+t) (z,(τ : ℂ))))
  let Qn := fun j (z : CoordinateSpace (d+t)) => (τ : ℂ)^h j * Qs j z
  let Ts := fun z : CoordinateSpace (d+t) => T (actualWeightedScalingMap W (jointPoint (d+t) (z,(τ : ℂ))))
  have hGraph : Differentiable ℂ (fun z : CoordinateSpace (d+t) => (z,(τ : ℂ))) :=
    differentiable_id.prodMk (differentiable_const _)
  have hHd (j) : DifferentiableOn ℂ (H j) (ball 0 R) :=
    ((P.factor_hol (e j)).comp hGraph.differentiableOn
      (fun z hz => ⟨(ball_subset_ball hRP.le) hz,hsP⟩)).const_mul _
  have hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace (d+t)) R, ‖H j z‖ ≤ D.epsilon := by
    intro j z hz
    change ‖(τ : ℂ) * P.tailFactor (e j) (z,(τ : ℂ))‖ ≤ _
    rw [norm_mul,show ‖(τ : ℂ)‖=τ by simp [Complex.norm_real,abs_of_pos hτ]]
    exact ((mul_le_mul_of_nonneg_left (P.factor_bound (e j) _
      ⟨(ball_subset_ball hRP.le) hz,hsP⟩) hτ.le).trans hτB).trans (half_le_self D.epsilon_pos.le)
  have hQsd (j) : DifferentiableOn ℂ (Qs j) (ball 0 R) := by
    intro z hz
    exact (((hData (z,(τ : ℂ)) ⟨hz,hsR⟩).1 j).1.comp z (hGraph z)).differentiableWithinAt
  have hQnd (j) : DifferentiableOn ℂ (Qn j) (ball 0 R) := (hQsd j).const_mul _
  have hTd : DifferentiableOn ℂ Ts (ball 0 R) := by
    intro z hz
    exact ((hData (z,(τ : ℂ)) ⟨hz,hsR⟩).2.1.comp z (hGraph z)).differentiableWithinAt
  let c := fun i => (τ : ℂ)^W i
  have hQgerm (j) : modelGerm hR (hQnd j) = HolGerm.constHom ((τ : ℂ)^h j) * actualDiagonalPullback c (q j) := by
    change modelGerm hR ((hQsd j).const_mul ((τ : ℂ)^h j)) = _
    rw [modelGerm_const_mul hR ((τ : ℂ)^h j) (hQsd j),
      modelGerm_scaled W (τ : ℂ) (Q j) (hQ j) hR (hQsd j),hQeq]
  have hTgerm : modelGerm hR hTd = actualDiagonalPullback c r := by
    rw [modelGerm_scaled W (τ : ℂ) T hT hR hTd,hTeq]
  have hQsupport : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val) (β + wordExponent (w j)) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (modelGerm hR (hQnd j))) = 0 := by
    intro j β hβ
    rw [hQgerm]
    exact diagonal_const_support c ((τ : ℂ)^h j) (q j) β (hq j β hβ)
  have hTsupport : ∀ β, ¬ AvoidsCones (List.ofFn w) β →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (modelGerm hR hTd)) = 0 := by
    intro β hβ
    rw [hTgerm,coeff_actualDiagonalPullback,hr β hβ,mul_zero]
  let M' := ∑ j, ‖(τ : ℂ)^h j‖ * M
  have hM' : 0 ≤ M' := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) hM
  have hQbound : ∀ z ∈ ball (0 : CoordinateSpace (d+t)) R, ∑ j, ‖Qn j z‖ ≤ M' := by
    intro z hz
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (((hData (z,(τ : ℂ)) ⟨hz,hsR⟩).1 j).2) (norm_nonneg _)
  have hPhysical : ∀ z ∈ ball (0 : CoordinateSpace (d+t)) R,
      (∑ j, Qn j z * (wordMonomial (w j) z + H j z)) + Ts z = 0 := by
    intro z hz
    have he := (hData (z,(τ : ℂ)) ⟨hz,hsR⟩).2.2
    refine (Eq.trans ?_ he)
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hi := P.weighted_identity (e j) (z,(τ : ℂ)) ⟨(ball_subset_ball hRP.le) hz,hsP⟩
    dsimp only [Qn,Qs,H]
    rw [hi]
    change (τ : ℂ)^h j * Qs j z * (wordMonomial (w j) z + H j z) =
      Qs j z * ((τ : ℂ)^h j * (coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) (e j).val) z + H j z))
    rw [show w j = wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) (e j).val) from rfl,
      wordMonomial_wordOfExponent]
    unfold coordinateMonomial
    ring
  have hall := actual_bounded_supported_neumann_zero_division hR w D H Qn Ts hHd hHb hQnd hTd
    hQsupport hTsupport M' hM' hQbound hPhysical
  have hc : ∀ i, c i ≠ 0 := fun _ => pow_ne_zero _ hs0
  constructor
  · intro j
    have hz := modelGerm_zero hR (hQnd j) (fun z hz => (hall z hz).1 j)
    rw [hQgerm] at hz
    exact const_diagonal_eq_zero c hc ((τ : ℂ)^h j) (pow_ne_zero _ hs0) (q j) hz
  · have hz := modelGerm_zero hR hTd (fun z hz => (hall z hz).2)
    rw [hTgerm] at hz
    have he := congrArg (actualDiagonalPullback (fun i => (c i)⁻¹)) hz
    rw [actualDiagonalPullback_inverse c hc,map_zero] at he
    exact he

/-- SAME original lifts/regions precede ALL original numerators and their unique supported divisions. -/
theorem exists_original_fibre_unique_division (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ P : FibreLiftUniformTailData d t I, ∀ g : HolGerm (ComplexModel (d+t)),
      ∃! z : (Fin (Fintype.card (LiftIndex d t I)) → HolGerm (ComplexModel (d+t))) ×
          HolGerm (ComplexModel (d+t)),
        g = (∑ j, z.1 j * P.lift (fibreEnumeration d t I j)) + z.2 ∧
        (∀ j β, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
          (β + wordExponent (fibreHeadWords d t I j)) →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (z.1 j)) = 0) ∧
        ∀ β, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) β →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) z.2) = 0 := by
  obtain ⟨P,hP⟩ := exists_original_fibre_supported_division d t I
  refine ⟨P,fun g => ?_⟩
  obtain ⟨q,r,he,hq,hr⟩ := hP g
  refine ⟨(q,r),⟨he,hq,hr⟩,?_⟩
  intro z hz
  have hzero : (∑ j, (z.1 j - q j) * P.lift (fibreEnumeration d t I j)) + (z.2-r) = 0 := by
    rw [show (∑ j, (z.1 j - q j) * P.lift (fibreEnumeration d t I j)) =
      (∑ j, z.1 j * P.lift (fibreEnumeration d t I j)) -
        (∑ j, q j * P.lift (fibreEnumeration d t I j)) by simp only [sub_mul,Finset.sum_sub_distrib]]
    linear_combination he - hz.1
  have hqs : ∀ j β, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
      (β + wordExponent (fibreHeadWords d t I j)) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (z.1 j-q j)) = 0 := by
    intro j β hβ
    rw [map_sub,map_sub,hz.2.1 j β hβ,hq j β hβ,sub_self]
  have hrs : ∀ β, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) β →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (z.2-r)) = 0 := by
    intro β hβ
    rw [map_sub,map_sub,hz.2.2 β hβ,hr β hβ,sub_self]
  have hall := supported_zero_for_original_data d t I P (fun j => z.1 j-q j) (z.2-r) hzero hqs hrs
  apply Prod.ext
  · funext j
    exact sub_eq_zero.mp (hall.1 j)
  · exact sub_eq_zero.mp hall.2

end
end Hironaka.HironakaChowFibreSupportedUniqueness
