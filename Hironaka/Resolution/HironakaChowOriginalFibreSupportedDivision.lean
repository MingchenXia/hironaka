import Hironaka.Resolution.HironakaChowFibreLiftUniformTails
import Hironaka.Resolution.HironakaActualDiagonalTaylor
import Hironaka.Resolution.HironakaActualCauchyNeumannDivision

/-! ALL-original-germ supported division for SAME actual fibre lifts.
Numerator-dependent domains/scales are internally chosen and transported
back by the genuine inverse diagonal. Assigned quotient space is NOT the
entire ideal of the lifts. Blueprint first. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowOriginalFibreSupportedDivision
noncomputable section
open HolGerm HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
 HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedScaling
 HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
 HironakaChowFibreLiftWeightedFactors HironakaChowFibreLiftUniformTails
 HironakaActualJointBaseFibre HironakaActualCauchyCoordinateDivision
 HironakaActualCauchyMonomialDivision HironakaActualCauchyEnumeratedPartition
 HironakaActualCauchyDiagramPartition
 HironakaActualCauchyTaylorSupport HironakaActualCauchyNeumannDivision HironakaActualDiagonalTaylor

/- Elementary model-germ operations kept private in the existing mother;
restated with zero separate mathematical credit. -/
variable {n k : ℕ}
private theorem modelGerm_sum {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (f : ι → CoordinateSpace n → ℂ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball 0 R)) :
    modelGerm hR (DifferentiableOn.fun_sum fun i (_hi : i ∈ Finset.univ) => hf i) =
      ∑ i, modelGerm hR (hf i) := by
  change HolGerm.mk (fun z : ComplexModel n => ∑ i, modelFunction (f i) z) _ = _
  exact HolGerm.mk_sum Finset.univ _ (fun i => modelFunction_holAt hR (hf i))

private theorem modelGerm_add {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R)) :
    modelGerm hR (hf.add hg) = modelGerm hR hf + modelGerm hR hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z + modelFunction g z) _ = _
  exact HolGerm.mk_add _ _ _ _

private theorem modelGerm_mul {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R)) :
    modelGerm hR (hf.mul hg) = modelGerm hR hf * modelGerm hR hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z * modelFunction g z) _ = _
  exact HolGerm.mk_mul _ _ _ _

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

private theorem inverse_diagonal_division (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (g : HolGerm (ComplexModel n)) (F Q : Fin k → HolGerm (ComplexModel n))
    (a : Fin k → ℂ) (r : HolGerm (ComplexModel n))
    (h : actualDiagonalPullback c g =
      (∑ j, Q j * (HolGerm.constHom (a j) * actualDiagonalPullback c (F j))) + r) :
    g = (∑ j, (HolGerm.constHom (a j) *
      actualDiagonalPullback (fun i => (c i)⁻¹) (Q j)) * F j) +
        actualDiagonalPullback (fun i => (c i)⁻¹) r := by
  have he := congrArg (actualDiagonalPullback (fun i => (c i)⁻¹)) h
  rw [actualDiagonalPullback_inverse c hc] at he
  simp only [map_add, map_sum, map_mul, actualDiagonalPullback_const] at he
  simp_rw [actualDiagonalPullback_inverse c hc] at he
  refine he.trans ?_
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem inverse_diagonal_const_support (c : Fin n → ℂ) (a : ℂ)
    (g : HolGerm (ComplexModel n)) (β : Fin n →₀ ℕ)
    (hz : MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n g) = 0) :
    MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
      (HolGerm.constHom a * actualDiagonalPullback (fun i => (c i)⁻¹) g)) = 0 := by
  have hConst : actualUnshiftedTaylorAlgHom n (HolGerm.constHom a) = MvPowerSeries.C a :=
    (actualUnshiftedTaylorAlgHom n).commutes a
  rw [map_mul, hConst, MvPowerSeries.coeff_C_mul,
    coeff_actualDiagonalPullback, hz, mul_zero, mul_zero]

private abbrev LiftIndex (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  ActualVertexIndex t (Ideal.map (jointBaseZeroTrace d t).toRingHom I)

def fibreEnumeration (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Fin (Fintype.card (LiftIndex d t I)) ≃ LiftIndex d t I := (Fintype.equivFin _).symm

def fibreHeadWords (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Fin (Fintype.card (LiftIndex d t I)) → CoordinateWord (d+t) :=
  fun j => wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) (fibreEnumeration d t I j).val)

private theorem numerator_domain (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I) (g : HolGerm (ComplexModel (d+t))) :
    ∃ (f : ComplexModel (d+t) → ℂ) (hf : OkaRelationSheaf.HolAt f 0),
      HolGerm.mk f hf = g ∧ ∃ (R M : ℝ), 0 < R ∧ R < P.radius ∧ 0 ≤ M ∧
      ∀ p ∈ ball (0 : CoordinateSpace (d+t)) R ×ˢ ball (0 : ℂ) R,
        DifferentiableAt ℂ (fun q : CoordinateSpace (d+t) × ℂ =>
          f (actualWeightedScalingMap
            (extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound))
            (jointPoint (d+t) q))) p ∧
        ‖f (actualWeightedScalingMap
            (extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound))
            (jointPoint (d+t) p))‖ ≤ M := by
  obtain ⟨f,hf,hfg⟩ := HolGerm.exists_eq_mk g
  let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
  let G := fun p : CoordinateSpace (d+t) × ℂ => f (actualWeightedScalingMap W (jointPoint (d+t) p))
  have hψ : ∀ᶠ z in nhds (0 : ComplexModel ((d+t)+1)), DifferentiableAt ℂ (actualWeightedScalingMap W) z :=
    Eventually.of_forall fun _ => (differentiable_actualWeightedScalingMap W).differentiableAt
  have hψ0 : actualWeightedScalingMap W 0 = 0 := by ext i; simp [actualWeightedScalingMap]
  have hG : OkaRelationSheaf.HolAt G 0 :=
    eventually_differentiableAt_comp_clm (jointPoint (d+t))
      (holomorphic_comp (actualWeightedScalingMap W) hψ hψ0 hf)
  let M := ‖G 0‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb : ∀ᶠ p in nhds (0 : CoordinateSpace (d+t) × ℂ), ‖G p‖ ≤ M :=
    ((hG.self_of_nhds.continuousAt.norm).eventually (gt_mem_nhds (lt_add_one ‖G 0‖))).mono
      (fun _ h => h.le)
  obtain ⟨R₀,hR₀,hAll⟩ := Metric.eventually_nhds_iff_ball.mp (hG.and hb)
  let R := min (R₀/2) (P.radius/2)
  have hR : 0 < R := lt_min (half_pos hR₀) (half_pos P.radius_pos)
  have hRold : R < R₀ := (min_le_left _ _).trans_lt (half_lt_self hR₀)
  refine ⟨f,hf,hfg.symm,R,M,hR,(min_le_right _ _).trans_lt (half_lt_self P.radius_pos),hM,?_⟩
  intro p hp
  apply hAll p
  rw [mem_ball_zero_iff,Prod.norm_mk]
  exact (max_lt (mem_ball_zero_iff.mp hp.1) (mem_ball_zero_iff.mp hp.2)).trans hRold

theorem exists_supported_division_for_original_data (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I) (g : HolGerm (ComplexModel (d+t))) :
    ∃ (q : Fin (Fintype.card (LiftIndex d t I)) → HolGerm (ComplexModel (d+t)))
      (r : HolGerm (ComplexModel (d+t))),
      g = (∑ j, q j * P.lift (fibreEnumeration d t I j)) + r ∧
      (∀ j β, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
        (β + wordExponent (fibreHeadWords d t I j)) →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (q j)) = 0) ∧
      ∀ β, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) β →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) r) = 0 := by
  obtain ⟨f,hf,hfg,R,M,hR,hRP,hM,hNum⟩ := numerator_domain d t I P g
  let e := fibreEnumeration d t I
  let w := fibreHeadWords d t I
  let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
  let h := fun j => weightedDegree (degLexWeight t P.fibre.degreeBound) (e j).val
  obtain ⟨D⟩ := nonempty_concreteNeumannData R hR w
  let τ := min (R/2) (D.epsilon/(2*P.bound))
  have hτ : 0 < τ := lt_min (half_pos hR) (div_pos D.epsilon_pos (mul_pos (by norm_num) P.bound_pos))
  have hτR : τ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hs0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hsR : (τ : ℂ) ∈ ball 0 R := by simpa [mem_ball_zero_iff, Complex.norm_real, abs_of_pos hτ] using hτR
  have hsP : (τ : ℂ) ∈ ball 0 P.radius := (ball_subset_ball hRP.le) hsR
  have hτB : τ*P.bound ≤ D.epsilon/2 := by
    calc
      _ ≤ (D.epsilon/(2*P.bound))*P.bound := mul_le_mul_of_nonneg_right (min_le_right _ _) P.bound_pos.le
      _ = (D.epsilon*P.bound)/(2*P.bound) := by ring
      _ = D.epsilon/2 := mul_div_mul_right D.epsilon 2 P.bound_pos.ne'
  let H := fun j (z : CoordinateSpace (d+t)) => (τ : ℂ) * P.tailFactor (e j) (z,(τ : ℂ))
  let G := fun z : CoordinateSpace (d+t) => f (actualWeightedScalingMap W (jointPoint (d+t) (z,(τ : ℂ))))
  have hGraph : Differentiable ℂ (fun z : CoordinateSpace (d+t) => (z,(τ : ℂ))) :=
    differentiable_id.prodMk (differentiable_const _)
  have hHd (j) : DifferentiableOn ℂ (H j) (ball 0 R) := by
    exact ((P.factor_hol (e j)).comp hGraph.differentiableOn
      (fun z hz => ⟨(ball_subset_ball hRP.le) hz,hsP⟩)).const_mul _
  have hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace (d+t)) R, ‖H j z‖ ≤ D.epsilon := by
    intro j z hz
    change ‖(τ : ℂ) * P.tailFactor (e j) (z,(τ : ℂ))‖ ≤ _
    rw [norm_mul,show ‖(τ : ℂ)‖=τ by simp [Complex.norm_real,abs_of_pos hτ]]
    exact ((mul_le_mul_of_nonneg_left (P.factor_bound (e j) _
      ⟨(ball_subset_ball hRP.le) hz,hsP⟩) hτ.le).trans hτB).trans (half_le_self D.epsilon_pos.le)
  have hGd : DifferentiableOn ℂ G (ball 0 R) := by
    intro z hz
    exact ((hNum (z,(τ : ℂ)) ⟨hz,hsR⟩).1.comp z (hGraph z)).differentiableWithinAt
  have hGb : ∀ z ∈ ball (0 : CoordinateSpace (d+t)) R, ‖G z‖ ≤ M :=
    fun z hz => (hNum (z,(τ : ℂ)) ⟨hz,hsR⟩).2
  have hd := neumannSums_differentiableOn hR D hHd hHb hM hGd hGb
  let Q := neumannQuotientSum R w H G
  let T := neumannRemainderSum R w H G
  have hBs (j) : DifferentiableOn ℂ (fun z => wordMonomial (w j) z + H j z) (ball 0 R) :=
    (wordMonomial_differentiable (w j)).differentiableOn.add (hHd j)
  have hScaledF (j) : DifferentiableOn ℂ
      (fun z : CoordinateSpace (d+t) => P.representative (e j)
        (actualWeightedScalingMap W (jointPoint (d+t) (z,(τ : ℂ))))) (ball 0 R) :=
    (P.scaled_hol (e j)).comp hGraph.differentiableOn
      (fun z hz => ⟨(ball_subset_ball hRP.le) hz,hsP⟩)
  have hNormF (j) : DifferentiableOn ℂ
      (fun z : CoordinateSpace (d+t) => P.representative (e j)
        (actualWeightedScalingMap W (jointPoint (d+t) (z,(τ : ℂ)))) / (τ : ℂ)^h j) (ball 0 R) := by
    simpa only [div_eq_mul_inv] using (hScaledF j).mul_const (((τ : ℂ)^h j)⁻¹)
  have hGermF (j) : modelGerm hR (hBs j) = HolGerm.constHom (((τ : ℂ)^h j)⁻¹) *
      actualDiagonalPullback (fun i => (τ : ℂ)^W i) (P.lift (e j)) := by
    have hPoint : EqOn (fun z => wordMonomial (w j) z + H j z)
        (fun z => P.representative (e j) (actualWeightedScalingMap W
          (jointPoint (d+t) (z,(τ : ℂ)))) / (τ : ℂ)^h j) (ball 0 R) := by
      intro z hz
      have hi := P.weighted_identity (e j) (z,(τ : ℂ)) ⟨(ball_subset_ball hRP.le) hz,hsP⟩
      change _ = _ / (τ : ℂ)^h j
      rw [hi,mul_div_cancel_left₀ _ (pow_ne_zero _ hs0)]
      change wordMonomial (w j) z + H j z =
        coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) (e j).val) z +
          (τ : ℂ) * P.tailFactor (e j) (z,(τ : ℂ))
      rw [show w j=wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ) (e j).val) from rfl,
        wordMonomial_wordOfExponent]
      rfl
    rw [modelGerm_eq_of_eqOn hR (hBs j) (hNormF j) hPoint]
    rw [← P.representative_eq (e j)]
    unfold actualDiagonalPullback
    rw [compAlgHom_mk,← HolGerm.mk_const,← HolGerm.mk_mul]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp only [modelFunction,Function.comp_apply]
      rw [scaled_joint_diagonal]
      ring
  have hGermG : modelGerm hR hGd = actualDiagonalPullback (fun i => (τ : ℂ)^W i) g := by
    rw [← hfg]
    exact modelGerm_scaled W (τ : ℂ) f hf hR hGd
  have hDiv : modelGerm hR hGd =
      (∑ j, modelGerm hR (hd.1 j) * modelGerm hR (hBs j)) + modelGerm hR hd.2 := by
    have hSum : (∑ j, modelGerm hR (hd.1 j) * modelGerm hR (hBs j)) =
        modelGerm hR (DifferentiableOn.fun_sum fun j (_ : j ∈ Finset.univ) =>
          (hd.1 j).mul (hBs j)) := by
      rw [modelGerm_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (modelGerm_mul hR (hd.1 j) (hBs j)).symm
    rw [hSum,← modelGerm_add]
    apply modelGerm_eq_of_eqOn hR hGd _
    intro z hz
    exact neumannSums_division hR D hHd hHb hM hGd hGb hz
  have hSupports := neumannSums_whole_support hR D hHd hHb hM hGd hGb
  let c := fun i => (τ : ℂ)^W i
  let invD := actualDiagonalPullback (fun i => (c i)⁻¹)
  let q := fun j => HolGerm.constHom (((τ : ℂ)^h j)⁻¹) * invD (modelGerm hR (hd.1 j))
  let r := invD (modelGerm hR hd.2)
  have hc : ∀ i, c i ≠ 0 := fun _ => pow_ne_zero _ hs0
  refine ⟨q,r,?_,?_,?_⟩
  · rw [hGermG] at hDiv
    simp_rw [hGermF] at hDiv
    exact inverse_diagonal_division c hc g (fun j => P.lift (e j))
      (fun j => modelGerm hR (hd.1 j)) (fun j => ((τ : ℂ)^h j)⁻¹)
      (modelGerm hR hd.2) hDiv
  · intro j β hβ
    exact inverse_diagonal_const_support c (((τ : ℂ)^h j)⁻¹)
      (modelGerm hR (hd.1 j)) β (hSupports.1 j β hβ)
  · intro β hβ
    change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t)
      (actualDiagonalPullback (fun i => (c i)⁻¹) (modelGerm hR hd.2))) = 0
    rw [coeff_actualDiagonalPullback,hSupports.2 β hβ,mul_zero]

/-- ORIGINAL I chooses the SAME fibre family BEFORE ALL original analytic numerator germs. -/
theorem exists_original_fibre_supported_division (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ P : FibreLiftUniformTailData d t I, ∀ g : HolGerm (ComplexModel (d+t)),
      ∃ (q : Fin (Fintype.card (LiftIndex d t I)) → HolGerm (ComplexModel (d+t)))
        (r : HolGerm (ComplexModel (d+t))),
        g = (∑ j, q j * P.lift (fibreEnumeration d t I j)) + r ∧
        (∀ j β, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
          (β + wordExponent (fibreHeadWords d t I j)) →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (q j)) = 0) ∧
        ∀ β, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) β →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) r) = 0 := by
  obtain ⟨P⟩ := exists_original_fibre_lift_uniform_tails d t I
  exact ⟨P,exists_supported_division_for_original_data d t I P⟩

end
end Hironaka.HironakaChowOriginalFibreSupportedDivision
