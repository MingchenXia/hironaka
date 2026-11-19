import Hironaka.Resolution.HironakaActualInheritedSmallTails
import Hironaka.Resolution.HironakaActualOriginalScaledAnalyticDivision
import Hironaka.Resolution.HironakaActualDiagonalTaylor
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
import Mathlib.Analysis.Analytic.Uniqueness

/-! The actual source Neumann remainder of a bounded holomorphic combination
of the SAME inherited full family vanishes on the entire source ball.
The original ideal and literal whole span produce membership internally;
inverse diagonal pullback retains off-source-diagram coefficient vanishing.
No scaled/nearby diagram identity, HS value or zero-remainder certificate
is supplied. This is a lower producer for BP3, not a separate BP node.
Initial source-only draft: no elaboration or acceptance is claimed. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedSourceCauchyRemainder
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm OkaRelationSheaf HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualFiniteDegLexWeights HironakaActualWeightedScaling
  HironakaActualWeightedVertexSmallTails HironakaActualCauchyCoordinateDivision
  HironakaActualCauchyTaylorSupport HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaActualCauchyEnumeratedPartition
  HironakaActualCauchyNeumannDivision HironakaActualDiagonalTaylor
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedSmallTails
  HironakaActualOriginalScaledAnalyticDivision HironakaActualAnalyticFormalNormalPowers

variable {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
variable {G : ActualAnalyticInheritedFamily n 0
  (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)}

/-- Literal SAME scaled representatives in the already fixed original vertex enumeration. -/
def actualInheritedSourceScaledFamily (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (j : Fin (actualVertexCount n I)) : CoordinateSpace n → ℂ :=
  inheritedNormalizedScaledRepresentative P (actualVertexEnumeration n I j) s

/-- The actual original weighted tails, without any translated head assumptions. -/
def actualInheritedSourceScaledTail (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (j : Fin (actualVertexCount n I)) (z : CoordinateSpace n) : ℂ :=
  s * P.tailFactor (actualVertexEnumeration n I j) (z,s)

/-- The genuine source numerator for an actual analytic coefficient tuple. -/
def actualInheritedSourceCombination (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ) (z : CoordinateSpace n) : ℂ :=
  ∑ j, A j z * actualInheritedSourceScaledFamily P s j z

theorem actualInheritedSourceScaledFamily_differentiableOn
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s ∈ ball 0 P.radius)
    (j : Fin (actualVertexCount n I)) :
    DifferentiableOn ℂ (actualInheritedSourceScaledFamily P s j) (ball 0 P.radius) := by
  have hgraph : Differentiable ℂ (fun z : CoordinateSpace n => (z,s)) :=
    differentiable_id.prodMk (differentiable_const s)
  have hd := (P.scaled_hol (actualVertexEnumeration n I j)).comp hgraph.differentiableOn
    (fun z hz => ⟨hz,hs⟩)
  unfold actualInheritedSourceScaledFamily inheritedNormalizedScaledRepresentative
  simp only [div_eq_mul_inv]
  exact hd.mul_const _

theorem actualInheritedSourceScaledTail_differentiableOn
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s ∈ ball 0 P.radius)
    (j : Fin (actualVertexCount n I)) :
    DifferentiableOn ℂ (actualInheritedSourceScaledTail P s j) (ball 0 P.radius) := by
  have hgraph : Differentiable ℂ (fun z : CoordinateSpace n => (z,s)) :=
    differentiable_id.prodMk (differentiable_const s)
  have hd := (P.factor_hol (actualVertexEnumeration n I j)).comp hgraph.differentiableOn
    (fun z hz => ⟨hz,hs⟩)
  exact (differentiable_const s).differentiableOn.fun_mul hd

theorem actualInheritedSourceScaledFamily_eq_monomial_add_tail
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs0 : s ≠ 0)
    (hs : s ∈ ball 0 P.radius) (j : Fin (actualVertexCount n I))
    {z : CoordinateSpace n} (hz : z ∈ ball 0 P.radius) :
    actualInheritedSourceScaledFamily P s j z = wordMonomial (actualVertexWords n I j) z +
      actualInheritedSourceScaledTail P s j z := by
  have he := P.weighted_identity (actualVertexEnumeration n I j) (z,s) ⟨hz,hs⟩
  unfold actualInheritedSourceScaledFamily inheritedNormalizedScaledRepresentative
  rw [he, mul_div_cancel_left₀ _ (pow_ne_zero _ hs0)]
  rw [actualVertexWords, wordMonomial_wordOfExponent]
  rfl

private theorem weighted_joint_eq_diagonal (W : Fin n → ℕ) (s : ℂ)
    (z : ComplexModel n) :
    actualWeightedScalingMap W
      (jointPoint n (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,s)) =
      actualDiagonalMap (fun i => s ^ W i) z := by
  ext i
  let p : CoordinateSpace n × ℂ :=
    (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,s)
  have hp : jointPoint n p (parameterIndex n) = s := by
    change (Fin.addCases (motive := fun _ : Fin (n+1) =>
      CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ)
      ((0 : Fin 1).natAdd n)) p = s
    rw [Fin.addCases_right]
    rfl
  have hb : jointPoint n p (i.castAdd 1) = z i := by
    change (Fin.addCases (motive := fun _ : Fin (n+1) =>
      CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ)
      (i.castAdd 1)) p = z i
    rw [Fin.addCases_left]
    rfl
  change jointPoint n p (parameterIndex n) ^ W i *
    jointPoint n p (i.castAdd 1) = s ^ W i * z i
  rw [hp,hb]

/-- A genuine WHOLE representative identity for the SAME chosen source family;
the real diagonal map is proved from actual joint coordinates. -/
theorem actualInheritedSourceScaledFamily_modelGerm
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s ∈ ball 0 P.radius)
    (j : Fin (actualVertexCount n I)) :
    modelGerm P.radius_pos (actualInheritedSourceScaledFamily_differentiableOn P hs j) =
      HolGerm.constHom ((s ^ weightedDegree (degLexWeight n P.germs.degreeBound)
        (actualVertexEnumeration n I j).val)⁻¹) *
      actualDiagonalPullback (fun i => s ^ degLexWeight n P.germs.degreeBound i)
        (G.germs (actualVertexEnumeration n I j)) := by
  let a : ActualVertexIndex n I := actualVertexEnumeration n I j
  let W := degLexWeight n P.germs.degreeBound
  let c : Fin n → ℂ := fun i => s ^ W i
  let u : ℂ := (s ^ weightedDegree W a.val)⁻¹
  have hrep : HolGerm.mk (P.representative a) (P.representative_hol a) = G.germs a :=
    P.representative_eq a
  have hbase :
      modelGerm P.radius_pos (actualInheritedSourceScaledFamily_differentiableOn P hs j) =
        HolGerm.constHom u * actualDiagonalPullback c
          (HolGerm.mk (P.representative a) (P.representative_hol a)) := by
    unfold actualDiagonalPullback
    rw [HironakaHolomorphicJetChartInvariance.compAlgHom_mk,
      ← HolGerm.mk_const, ← HolGerm.mk_mul]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      change P.representative a
          (actualWeightedScalingMap W
            (jointPoint n (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,s))) /
          s ^ weightedDegree W a.val = u * P.representative a (actualDiagonalMap c z)
      calc
        _ = P.representative a (actualDiagonalMap c z) /
            s ^ weightedDegree W a.val :=
          congrArg (fun v : ComplexModel n => P.representative a v /
            s ^ weightedDegree W a.val) (weighted_joint_eq_diagonal W s z)
        _ = _ := by
          change _ / (s ^ weightedDegree W a.val) =
            (s ^ weightedDegree W a.val)⁻¹ * _
          rw [div_eq_mul_inv, mul_comm]
  exact hbase.trans (congrArg (fun F : HolGerm (ComplexModel n) =>
    HolGerm.constHom u * actualDiagonalPullback c F) hrep)

private theorem modelGerm_eq_sum_mul {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    {f : CoordinateSpace n → ℂ} {q g : ι → CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hq : ∀ j, DifferentiableOn ℂ (q j) (ball 0 R))
    (hg : ∀ j, DifferentiableOn ℂ (g j) (ball 0 R))
    (he : ∀ z ∈ ball (0 : CoordinateSpace n) R, f z = ∑ j, q j z * g j z) :
    modelGerm hR hf = ∑ j, modelGerm hR (hq j) * modelGerm hR (hg j) := by
  have hp (j : ι) := eventually_differentiableAt_mul
    (modelFunction_holAt hR (hq j)) (modelFunction_holAt hR (hg j))
  have hsum := eventually_differentiableAt_sum Finset.univ hp
  change HolGerm.mk (modelFunction f) (modelFunction_holAt hR hf) = _
  calc
    _ = HolGerm.mk (fun z : ComplexModel n =>
        ∑ j, modelFunction (q j) z * modelFunction (g j) z) hsum := by
      apply HolGerm.mk_eq_mk_iff.mpr
      let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
      have ht : Tendsto e (𝓝 (0 : ComplexModel n)) (𝓝 (0 : CoordinateSpace n)) := by
        simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
      filter_upwards [ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hR))] with z hz
      exact he (e z) hz
    _ = _ := by
      rw [HolGerm.mk_sum Finset.univ _ hp]
      apply Finset.sum_congr rfl
      intro j _
      exact HolGerm.mk_mul _ _ _ _

private theorem zero_on_ball_of_modelGerm_zero {R : ℝ} (hR : 0 < R)
    {f : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hzero : modelGerm hR hf = 0) : ∀ z ∈ ball (0 : CoordinateSpace n) R, f z = 0 := by
  rw [modelGerm, ← HolGerm.mk_zero] at hzero
  have hev := HolGerm.mk_eq_mk_iff.mp hzero
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  have ht : Tendsto e.symm (𝓝 (0 : CoordinateSpace n)) (𝓝 (0 : ComplexModel n)) := by
    simpa only [map_zero] using e.symm.continuous.tendsto (0 : CoordinateSpace n)
  have hfg : f =ᶠ[𝓝 (0 : CoordinateSpace n)] (fun _ => (0 : ℂ)) := by
    filter_upwards [ht.eventually hev] with z hz
    change f (e (e.symm z)) = 0 at hz
    simpa only [e.apply_symm_apply] using hz
  have haf : AnalyticOnNhd ℂ f (ball 0 R) := fun z hz =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn isOpen_ball hf hz
  have ha0 : AnalyticOnNhd ℂ (fun _ : CoordinateSpace n => (0 : ℂ)) (ball 0 R) :=
    fun _ _ => analyticAt_const
  exact haf.eqOn_of_preconnected_of_eventuallyEq ha0 (convex_ball 0 R).isPreconnected
    (mem_ball_self hR) hfg

/-- The ACTUAL source remainder of every bounded actual holomorphic combination
of the SAME full family is WHOLE zero on the unchanged source ball. All ideal
membership and off-diagram contradiction are derived from the original hspan;
there is no scaled-diagram or desired zero-remainder premise. -/
theorem actual_inherited_source_neumann_remainder_eq_zero
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (hspan : Ideal.span (range G.germs) = I)
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs0 : s ≠ 0)
    (hs : s ∈ ball 0 P.radius)
    (D : ConcreteNeumannData P.radius (actualVertexWords n I))
    (hsmall : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceScaledTail P s j z‖ ≤ D.epsilon)
    (A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ)
    (hA : ∀ j, DifferentiableOn ℂ (A j) (ball 0 P.radius))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceCombination P s A z‖ ≤ M) :
    ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      neumannRemainderSum P.radius (actualVertexWords n I)
        (actualInheritedSourceScaledTail P s) (actualInheritedSourceCombination P s A) z = 0 := by
  let w := actualVertexWords n I
  let H := actualInheritedSourceScaledTail P s
  let F := actualInheritedSourceCombination P s A
  let g := actualInheritedSourceScaledFamily P s
  have hH (j : Fin (actualVertexCount n I)) : DifferentiableOn ℂ (H j) (ball 0 P.radius) :=
    actualInheritedSourceScaledTail_differentiableOn P hs j
  have hg (j : Fin (actualVertexCount n I)) : DifferentiableOn ℂ (g j) (ball 0 P.radius) :=
    actualInheritedSourceScaledFamily_differentiableOn P hs j
  have hF : DifferentiableOn ℂ F (ball 0 P.radius) :=
    DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) => (hA j).mul (hg j)
  have hd := neumannSums_differentiableOn P.radius_pos D hH hsmall hM hF hbound
  have hsupport := neumannSums_whole_support P.radius_pos D hH hsmall hM hF hbound
  let q := neumannQuotientSum P.radius w H F
  let r := neumannRemainderSum P.radius w H F
  have hdiv : ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      F z = (∑ j, q j z * g j z) + r z := by
    intro z hz
    calc
      F z = (∑ j, q j z * (wordMonomial (w j) z + H j z)) + r z :=
        neumannSums_division P.radius_pos D hH hsmall hM hF hbound hz
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [← actualInheritedSourceScaledFamily_eq_monomial_add_tail P hs0 hs j hz]
  have hrSum : ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      r z = ∑ j, (A j z - q j z) * g j z := by
    intro z hz
    have he := hdiv z hz
    calc
      r z = F z - (∑ j, q j z * g j z) := by linear_combination -he
      _ = _ := by
        change (∑ j, A j z * g j z) - (∑ j, q j z * g j z) = _
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
  let rG := modelGerm P.radius_pos hd.2
  have hRG : rG = ∑ j, modelGerm P.radius_pos ((hA j).sub (hd.1 j)) *
      modelGerm P.radius_pos (hg j) :=
    modelGerm_eq_sum_mul P.radius_pos hd.2 (fun j => (hA j).sub (hd.1 j)) hg hrSum
  let W := degLexWeight n P.germs.degreeBound
  let c : Fin n → ℂ := fun i => s ^ W i
  have hc (i : Fin n) : c i ≠ 0 := pow_ne_zero _ hs0
  let E := actualDiagonalPullback (fun i => (c i)⁻¹)
  have hEg (j : Fin (actualVertexCount n I)) :
      E (modelGerm P.radius_pos (hg j)) =
        HolGerm.constHom ((s ^ weightedDegree W (actualVertexEnumeration n I j).val)⁻¹) *
          G.germs (actualVertexEnumeration n I j) := by
    change actualDiagonalPullback (fun i => (c i)⁻¹) _ = _
    rw [actualInheritedSourceScaledFamily_modelGerm P hs j, map_mul,
      actualDiagonalPullback_const, actualDiagonalPullback_inverse c hc]
  have hGmem (a : ActualVertexIndex n I) : G.germs a ∈ I := by
    exact hspan.le (Ideal.subset_span ⟨a,rfl⟩)
  have hER : E rG ∈ I := by
    have he := congrArg E hRG
    simp only [map_sum, map_mul] at he
    rw [he]
    apply Ideal.sum_mem
    intro j _
    rw [hEg j]
    exact I.mul_mem_left _ (I.mul_mem_left _ (hGmem (actualVertexEnumeration n I j)))
  have hERsupport : ∀ β ∈ actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (E rG)) = 0 := by
    intro β hβ
    change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
      (actualDiagonalPullback (fun i => (c i)⁻¹) rG)) = 0
    rw [coeff_actualDiagonalPullback]
    have hrzero : MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n rG) = 0 := by
      apply hsupport.2 β
      intro havoid
      exact (actualVertexWords_avoids_iff n I β).mp havoid hβ
    rw [hrzero, mul_zero]
  have hERzero : E rG = 0 := by
    by_contra hne
    have hTne : actualUnshiftedTaylorAlgHom n (E rG) ≠ 0 := by
      intro hT
      apply hne
      apply actualUnshiftedTaylorAlgHom_injective n
      simpa only [map_zero] using hT
    have hdiagram : actualInitialExponent MonomialOrder.degLex
        (actualUnshiftedTaylorAlgHom n (E rG)) hTne ∈
        actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) :=
      ⟨_, Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hER, hTne, rfl⟩
    exact (actualInitialExponent_spec MonomialOrder.degLex _ hTne).1
      (hERsupport _ hdiagram)
  have hundo : actualDiagonalPullback c (E rG) = rG := by
    simpa only [E, inv_inv] using actualDiagonalPullback_inverse
      (fun i => (c i)⁻¹) (fun i => inv_ne_zero (hc i)) rG
  have hrGzero : rG = 0 := by
    have he := congrArg (actualDiagonalPullback c) hERzero
    rwa [hundo, map_zero] at he
  exact zero_on_ball_of_modelGerm_zero P.radius_pos hd.2 hrGzero

end
end Hironaka.HironakaActualInheritedSourceCauchyRemainder
