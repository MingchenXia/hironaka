import Hironaka.Resolution.HironakaActualCauchyEnumeratedPartition
import Hironaka.Resolution.HironakaActualCauchyCoefficientLimits
import Hironaka.Analytic.WeierstrassDivisionAbstract

/-!
# Actual multigenerator Cauchy-Neumann division

The operators are the literal finite Cauchy partition, not supplied operators.
The contraction threshold is produced from their actual same-domain constants.
Normally convergent actual sums and coefficientwise uniform-limit support give
analytic quotients and remainder. Original-ideal small tails are coupled below
in a separate original-only producer.
-/

set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualCauchyNeumannDivision

noncomputable section
attribute [local instance] Classical.propDecidable

open HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyCoordinateDivision
  HironakaActualCauchyTaylorSupport HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualCauchyCoefficientLimits

variable {n k : ℕ}

structure ConcreteNeumannData (R : ℝ) (w : Fin k → CoordinateWord n) where
  quotientConstant : Fin k → ℝ
  quotientConstant_nonneg : ∀ j, 0 ≤ quotientConstant j
  remainderConstant : ℝ
  remainderConstant_nonneg : 0 ≤ remainderConstant
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  contraction : epsilon * (∑ j, quotientConstant j) ≤ 1/2
  quotient_bound : ∀ (M : ℝ) (f : CoordinateSpace n → ℂ), DifferentiableOn ℂ f (ball 0 R) →
    (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖f z‖ ≤ M) →
    ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖arrayQuotient (R/2) w j f z‖ ≤ quotientConstant j * M
  remainder_bound : ∀ (M : ℝ) (f : CoordinateSpace n → ℂ), DifferentiableOn ℂ f (ball 0 R) →
    (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖f z‖ ≤ M) →
    ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖arrayRemainder (R/2) w f z‖ ≤ remainderConstant * M

/-- A genuine contraction threshold and actual Cauchy bounds are produced before any tails or input h. -/
theorem nonempty_concreteNeumannData (R : ℝ) (hR : 0 < R) (w : Fin k → CoordinateWord n) :
    Nonempty (ConcreteNeumannData R w) := by
  obtain ⟨C,Cr,hC,hCr,hbounds⟩ := exists_array_partition_bounds (half_pos hR) (half_lt_self hR) w
  let S := ∑ j, C j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hC j
  let ε := 1 / (4 * (1 + S))
  have hden : 0 < 4 * (1 + S) := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  have hcontract : ε * S ≤ 1/2 := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div,one_mul,div_le_iff₀ hden]
    nlinarith
  exact ⟨{
    quotientConstant := C
    quotientConstant_nonneg := hC
    remainderConstant := Cr
    remainderConstant_nonneg := hCr
    epsilon := ε
    epsilon_pos := hε
    contraction := hcontract
    quotient_bound := fun M f hf hM => (hbounds M f hf hM).1
    remainder_bound := fun M f hf hM => (hbounds M f hf hM).2 }⟩

def diagramNeumannIter (R : ℝ) (w : Fin k → CoordinateWord n)
    (H : Fin k → CoordinateSpace n → ℂ) (h : CoordinateSpace n → ℂ) : ℕ → CoordinateSpace n → ℂ
  | 0 => h
  | r+1 => fun z => -(∑ j, H j z * arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z)

theorem diagramNeumannIter_differentiableOn_and_norm_le {R M : ℝ} (hR : 0 < R)
    {w : Fin k → CoordinateWord n} (D : ConcreteNeumannData R w)
    {H : Fin k → CoordinateSpace n → ℂ} (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {h : CoordinateSpace n → ℂ} (hM : 0 ≤ M) (hhd : DifferentiableOn ℂ h (ball 0 R))
    (hhb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) (r : ℕ) :
    DifferentiableOn ℂ (diagramNeumannIter R w H h r) (ball 0 R) ∧
      ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖diagramNeumannIter R w H h r z‖ ≤ M * (1/2 : ℝ)^r := by
  induction r with
  | zero => exact ⟨hhd,fun z hz => by simpa [diagramNeumannIter] using hhb z hz⟩
  | succ r ih =>
    have hq (j : Fin k) := arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) w j ih.1
    refine ⟨(DifferentiableOn.fun_sum fun j _ => (hHd j).fun_mul (hq j)).fun_neg,?_⟩
    intro z hz
    have hpow : 0 ≤ M * (1/2 : ℝ)^r := by positivity
    change ‖-(∑ j, H j z * arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z)‖ ≤ _
    rw [norm_neg]
    calc
      _ ≤ ∑ j, ‖H j z * arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z‖ := norm_sum_le _ _
      _ ≤ ∑ j, D.epsilon * (D.quotientConstant j * (M * (1/2 : ℝ)^r)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hHb j z hz) (D.quotient_bound _ _ ih.1 ih.2 j z hz)
          (norm_nonneg _) D.epsilon_pos.le
      _ = (D.epsilon * (∑ j, D.quotientConstant j)) * (M * (1/2 : ℝ)^r) := by
        simp only [Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (1/2) * (M * (1/2 : ℝ)^r) := mul_le_mul_of_nonneg_right D.contraction hpow
      _ = M * (1/2 : ℝ)^(r+1) := by rw [pow_succ]; ring

theorem diagramNeumannIter_eq_step (R : ℝ) (w : Fin k → CoordinateWord n)
    (H : Fin k → CoordinateSpace n → ℂ) (h : CoordinateSpace n → ℂ) (r : ℕ) (z : CoordinateSpace n) :
    diagramNeumannIter R w H h r z =
      (∑ j, arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z *
        (wordMonomial (w j) z + H j z)) +
      arrayRemainder (R/2) w (diagramNeumannIter R w H h r) z +
      diagramNeumannIter R w H h (r+1) z := by
  have he := array_division_identity (R/2) w (diagramNeumannIter R w H h r) z
  have hsum : (∑ j, arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z *
      (wordMonomial (w j) z + H j z)) =
      (∑ j, wordMonomial (w j) z * arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z) +
      (∑ j, H j z * arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  simp only [diagramNeumannIter]
  linear_combination he

theorem diagramNeumannIter_telescope (R : ℝ) (w : Fin k → CoordinateWord n)
    (H : Fin k → CoordinateSpace n → ℂ) (h : CoordinateSpace n → ℂ) (N : ℕ) (z : CoordinateSpace n) :
    h z = (∑ j, (∑ r ∈ Finset.range N,
      arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z) * (wordMonomial (w j) z + H j z)) +
      (∑ r ∈ Finset.range N, arrayRemainder (R/2) w (diagramNeumannIter R w H h r) z) +
      diagramNeumannIter R w H h N z := by
  induction N with
  | zero => simp [diagramNeumannIter]
  | succ N ih =>
    rw [ih,diagramNeumannIter_eq_step R w H h N z]
    simp only [Finset.sum_range_succ,add_mul,Finset.sum_add_distrib]
    ring

def neumannQuotientSum (R : ℝ) (w : Fin k → CoordinateWord n)
    (H : Fin k → CoordinateSpace n → ℂ) (h : CoordinateSpace n → ℂ) (j : Fin k)
    (z : CoordinateSpace n) : ℂ :=
  ∑' r, arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z

def neumannRemainderSum (R : ℝ) (w : Fin k → CoordinateWord n)
    (H : Fin k → CoordinateSpace n → ℂ) (h : CoordinateSpace n → ℂ)
    (z : CoordinateSpace n) : ℂ :=
  ∑' r, arrayRemainder (R/2) w (diagramNeumannIter R w H h r) z

private theorem component_bounds {R M : ℝ} (hR : 0 < R)
    {w : Fin k → CoordinateWord n} (D : ConcreteNeumannData R w)
    {H : Fin k → CoordinateSpace n → ℂ} (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {h : CoordinateSpace n → ℂ} (hM : 0 ≤ M) (hhd : DifferentiableOn ℂ h (ball 0 R))
    (hhb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) :
    (∀ r j, ∀ z ∈ ball (0 : CoordinateSpace n) R,
      ‖arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z‖ ≤
        (D.quotientConstant j * M) * (1/2 : ℝ)^r) ∧
    ∀ r, ∀ z ∈ ball (0 : CoordinateSpace n) R,
      ‖arrayRemainder (R/2) w (diagramNeumannIter R w H h r) z‖ ≤
        (D.remainderConstant * M) * (1/2 : ℝ)^r := by
  have hk := diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hhd hhb
  exact ⟨fun r j z hz => (D.quotient_bound _ _ (hk r).1 (hk r).2 j z hz).trans_eq (by ring),
    fun r z hz => (D.remainder_bound _ _ (hk r).1 (hk r).2 z hz).trans_eq (by ring)⟩

theorem neumannSums_differentiableOn {R M : ℝ} (hR : 0 < R)
    {w : Fin k → CoordinateWord n} (D : ConcreteNeumannData R w)
    {H : Fin k → CoordinateSpace n → ℂ} (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {h : CoordinateSpace n → ℂ} (hM : 0 ≤ M) (hhd : DifferentiableOn ℂ h (ball 0 R))
    (hhb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) :
    (∀ j, DifferentiableOn ℂ (neumannQuotientSum R w H h j) (ball 0 R)) ∧
      DifferentiableOn ℂ (neumannRemainderSum R w H h) (ball 0 R) := by
  have hk := diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hhd hhb
  obtain ⟨hqb,hrb⟩ := component_bounds hR D hHd hHb hM hhd hhb
  have hsum : Summable fun r : ℕ => (1/2 : ℝ)^r := summable_geometric_two
  refine ⟨fun j z hz => ?_,fun z hz => ?_⟩
  · exact (differentiableAt_tsum_of_forall_norm_le isOpen_ball (hsum.mul_left (D.quotientConstant j * M))
      (fun r => arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) w j (hk r).1)
      (fun r => hqb r j) hz).differentiableWithinAt
  · exact (differentiableAt_tsum_of_forall_norm_le isOpen_ball (hsum.mul_left (D.remainderConstant * M))
      (fun r => arrayRemainder_differentiableOn (half_pos hR) (half_lt_self hR) w (hk r).1)
      hrb hz).differentiableWithinAt

theorem neumannSums_division {R M : ℝ} (hR : 0 < R)
    {w : Fin k → CoordinateWord n} (D : ConcreteNeumannData R w)
    {H : Fin k → CoordinateSpace n → ℂ} (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {h : CoordinateSpace n → ℂ} (hM : 0 ≤ M) (hhd : DifferentiableOn ℂ h (ball 0 R))
    (hhb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M)
    {z : CoordinateSpace n} (hz : z ∈ ball 0 R) :
    h z = ∑ j, neumannQuotientSum R w H h j z * (wordMonomial (w j) z + H j z) +
      neumannRemainderSum R w H h z := by
  have hk := diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hhd hhb
  obtain ⟨hqb,hrb⟩ := component_bounds hR D hHd hHb hM hhd hhb
  have hsum : Summable fun r : ℕ => (1/2 : ℝ)^r := summable_geometric_two
  have hlim : Tendsto (fun N => (∑ j, (∑ r ∈ Finset.range N,
      arrayQuotient (R/2) w j (diagramNeumannIter R w H h r) z) * (wordMonomial (w j) z + H j z)) +
      (∑ r ∈ Finset.range N, arrayRemainder (R/2) w (diagramNeumannIter R w H h r) z) +
      diagramNeumannIter R w H h N z) atTop
      (nhds ((∑ j, neumannQuotientSum R w H h j z * (wordMonomial (w j) z + H j z)) +
        neumannRemainderSum R w H h z + 0)) := by
    refine ((tendsto_finsetSum _ fun j _ => Tendsto.mul_const _ ?_).add ?_).add ?_
    · exact ((hsum.mul_left _).of_norm_bounded fun r => hqb r j z hz).hasSum.tendsto_sum_nat
    · exact ((hsum.mul_left _).of_norm_bounded fun r => hrb r z hz).hasSum.tendsto_sum_nat
    · refine squeeze_zero_norm (fun N => (hk N).2 z hz) ?_
      have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).const_mul M
      rwa [mul_zero] at ht
  rw [add_zero] at hlim
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun N =>
    diagramNeumannIter_telescope R w H h N z) hlim

private theorem coeff_modelGerm_sum {R : ℝ} (hR : 0 < R)
    (f : ℕ → CoordinateSpace n → ℂ) (hf : ∀ r, DifferentiableOn ℂ (f r) (ball 0 R))
    (N : ℕ) (b : Fin n →₀ ℕ) :
    MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n
      (modelGerm hR (DifferentiableOn.fun_sum fun r (_hr : r ∈ Finset.range N) => hf r))) =
      ∑ r ∈ Finset.range N, MvPowerSeries.coeff b
        (actualUnshiftedTaylorAlgHom n (modelGerm hR (hf r))) := by
  have hfm (r : ℕ) := modelFunction_holAt hR (hf r)
  change MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n
    (HolGerm.mk (fun z : Hironaka.ComplexModel n => ∑ r ∈ Finset.range N, modelFunction (f r) z)
      (eventually_differentiableAt_sum (Finset.range N) hfm))) = _
  rw [HolGerm.mk_sum (Finset.range N) _ hfm,map_sum,map_sum]
  rfl

theorem neumannSums_whole_support {R M : ℝ} (hR : 0 < R)
    {w : Fin k → CoordinateWord n} (D : ConcreteNeumannData R w)
    {H : Fin k → CoordinateSpace n → ℂ} (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {h : CoordinateSpace n → ℂ} (hM : 0 ≤ M) (hhd : DifferentiableOn ℂ h (ball 0 R))
    (hhb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) :
    let hd := neumannSums_differentiableOn hR D hHd hHb hM hhd hhb
    (∀ j b, ¬ AvoidsCones ((List.ofFn w).take j.val) (b + wordExponent (w j)) →
      MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n (modelGerm hR (hd.1 j))) = 0) ∧
    ∀ b, ¬ AvoidsCones (List.ofFn w) b →
      MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n (modelGerm hR hd.2)) = 0 := by
  have hk := diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hhd hhb
  obtain ⟨hqb,hrb⟩ := component_bounds hR D hHd hHb hM hhd hhb
  have hsum : Summable fun r : ℕ => (1/2 : ℝ)^r := summable_geometric_two
  have hd := neumannSums_differentiableOn hR D hHd hHb hM hhd hhb
  constructor
  · intro j b hbad
    let f (r : ℕ) := arrayQuotient (R/2) w j (diagramNeumannIter R w H h r)
    have hf (r : ℕ) := arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) w j (hk r).1
    have hu := tendstoUniformlyOn_tsum_nat (hsum.mul_left (D.quotientConstant j * M))
      (s := ball (0 : CoordinateSpace n) R) (fun r z hz => hqb r j z hz)
    apply coeff_eq_zero_of_uniform_limit (half_pos hR) (half_lt_self hR)
      (fun N => DifferentiableOn.fun_sum fun r (_hr : r ∈ Finset.range N) => hf r) (hd.1 j) hu b
    intro N
    rw [coeff_modelGerm_sum hR f hf N b]
    apply Finset.sum_eq_zero
    intro r _
    rw [coeff_arrayQuotientGerm (half_pos hR) (half_lt_self hR) w j (hk r).1 b,if_neg hbad]
  · intro b hbad
    let f (r : ℕ) := arrayRemainder (R/2) w (diagramNeumannIter R w H h r)
    have hf (r : ℕ) := arrayRemainder_differentiableOn (half_pos hR) (half_lt_self hR) w (hk r).1
    have hu := tendstoUniformlyOn_tsum_nat (hsum.mul_left (D.remainderConstant * M))
      (s := ball (0 : CoordinateSpace n) R) (fun r z hz => hrb r z hz)
    apply coeff_eq_zero_of_uniform_limit (half_pos hR) (half_lt_self hR)
      (fun N => DifferentiableOn.fun_sum fun r (_hr : r ∈ Finset.range N) => hf r) hd.2 hu b
    intro N
    rw [coeff_modelGerm_sum hR f hf N b]
    apply Finset.sum_eq_zero
    intro r _
    rw [coeff_arrayRemainderGerm (half_pos hR) (half_lt_self hR) w (hk r).1 b,if_neg hbad]

end

end Hironaka.HironakaActualCauchyNeumannDivision
