import Hironaka.Resolution.HironakaActualCauchyNeumannDivision
import Hironaka.Resolution.HironakaActualFormalCoordinatePowerDivision

/-!
# The same actual Cauchy-Neumann sums retain additive weight filtrations

The actual finite Cauchy masks shift coefficient weights by their literal
head exponents. The literal Neumann error recursion retains the numerator
filtration. Actual uniform coefficient limits retain these zeros for the
same analytic quotient and remainder sums, alongside their whole owner
support. No selected ideal standard-basis property is assumed.
-/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaActualCauchyFilteredNeumannDivision
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualCauchyCoefficientLimits
  HironakaActualCauchyNeumannDivision HironakaActualFormalCoordinatePowerDivision
variable {n k : ℕ}

/-- The actual coefficient masks lower quotient weights by the SAME head
weight and retain the numerator weight in the remainder. -/
theorem arrayPartition_weight_vanishing {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (heads : Fin k → CoordinateWord n) (w : Fin n → ℕ) (q : ℕ)
    {F : CoordinateSpace n → ℂ} (hF : DifferentiableOn ℂ F (ball 0 R))
    (hweight : actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hF) ∈
      actualFormalWeightVanishing w q) :
    (∀ j, actualUnshiftedTaylorAlgHom n
      (modelGerm (hρ.trans hρR) (arrayQuotient_differentiableOn hρ hρR heads j hF)) ∈
        actualFormalWeightVanishing w (q-Finsupp.weight w (wordExponent (heads j)))) ∧
    actualUnshiftedTaylorAlgHom n
      (modelGerm (hρ.trans hρR) (arrayRemainder_differentiableOn hρ hρR heads hF)) ∈
        actualFormalWeightVanishing w q := by
  constructor
  · intro j β hβ
    rw [coeff_arrayQuotientGerm hρ hρR heads j hF β]
    split_ifs
    · apply hweight
      rw [map_add]
      omega
    · rfl
  · intro β hβ
    rw [coeff_arrayRemainderGerm hρ hρR heads hF β]
    split_ifs
    · exact hweight β hβ
    · rfl

private theorem modelGerm_mul {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) :
    modelGerm hR (hf.mul hg) = modelGerm hR hf * modelGerm hR hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z * modelFunction g z) _ = _
  exact HolGerm.mk_mul _ _ _ _

private theorem modelGerm_neg {R : ℝ} (hR : 0 < R)
    {f : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R)) :
    modelGerm hR hf.neg = -modelGerm hR hf := by
  change HolGerm.mk (fun z : ComplexModel n => -modelFunction f z) _ = _
  exact HolGerm.mk_neg _ _

private theorem modelGerm_sum {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (f : ι → CoordinateSpace n → ℂ) (hf : ∀ i, DifferentiableOn ℂ (f i) (ball 0 R)) :
    modelGerm hR (DifferentiableOn.fun_sum fun i (_hi : i ∈ Finset.univ) => hf i) =
      ∑ i, modelGerm hR (hf i) := by
  change HolGerm.mk (fun z : ComplexModel n => ∑ i, modelFunction (f i) z) _ = _
  exact HolGerm.mk_sum Finset.univ _ (fun i => modelFunction_holAt hR (hf i))

/-- The exact original error iteration retains the numerator filtration.
This does not assume any standardness of the selected germs. -/
theorem diagramNeumannIter_weight_vanishing {R M : ℝ} (hR : 0 < R)
    {heads : Fin k → CoordinateWord n} (D : ConcreteNeumannData R heads)
    {H : Fin k → CoordinateSpace n → ℂ} (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {F : CoordinateSpace n → ℂ} (hM : 0 ≤ M) (hFd : DifferentiableOn ℂ F (ball 0 R))
    (hFb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖F z‖ ≤ M)
    (w : Fin n → ℕ) (q : ℕ)
    (hHweight : ∀ j, actualUnshiftedTaylorAlgHom n (modelGerm hR (hHd j)) ∈
      actualFormalWeightVanishing w (Finsupp.weight w (wordExponent (heads j))))
    (hFweight : actualUnshiftedTaylorAlgHom n (modelGerm hR hFd) ∈
      actualFormalWeightVanishing w q) (r : ℕ) :
    actualUnshiftedTaylorAlgHom n (modelGerm hR
      (diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hFd hFb r).1) ∈
        actualFormalWeightVanishing w q := by
  let hd := diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hFd hFb
  induction r with
  | zero => simpa only [diagramNeumannIter] using hFweight
  | succ r ih =>
    let hqd (j : Fin k) := arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) heads j (hd r).1
    have hq := (arrayPartition_weight_vanishing (half_pos hR) (half_lt_self hR)
      heads w q (hd r).1 ih).1
    have he : modelGerm hR (hd (r+1)).1 =
        -(∑ j, modelGerm hR (hHd j) * modelGerm hR (hqd j)) := by
      change modelGerm hR ((DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) =>
        (hHd j).fun_mul (hqd j)).fun_neg) = _
      rw [modelGerm_neg hR (DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) =>
        (hHd j).fun_mul (hqd j)), modelGerm_sum hR
          (fun j z => H j z * arrayQuotient (R/2) heads j (diagramNeumannIter R heads H F r) z)
          (fun j => (hHd j).fun_mul (hqd j))]
      congr 1
    rw [he, map_neg, map_sum]
    apply (actualFormalWeightVanishing w q).neg_mem
    apply (actualFormalWeightVanishing w q).sum_mem
    intro j _
    rw [map_mul]
    have hp := actualFormalWeightVanishing_mul_mem w
      (Finsupp.weight w (wordExponent (heads j)))
      (q-Finsupp.weight w (wordExponent (heads j)))
      (actualUnshiftedTaylorAlgHom n (modelGerm hR (hHd j)))
      (actualUnshiftedTaylorAlgHom n (modelGerm hR (hqd j))) (hHweight j) (hq j)
    intro β hβ
    apply hp β
    have hle : q ≤ Finsupp.weight w (wordExponent (heads j)) +
        (q-Finsupp.weight w (wordExponent (heads j))) := by omega
    exact hβ.trans_le hle

private theorem coeff_modelGerm_sum {R : ℝ} (hR : 0 < R)
    (f : ℕ → CoordinateSpace n → ℂ) (hf : ∀ r, DifferentiableOn ℂ (f r) (ball 0 R))
    (N : ℕ) (β : Fin n →₀ ℕ) :
    MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
      (modelGerm hR (DifferentiableOn.fun_sum fun r (_hr : r ∈ Finset.range N) => hf r))) =
      ∑ r ∈ Finset.range N, MvPowerSeries.coeff β
        (actualUnshiftedTaylorAlgHom n (modelGerm hR (hf r))) := by
  have hfm (r : ℕ) := modelFunction_holAt hR (hf r)
  change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
    (HolGerm.mk (fun z : Hironaka.ComplexModel n => ∑ r ∈ Finset.range N, modelFunction (f r) z)
      (eventually_differentiableAt_sum (Finset.range N) hfm))) = _
  rw [HolGerm.mk_sum (Finset.range N) _ hfm, map_sum, map_sum]
  rfl

/-- The SAME actual normally convergent quotient sums and remainder sum
retain their genuine whole shifted coefficient weight filtrations. -/
theorem neumannSums_weight_vanishing {R M : ℝ} (hR : 0 < R)
    {heads : Fin k → CoordinateWord n} (D : ConcreteNeumannData R heads)
    {H : Fin k → CoordinateSpace n → ℂ} (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {F : CoordinateSpace n → ℂ} (hM : 0 ≤ M) (hFd : DifferentiableOn ℂ F (ball 0 R))
    (hFb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖F z‖ ≤ M)
    (w : Fin n → ℕ) (q : ℕ)
    (hHweight : ∀ j, actualUnshiftedTaylorAlgHom n (modelGerm hR (hHd j)) ∈
      actualFormalWeightVanishing w (Finsupp.weight w (wordExponent (heads j))))
    (hFweight : actualUnshiftedTaylorAlgHom n (modelGerm hR hFd) ∈
      actualFormalWeightVanishing w q) :
    let hd := neumannSums_differentiableOn hR D hHd hHb hM hFd hFb
    (∀ j, actualUnshiftedTaylorAlgHom n (modelGerm hR (hd.1 j)) ∈
      actualFormalWeightVanishing w (q-Finsupp.weight w (wordExponent (heads j)))) ∧
    actualUnshiftedTaylorAlgHom n (modelGerm hR hd.2) ∈ actualFormalWeightVanishing w q := by
  have hk := diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hFd hFb
  have hw := diagramNeumannIter_weight_vanishing hR D hHd hHb hM hFd hFb w q hHweight hFweight
  have hparts (r : ℕ) := arrayPartition_weight_vanishing (half_pos hR) (half_lt_self hR)
    heads w q (hk r).1 (hw r)
  have hqb (r : ℕ) (j : Fin k) (z : CoordinateSpace n) (hz : z ∈ ball 0 R) :
      ‖arrayQuotient (R/2) heads j (diagramNeumannIter R heads H F r) z‖ ≤
        (D.quotientConstant j*M)*(1/2 : ℝ)^r := by
    exact (D.quotient_bound _ _ (hk r).1 (hk r).2 j z hz).trans_eq (by ring)
  have hrb (r : ℕ) (z : CoordinateSpace n) (hz : z ∈ ball 0 R) :
      ‖arrayRemainder (R/2) heads (diagramNeumannIter R heads H F r) z‖ ≤
        (D.remainderConstant*M)*(1/2 : ℝ)^r := by
    exact (D.remainder_bound _ _ (hk r).1 (hk r).2 z hz).trans_eq (by ring)
  have hsum : Summable fun r : ℕ => (1/2 : ℝ)^r := summable_geometric_two
  have hd := neumannSums_differentiableOn hR D hHd hHb hM hFd hFb
  constructor
  · intro j β hβ
    let f (r : ℕ) := arrayQuotient (R/2) heads j (diagramNeumannIter R heads H F r)
    have hf (r : ℕ) := arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) heads j (hk r).1
    have hu := tendstoUniformlyOn_tsum_nat (hsum.mul_left (D.quotientConstant j*M))
      (s := ball (0 : CoordinateSpace n) R) (fun r z hz => hqb r j z hz)
    apply coeff_eq_zero_of_uniform_limit (half_pos hR) (half_lt_self hR)
      (fun N => DifferentiableOn.fun_sum fun r (_hr : r ∈ Finset.range N) => hf r) (hd.1 j) hu β
    intro N
    rw [coeff_modelGerm_sum hR f hf N β]
    apply Finset.sum_eq_zero
    intro r _
    exact (hparts r).1 j β hβ
  · intro β hβ
    let f (r : ℕ) := arrayRemainder (R/2) heads (diagramNeumannIter R heads H F r)
    have hf (r : ℕ) := arrayRemainder_differentiableOn (half_pos hR) (half_lt_self hR) heads (hk r).1
    have hu := tendstoUniformlyOn_tsum_nat (hsum.mul_left (D.remainderConstant*M))
      (s := ball (0 : CoordinateSpace n) R) (fun r z hz => hrb r z hz)
    apply coeff_eq_zero_of_uniform_limit (half_pos hR) (half_lt_self hR)
      (fun N => DifferentiableOn.fun_sum fun r (_hr : r ∈ Finset.range N) => hf r) hd.2 hu β
    intro N
    rw [coeff_modelGerm_sum hR f hf N β]
    apply Finset.sum_eq_zero
    intro r _
    exact (hparts r).2 β hβ

end
end Hironaka.HironakaActualCauchyFilteredNeumannDivision
