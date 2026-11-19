import Hironaka.Resolution.HironakaActualCauchyNeumannDivision
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
import Mathlib.Analysis.Analytic.Uniqueness

/-! Native monomial-partition reconstruction and bounded supported uniqueness
for the SAME concrete Cauchy operators on ONE unchanged ball. The tails need
only the public ConcreteNeumannData bounds. No target monic heads, nearby
diagram, HS value, abstract inverse or translated-formal-series certificate.
This is a lower analytic uniqueness node, not a neighborhood HS producer.
Blueprint: hironaka-actual-inherited-neighborhood-hs-cosupport-extension.tex.
Source-only initial draft: no Lean elaboration or acceptance is claimed. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualBoundedSupportedNeumannUniqueness
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualCauchyNeumannDivision
  HironakaActualAnalyticFormalNormalPowers
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

private theorem modelGerm_sub {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R)) :
    modelGerm hR (hf.sub hg) = modelGerm hR hf - modelGerm hR hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z - modelFunction g z) _ = _
  exact HolGerm.mk_sub _ _ _ _

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

private theorem eqOn_of_modelGerm_eq {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (he : modelGerm hR hf = modelGerm hR hg) : EqOn f g (ball 0 R) := by
  have hev := HolGerm.mk_eq_mk_iff.mp he
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  have ht : Tendsto e.symm (𝓝 (0 : CoordinateSpace n)) (𝓝 (0 : ComplexModel n)) := by
    simpa only [map_zero] using e.symm.continuous.tendsto (0 : CoordinateSpace n)
  have hfg : f =ᶠ[𝓝 (0 : CoordinateSpace n)] g := by
    filter_upwards [ht.eventually hev] with z hz
    change f (e (e.symm z)) = g (e (e.symm z)) at hz
    simpa only [e.apply_symm_apply] using hz
  have haf : AnalyticOnNhd ℂ f (ball 0 R) := fun z hz =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn isOpen_ball hf hz
  have hag : AnalyticOnNhd ℂ g (ball 0 R) := fun z hz =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn isOpen_ball hg hz
  exact haf.eqOn_of_preconnected_of_eventuallyEq hag (convex_ball 0 R).isPreconnected
    (mem_ball_self hR) hfg

private theorem word_mem_take (w : Fin k → CoordinateWord n)
    {i j : Fin k} (hij : i < j) : w i ∈ (List.ofFn w).take j.val := by
  apply List.mem_take_iff_getElem.mpr
  refine ⟨i.val, ?_, ?_⟩
  · simp only [List.length_ofFn]
    exact lt_min hij i.isLt
  · simp only [List.getElem_ofFn, Fin.eta]

private theorem word_mem_all (w : Fin k → CoordinateWord n) (i : Fin k) :
    w i ∈ List.ofFn w := List.mem_ofFn.mpr ⟨i, rfl⟩

private theorem formal_piece_coefficient_zero_of_avoids
    (w : Fin k → CoordinateWord n) (Q : Fin k → MvPowerSeries (Fin n) ℂ)
    (α : Fin n →₀ ℕ) (j : Fin k) (hj : ¬ wordExponent (w j) ≤ α) :
    MvPowerSeries.coeff α (MvPowerSeries.monomial (wordExponent (w j)) 1 * Q j) = 0 := by
  rw [MvPowerSeries.coeff_monomial_mul, if_neg hj]

private theorem formal_quotient_mask_reconstruction
    (w : Fin k → CoordinateWord n) (Q : Fin k → MvPowerSeries (Fin n) ℂ)
    (r : MvPowerSeries (Fin n) ℂ)
    (hQ : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val)
      (β + wordExponent (w j)) → MvPowerSeries.coeff β (Q j) = 0)
    (hr : ∀ α, ¬ AvoidsCones (List.ofFn w) α → MvPowerSeries.coeff α r = 0)
    (i : Fin k) (β : Fin n →₀ ℕ) :
    (if AvoidsCones ((List.ofFn w).take i.val) (β + wordExponent (w i)) then
      MvPowerSeries.coeff (β + wordExponent (w i))
        ((∑ j, MvPowerSeries.monomial (wordExponent (w j)) 1 * Q j) + r) else 0) =
      MvPowerSeries.coeff β (Q i) := by
  by_cases hβ : AvoidsCones ((List.ofFn w).take i.val) (β + wordExponent (w i))
  · rw [if_pos hβ, map_add, map_sum]
    have hri : MvPowerSeries.coeff (β + wordExponent (w i)) r = 0 := by
      apply hr
      intro h
      exact h (w i) (word_mem_all w i) (by intro l; simp only [Finsupp.add_apply]; omega)
    rw [hri, add_zero]
    rw [Finset.sum_eq_single i]
    · rw [MvPowerSeries.coeff_monomial_mul,
        if_pos (show wordExponent (w i) ≤ β + wordExponent (w i) by
          intro l; simp only [Finsupp.add_apply]; omega), one_mul,
        add_tsub_cancel_right]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hji | hij
      · exact formal_piece_coefficient_zero_of_avoids w Q _ j
          (hβ (w j) (word_mem_take w hji))
      · rw [MvPowerSeries.coeff_monomial_mul]
        split_ifs with hj
        · rw [one_mul]
          apply hQ j
          intro h
          have he : (β + wordExponent (w i) - wordExponent (w j)) +
              wordExponent (w j) = β + wordExponent (w i) := tsub_add_cancel_of_le hj
          exact h (w i) (word_mem_take w hij) (by
            rw [he]
            intro l
            simp only [Finsupp.add_apply]
            omega)
        · rfl
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · rw [if_neg hβ, hQ i β hβ]

private theorem formal_remainder_mask_reconstruction
    (w : Fin k → CoordinateWord n) (Q : Fin k → MvPowerSeries (Fin n) ℂ)
    (r : MvPowerSeries (Fin n) ℂ)
    (hr : ∀ α, ¬ AvoidsCones (List.ofFn w) α → MvPowerSeries.coeff α r = 0)
    (α : Fin n →₀ ℕ) :
    (if AvoidsCones (List.ofFn w) α then
      MvPowerSeries.coeff α ((∑ j, MvPowerSeries.monomial (wordExponent (w j)) 1 * Q j) + r)
        else 0) = MvPowerSeries.coeff α r := by
  by_cases hα : AvoidsCones (List.ofFn w) α
  · rw [if_pos hα, map_add, map_sum]
    have hz : (∑ j, MvPowerSeries.coeff α
        (MvPowerSeries.monomial (wordExponent (w j)) 1 * Q j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact formal_piece_coefficient_zero_of_avoids w Q α j (hα (w j) (word_mem_all w j))
    rw [hz, zero_add]
  · rw [if_neg hα, hr α hα]

private theorem actualTaylor_monomial_supported_sum {R : ℝ} (hR : 0 < R)
    (w : Fin k → CoordinateWord n) (Q : Fin k → CoordinateSpace n → ℂ)
    (r : CoordinateSpace n → ℂ)
    (hQ : ∀ j, DifferentiableOn ℂ (Q j) (ball 0 R))
    (hr : DifferentiableOn ℂ r (ball 0 R)) :
    actualUnshiftedTaylorAlgHom n (modelGerm hR
      ((DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) =>
        (wordMonomial_differentiable (w j)).differentiableOn.mul (hQ j)).add hr)) =
      (∑ j, MvPowerSeries.monomial (wordExponent (w j)) 1 *
        actualUnshiftedTaylorAlgHom n (modelGerm hR (hQ j))) +
          actualUnshiftedTaylorAlgHom n (modelGerm hR hr) := by
  have hw (j : Fin k) : DifferentiableOn ℂ (wordMonomial (w j)) (ball 0 R) :=
    (wordMonomial_differentiable (w j)).differentiableOn
  have hp (j : Fin k) : DifferentiableOn ℂ
      (fun x => wordMonomial (w j) x * Q j x) (ball 0 R) := (hw j).mul (hQ j)
  have hs : DifferentiableOn ℂ
      (fun x => ∑ j, wordMonomial (w j) x * Q j x) (ball 0 R) :=
    DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) => hp j
  rw [modelGerm_add hR hs hr, modelGerm_sum hR _ hp, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [modelGerm_mul hR (hw j) (hQ j), map_mul, actualTaylor_wordMonomial]

/-- The NATIVE concrete quotient/remainder masks reconstruct an entire
supported monomial decomposition on the SAME ball, for arbitrary finite
words. No monic family or target diagram is involved. -/
theorem actual_arrayPartition_supported_reconstruction {R : ℝ} (hR : 0 < R)
    (w : Fin k → CoordinateWord n) (Q : Fin k → CoordinateSpace n → ℂ)
    (r : CoordinateSpace n → ℂ)
    (hQ : ∀ j, DifferentiableOn ℂ (Q j) (ball 0 R))
    (hr : DifferentiableOn ℂ r (ball 0 R))
    (hQsupport : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val)
      (β + wordExponent (w j)) → MvPowerSeries.coeff β
        (actualUnshiftedTaylorAlgHom n (modelGerm hR (hQ j))) = 0)
    (hrsupport : ∀ α, ¬ AvoidsCones (List.ofFn w) α → MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hR hr)) = 0) :
    ∀ z ∈ ball (0 : CoordinateSpace n) R,
      (∀ j, arrayQuotient (R/2) w j
        (fun x => (∑ i, wordMonomial (w i) x * Q i x) + r x) z = Q j z) ∧
      arrayRemainder (R/2) w
        (fun x => (∑ i, wordMonomial (w i) x * Q i x) + r x) z = r z := by
  let F : CoordinateSpace n → ℂ := fun x => (∑ i, wordMonomial (w i) x * Q i x) + r x
  have hF : DifferentiableOn ℂ F (ball 0 R) :=
    (DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) =>
      (wordMonomial_differentiable (w j)).differentiableOn.mul (hQ j)).add hr
  have hT := actualTaylor_monomial_supported_sum hR w Q r hQ hr
  have hquot (j : Fin k) : EqOn (arrayQuotient (R/2) w j F) (Q j) (ball 0 R) := by
    apply eqOn_of_modelGerm_eq hR
      (arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) w j hF) (hQ j)
    apply actualUnshiftedTaylorAlgHom_injective n
    apply MvPowerSeries.ext
    intro β
    rw [coeff_arrayQuotientGerm (half_pos hR) (half_lt_self hR) w j hF β]
    change (if AvoidsCones ((List.ofFn w).take j.val) (β + wordExponent (w j)) then
      MvPowerSeries.coeff (β + wordExponent (w j))
        (actualUnshiftedTaylorAlgHom n (modelGerm hR hF)) else 0) = _
    rw [hT]
    exact formal_quotient_mask_reconstruction w _ _ hQsupport hrsupport j β
  have hrem : EqOn (arrayRemainder (R/2) w F) r (ball 0 R) := by
    apply eqOn_of_modelGerm_eq hR
      (arrayRemainder_differentiableOn (half_pos hR) (half_lt_self hR) w hF) hr
    apply actualUnshiftedTaylorAlgHom_injective n
    apply MvPowerSeries.ext
    intro α
    rw [coeff_arrayRemainderGerm (half_pos hR) (half_lt_self hR) w hF α]
    change (if AvoidsCones (List.ofFn w) α then MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hR hF)) else 0) = _
    rw [hT]
    exact formal_remainder_mask_reconstruction w _ _ hrsupport α
  intro z hz
  exact ⟨fun j => hquot j hz, hrem hz⟩

private theorem arrayQuotient_congr_on_ball {R : ℝ} (hR : 0 < R)
    (w : Fin k → CoordinateWord n) (j : Fin k) {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (he : EqOn f g (ball 0 R)) :
    EqOn (arrayQuotient (R/2) w j f) (arrayQuotient (R/2) w j g) (ball 0 R) := by
  have hm := modelGerm_eq_of_eqOn hR hf hg he
  apply eqOn_of_modelGerm_eq hR
    (arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) w j hf)
    (arrayQuotient_differentiableOn (half_pos hR) (half_lt_self hR) w j hg)
  apply actualUnshiftedTaylorAlgHom_injective n
  apply MvPowerSeries.ext
  intro β
  rw [coeff_arrayQuotientGerm (half_pos hR) (half_lt_self hR) w j hf β,
    coeff_arrayQuotientGerm (half_pos hR) (half_lt_self hR) w j hg β, hm]

/-- A zero supported division vanishes WHOLE on the SAME ball. The actual
Cauchy bound sends B_R to B_R; R/2 is only the fixed contour parameter.
The finite sum bound is iterated geometrically with no radius loss. -/
theorem actual_bounded_supported_neumann_zero_division {R : ℝ} (hR : 0 < R)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData R w)
    (H Q : Fin k → CoordinateSpace n → ℂ) (r : CoordinateSpace n → ℂ)
    (hH : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHbound : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    (hQ : ∀ j, DifferentiableOn ℂ (Q j) (ball 0 R))
    (hr : DifferentiableOn ℂ r (ball 0 R))
    (hQsupport : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val)
      (β + wordExponent (w j)) → MvPowerSeries.coeff β
        (actualUnshiftedTaylorAlgHom n (modelGerm hR (hQ j))) = 0)
    (hrsupport : ∀ α, ¬ AvoidsCones (List.ofFn w) α → MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hR hr)) = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hQbound : ∀ z ∈ ball (0 : CoordinateSpace n) R, ∑ j, ‖Q j z‖ ≤ M)
    (hzero : ∀ z ∈ ball (0 : CoordinateSpace n) R,
      (∑ j, Q j z * (wordMonomial (w j) z + H j z)) + r z = 0) :
    ∀ z ∈ ball (0 : CoordinateSpace n) R, (∀ j, Q j z = 0) ∧ r z = 0 := by
  let F : CoordinateSpace n → ℂ := fun z => (∑ j, wordMonomial (w j) z * Q j z) + r z
  let E : CoordinateSpace n → ℂ := fun z => -(∑ j, H j z * Q j z)
  have hF : DifferentiableOn ℂ F (ball 0 R) :=
    (DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) =>
      (wordMonomial_differentiable (w j)).differentiableOn.mul (hQ j)).add hr
  have hE : DifferentiableOn ℂ E (ball 0 R) :=
    (DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) => (hH j).mul (hQ j)).neg
  have hFE : EqOn F E (ball 0 R) := by
    intro z hz
    have hh := hzero z hz
    dsimp only [F, E]
    have he : (∑ j, Q j z * (wordMonomial (w j) z + H j z)) =
        (∑ j, wordMonomial (w j) z * Q j z) + (∑ j, H j z * Q j z) := by
      simp only [mul_add, Finset.sum_add_distrib, mul_comm]
    rw [he] at hh
    linear_combination hh
  have hfixed (j : Fin k) (z : CoordinateSpace n) (hz : z ∈ ball 0 R) :
      Q j z = arrayQuotient (R/2) w j E z := by
    have hrec := (actual_arrayPartition_supported_reconstruction hR w Q r hQ hr
      hQsupport hrsupport z hz).1 j
    exact hrec.symm.trans (arrayQuotient_congr_on_ball hR w j hF hE hFE hz)
  have hstep (B : ℝ) (hB0 : 0 ≤ B)
      (hB : ∀ z ∈ ball (0 : CoordinateSpace n) R, ∑ j, ‖Q j z‖ ≤ B) :
      ∀ z ∈ ball (0 : CoordinateSpace n) R, ∑ j, ‖Q j z‖ ≤ B/2 := by
    have hEb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖E z‖ ≤ D.epsilon * B := by
      intro z hz
      change ‖-(∑ j, H j z * Q j z)‖ ≤ _
      rw [norm_neg]
      calc
        _ ≤ ∑ j, ‖H j z * Q j z‖ := norm_sum_le _ _
        _ ≤ ∑ j, D.epsilon * ‖Q j z‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hHbound j z hz) (norm_nonneg _)
        _ = D.epsilon * ∑ j, ‖Q j z‖ := (Finset.mul_sum _ _ _).symm
        _ ≤ D.epsilon * B := mul_le_mul_of_nonneg_left (hB z hz) D.epsilon_pos.le
    intro z hz
    calc
      _ = ∑ j, ‖arrayQuotient (R/2) w j E z‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hfixed j z hz]
      _ ≤ ∑ j, D.quotientConstant j * (D.epsilon * B) :=
        Finset.sum_le_sum fun j _ => D.quotient_bound _ E hE hEb j z hz
      _ = (∑ j, D.quotientConstant j) * (D.epsilon * B) := (Finset.sum_mul _ _ _).symm
      _ = (D.epsilon * ∑ j, D.quotientConstant j) * B := by ring
      _ ≤ (1/2) * B := mul_le_mul_of_nonneg_right D.contraction hB0
      _ = B/2 := by ring
  have hiter (N : ℕ) : ∀ z ∈ ball (0 : CoordinateSpace n) R,
      ∑ j, ‖Q j z‖ ≤ M * (1/2 : ℝ)^N := by
    induction N with
    | zero => simpa only [pow_zero, mul_one] using hQbound
    | succ N ih =>
      intro z hz
      have hh := hstep _ (mul_nonneg hM (pow_nonneg (by norm_num) N)) ih z hz
      exact hh.trans_eq (by rw [pow_succ]; ring)
  intro z hz
  have hlim : Tendsto (fun N : ℕ => M * (1/2 : ℝ)^N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).const_mul M
  have hsum0 : (∑ j, ‖Q j z‖) ≤ 0 := ge_of_tendsto' hlim (fun N => hiter N z hz)
  have hQzero (j : Fin k) : Q j z = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm ((Finset.single_le_sum (fun i _ => norm_nonneg (Q i z))
      (Finset.mem_univ j)).trans hsum0) (norm_nonneg _)
  refine ⟨hQzero, ?_⟩
  simpa only [hQzero, zero_mul, Finset.sum_const_zero, zero_add] using hzero z hz

/-- Two SAME bounded analytic divisions with the native owner partition
coincide WHOLE. The only smallness is the genuine same-ball ConcreteNeumannData
contraction; target heads, target diagrams and HS certificates are absent. -/
theorem actual_bounded_supported_neumann_division_unique {R : ℝ} (hR : 0 < R)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData R w)
    (H Q Q' : Fin k → CoordinateSpace n → ℂ) (r r' F : CoordinateSpace n → ℂ)
    (hH : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHbound : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    (hQ : ∀ j, DifferentiableOn ℂ (Q j) (ball 0 R))
    (hQ' : ∀ j, DifferentiableOn ℂ (Q' j) (ball 0 R))
    (hr : DifferentiableOn ℂ r (ball 0 R)) (hr' : DifferentiableOn ℂ r' (ball 0 R))
    (hQsupport : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val)
      (β + wordExponent (w j)) → MvPowerSeries.coeff β
        (actualUnshiftedTaylorAlgHom n (modelGerm hR (hQ j))) = 0)
    (hQ'support : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val)
      (β + wordExponent (w j)) → MvPowerSeries.coeff β
        (actualUnshiftedTaylorAlgHom n (modelGerm hR (hQ' j))) = 0)
    (hrsupport : ∀ α, ¬ AvoidsCones (List.ofFn w) α → MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hR hr)) = 0)
    (hr'support : ∀ α, ¬ AvoidsCones (List.ofFn w) α → MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hR hr')) = 0)
    (M M' : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hQbound : ∀ z ∈ ball (0 : CoordinateSpace n) R, ∑ j, ‖Q j z‖ ≤ M)
    (hQ'bound : ∀ z ∈ ball (0 : CoordinateSpace n) R, ∑ j, ‖Q' j z‖ ≤ M')
    (hdiv : ∀ z ∈ ball (0 : CoordinateSpace n) R,
      F z = (∑ j, Q j z * (wordMonomial (w j) z + H j z)) + r z)
    (hdiv' : ∀ z ∈ ball (0 : CoordinateSpace n) R,
      F z = (∑ j, Q' j z * (wordMonomial (w j) z + H j z)) + r' z) :
    ∀ z ∈ ball (0 : CoordinateSpace n) R, (∀ j, Q j z = Q' j z) ∧ r z = r' z := by
  let dq (j : Fin k) : CoordinateSpace n → ℂ := fun z => Q j z - Q' j z
  let dr : CoordinateSpace n → ℂ := fun z => r z - r' z
  have hdq (j : Fin k) : DifferentiableOn ℂ (dq j) (ball 0 R) := (hQ j).sub (hQ' j)
  have hdr : DifferentiableOn ℂ dr (ball 0 R) := hr.sub hr'
  have hds : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val)
      (β + wordExponent (w j)) → MvPowerSeries.coeff β
        (actualUnshiftedTaylorAlgHom n (modelGerm hR (hdq j))) = 0 := by
    intro j β hβ
    rw [modelGerm_sub hR (hQ j) (hQ' j), map_sub, map_sub,
      hQsupport j β hβ, hQ'support j β hβ, sub_self]
  have hdrs : ∀ α, ¬ AvoidsCones (List.ofFn w) α → MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hR hdr)) = 0 := by
    intro α hα
    rw [modelGerm_sub hR hr hr', map_sub, map_sub, hrsupport α hα,
      hr'support α hα, sub_self]
  have hdb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ∑ j, ‖dq j z‖ ≤ M + M' := by
    intro z hz
    calc
      _ ≤ ∑ j, (‖Q j z‖ + ‖Q' j z‖) := Finset.sum_le_sum fun j _ => norm_sub_le _ _
      _ = (∑ j, ‖Q j z‖) + (∑ j, ‖Q' j z‖) := Finset.sum_add_distrib
      _ ≤ M + M' := add_le_add (hQbound z hz) (hQ'bound z hz)
  have hdz : ∀ z ∈ ball (0 : CoordinateSpace n) R,
      (∑ j, dq j z * (wordMonomial (w j) z + H j z)) + dr z = 0 := by
    intro z hz
    change (∑ j, (Q j z - Q' j z) * (wordMonomial (w j) z + H j z)) + (r z - r' z) = 0
    calc
      _ = ((∑ j, Q j z * (wordMonomial (w j) z + H j z)) + r z) -
          ((∑ j, Q' j z * (wordMonomial (w j) z + H j z)) + r' z) := by
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        ring
      _ = F z - F z := by rw [← hdiv z hz, ← hdiv' z hz]
      _ = 0 := sub_self _
  have hz := actual_bounded_supported_neumann_zero_division hR w D H dq dr hH hHbound
    hdq hdr hds hdrs (M + M') (add_nonneg hM hM') hdb hdz
  intro z hzB
  exact ⟨fun j => sub_eq_zero.mp ((hz z hzB).1 j), sub_eq_zero.mp (hz z hzB).2⟩

end
end Hironaka.HironakaActualBoundedSupportedNeumannUniqueness
