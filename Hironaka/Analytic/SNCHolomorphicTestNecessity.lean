import Hironaka.Analytic.HolomorphicCoordinateOrders
import Hironaka.Analytic.HolomorphicCoordinatePrime
import Mathlib.Algebra.BigOperators.Associated

set_option autoImplicit false

/-! # Transverse necessity for arbitrary holomorphic SNC tests

Extra test zeros and a residual factor vanishing at the origin are allowed.
Actual coordinate primeness and holomorphic division supply a nearby transverse
unit point; the literal finite lower integral then forces the last-coordinate
strict threshold. These are local supplementary analytic assertions, not a
valuative converse. Reference: Demailly, *Analytic Methods in Algebraic Geometry*,
multiplier ideal integrability; *Complex Analytic and Differential Geometry*.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.SNCHolomorphicTestNecessity

open HolomorphicGermReducednessBridge DivisorialMultiplierOrder

noncomputable section

/-- Actual distinct coordinate germs cannot divide one another. -/
theorem coordinate_germ_not_dvd_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ¬HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j) ∣
      HolGerm.mk (fun z : ComplexModel n => z i) (eventually_differentiableAt_coordinate i) := by
  rintro ⟨q, hq⟩
  obtain ⟨Q, hQ, rfl⟩ := HolGerm.exists_eq_mk q
  have heq : (fun z : ComplexModel n => z i) =ᶠ[𝓝 0] fun z => z j * Q z := by
    exact HolGerm.mk_eq_mk_iff.mp
      (hq.trans (HolGerm.mk_mul (fun z : ComplexModel n => z j) Q
        (eventually_differentiableAt_coordinate j) hQ).symm)
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp heq
  let z : ComplexModel n := EuclideanSpace.single i ((R / 2 : ℝ) : ℂ)
  have hz : z ∈ ball 0 R := by
    rw [mem_ball_zero_iff]
    simp only [z, EuclideanSpace.single, PiLp.norm_single, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < R / 2)]
    linarith
  have hi : z i = ((R / 2 : ℝ) : ℂ) := by simp [z, EuclideanSpace.single]
  have hj : z j = 0 := by simp [z, EuclideanSpace.single, hij.symm]
  have hne : z i ≠ 0 := by
    rw [hi]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : 0 < R / 2))
  exact hne (by simpa only [hj, zero_mul] using hball z hz)

private theorem eventually_differentiableAt_product
    {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty] using eventually_differentiableAt_const (E := ComplexModel n) 1
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem mk_product
    {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (eventually_differentiableAt_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) : (ComplexModel n → ℂ) →+*
      Germ (𝓝 (0 : ComplexModel n)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

/-- An actual residual nondivisible by the last coordinate has genuine nearby
unit points on that hyperplane, avoiding every other coordinate hyperplane. -/
theorem frequently_last_zero_and_residual_and_other_coordinates_ne_zero
    {m : ℕ} {H : ComplexModel (m + 1) → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk H hH) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      z (Fin.last m) = 0 ∧ H z ≠ 0 ∧ ∀ i : Fin m, z i.castSucc ≠ 0 := by
  classical
  let M : ComplexModel (m + 1) → ℂ := fun z => ∏ i : Fin m, z i.castSucc
  have hM : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ M z :=
    eventually_differentiableAt_product Finset.univ (fun (i : Fin m) z => z i.castSucc)
      (fun i => eventually_differentiableAt_coordinate i.castSucc)
  let P : ComplexModel (m + 1) → ℂ := fun z => H z * M z
  have hP : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ P z :=
    eventually_differentiableAt_mul hH hM
  let t : HolGerm (ComplexModel (m + 1)) := HolGerm.mk
    (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m))
  have ht : Prime t := HolomorphicCoordinatePrime.prime_coordinate_germ (Fin.last m)
  have hnotM : ¬t ∣ HolGerm.mk M hM := by
    rw [mk_product Finset.univ (fun (i : Fin m) (z : ComplexModel (m + 1)) => z i.castSucc)
      (fun i => eventually_differentiableAt_coordinate i.castSucc)]
    exact ht.not_dvd_finsetProd fun i _ =>
      coordinate_germ_not_dvd_of_ne (Fin.castSucc_ne_last i)
  have hnotP : ¬t ∣ HolGerm.mk P hP := by
    rw [HolGerm.mk_mul H M hH hM]
    exact fun hdiv => (ht.dvd_or_dvd hdiv).elim hnot hnotM
  by_contra hnone
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      z (Fin.last m) = 0 → P z = 0 := by
    filter_upwards [Filter.not_frequently.mp hnone] with z hz hzlast
    by_cases hzH : H z = 0
    · simp only [P, hzH, zero_mul]
    · have hother : ¬∀ i : Fin m, z i.castSucc ≠ 0 :=
        fun hi => hz ⟨hzlast, hzH, hi⟩
      obtain ⟨i, hi⟩ := not_forall.mp hother
      have hMzero : M z = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (not_ne_iff.mp hi)
      simp only [P, hMzero, mul_zero]
  obtain ⟨Q, hQ, heq⟩ := exists_eq_last_mul_of_eq_zero (by simp) hP hvan
  apply hnotP
  refine ⟨HolGerm.mk Q hQ, ?_⟩
  exact (HolGerm.mk_eq_mk_iff.mpr heq).trans
    (HolGerm.mk_mul (fun z : ComplexModel (m + 1) => z (Fin.last m)) Q
      (eventually_differentiableAt_coordinate (Fin.last m)) hQ)

private theorem coe_sum_real {n : ℕ} (f : Fin n → ℝ) :
    ((∑ j, f j : ℝ) : EReal) = ∑ j, (f j : EReal) :=
  map_sum (⟨⟨fun r : ℝ => (r : EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f Finset.univ

/-- The actual finite integral forces the strict last-coordinate threshold,
without requiring the residual factor to be a unit at the original center. -/
theorem last_threshold_of_multiplier_integrable {m : ℕ}
    (a : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℝ)
    {F H : ComplexModel (m + 1) → ℂ} {ρ : ComplexModel (m + 1) → ℝ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk H hH)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ j : Fin (m + 1), z j ^ a j)
    (hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ContinuousAt ρ z)
    {c : ℝ}
    (hint : MultiplierIntegrableAt (fun z : ComplexModel (m + 1) =>
      (∑ j, ((2 * b j : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (ρ z : EReal))
      c F 0 volume) :
    c * b (Fin.last m) < (a (Fin.last m) : ℝ) + 1 := by
  classical
  let f : ComplexModel (m + 1) → ℂ := fun z =>
    H z * ∏ i : Fin m, z i.castSucc ^ a i.castSucc
  have htest : F =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      (fun z => z (Fin.last m) ^ a (Fin.last m) * f z) := by
    filter_upwards [heq] with z hz
    rw [hz, Fin.prod_univ_castSucc]
    dsimp only [f]
    ring
  obtain ⟨hc, U, hU, h0U, -, hL2⟩ := hint.congr EventuallyEq.rfl htest
  obtain ⟨V, hVsub, hV, h0V⟩ := _root_.mem_nhds_iff.mp (hH.and hρ)
  obtain ⟨y, hy, hyUV⟩ :=
    ((frequently_last_zero_and_residual_and_other_coordinates_ne_zero hH hnot).and_eventually
      ((show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ U from hU.mem_nhds h0U).and
        (show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ V from hV.mem_nhds h0V))).exists
  have hyH : DifferentiableAt ℂ H y := (hVsub hyUV.2).1
  have hyρ : ContinuousAt ρ y := (hVsub hyUV.2).2
  have hcontf : ContinuousAt f y := by
    apply hyH.continuousAt.mul
    exact tendsto_finsetProd Finset.univ fun i _ =>
      (((EuclideanSpace.proj (𝕜 := ℂ) i.castSucc).continuous.continuousAt).pow (a i.castSucc))
  have hfy : f y ≠ 0 :=
    mul_ne_zero hy.2.1 (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hy.2.2 i))
  let Q : ComplexModel (m + 1) → ℝ := fun z =>
    (∑ i : Fin m, 2 * b i.castSucc * Real.log ‖z i.castSucc‖) + ρ z
  have hcontQ : ContinuousAt Q y := by
    apply ContinuousAt.add ?_ hyρ
    apply tendsto_finsetSum Finset.univ
    intro i _
    have hn : ContinuousAt (fun z : ComplexModel (m + 1) => ‖z i.castSucc‖) y :=
      (EuclideanSpace.proj (𝕜 := ℂ) i.castSucc).continuous.continuousAt.norm
    have hl : ContinuousAt
        (fun z : ComplexModel (m + 1) => Real.log ‖z i.castSucc‖) y :=
      (Real.continuousAt_log (norm_ne_zero_iff.mpr (hy.2.2 i))).comp'
        (f := fun z : ComplexModel (m + 1) => ‖z i.castSucc‖) hn
    exact continuousAt_const.mul hl
  have hbound : ∀ᶠ z in 𝓝 y, Q z ≤ Q y + 1 :=
    (hcontQ.tendsto.eventually_lt tendsto_const_nhds (by linarith)).mono fun _ hz => hz.le
  have hcoords : ∀ᶠ z in 𝓝 y, ∀ i : Fin m, z i.castSucc ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i.castSucc).continuous.continuousAt.eventually_ne (hy.2.2 i)
  obtain ⟨W, hWsub, hW, hyW⟩ := _root_.mem_nhds_iff.mp
    ((show ∀ᶠ z in 𝓝 y, z ∈ U from hU.mem_nhds hyUV.1).and (hbound.and hcoords))
  have hWU : W ⊆ U := fun z hz => (hWsub hz).1
  have hupper : ∀ z ∈ W, z (Fin.last m) ≠ 0 →
      ((∑ j : Fin (m + 1), ((2 * b j : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖z j‖)) + (ρ z : EReal)) ≤
      (((2 * b (Fin.last m)) * Real.log ‖z (Fin.last m)‖ + (Q y + 1) : ℝ) : EReal) := by
    intro z hz hzlast
    have hlog (j : Fin (m + 1)) : ENNReal.log (ENNReal.ofReal ‖z j‖) =
        ((Real.log ‖z j‖ : ℝ) : EReal) := by
      apply ENNReal.log_ofReal_of_pos
      apply norm_pos_iff.mpr
      refine Fin.lastCases hzlast (fun i => (hWsub hz).2.2 i) j
    simp_rw [hlog, ← EReal.coe_mul]
    rw [← coe_sum_real, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    rw [Fin.sum_univ_castSucc]
    have hQbound := (hWsub hz).2.1
    dsimp only [Q] at hQbound
    linarith
  have hneg := neg_two_lt_of_lintegral_ne_top hy.1 (hW.mem_nhds hyW) hc hupper
    hcontf hfy (a (Fin.last m)) (hL2.mono hWU).2.ne
  nlinarith

end
end Hironaka.SNCHolomorphicTestNecessity
