import Hironaka.Analytic.PotentialTheory.AnalyticSingularitiesBasic
import Hironaka.Analytic.ERealChordUSC
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pending local logarithmic PSH and generator comparison

Holomorphic generator logarithms are PSH after positive scaling by the
one-variable Jensen argument in the `HolomorphicJensen` namespace below. The bounded
holomorphic coefficient-matrix comparison is proved directly by finite
Cauchy--Schwarz and extended-logarithm monotonicity. The other results compose
these facts.
No coherent ideal sheaf, integral closure, or principalization is assumed.
The default checked core does not import this module.
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators ContDiff ENNReal

namespace Hironaka.HolomorphicJensen

/-- Jensen's formula implies the scalar logarithmic submean inequality when
the analytic function does not vanish at the centre. -/
theorem log_norm_le_circleAverage_of_analyticOnNhd
    {q : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hq : AnalyticOnNhd ℂ q (closedBall c R)) (hqc : q c ≠ 0) :
    Real.log ‖q c‖ ≤ Real.circleAverage (fun z => Real.log ‖q z‖) c R := by
  have hq' : AnalyticOnNhd ℂ q (closedBall c |R|) := by
    simpa [abs_of_pos hR] using hq
  rw [hq'.circleAverage_log_norm hR.ne' hqc]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro z
  by_cases hz : z ∈ closedBall c |R|
  · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hq' hz]
    by_cases hzc : z = c
    · subst z
      rw [(hq' c (by simp)).analyticOrderAt_eq_zero.mpr hqc]
      simp
    · have hord : (0 : ℤ) ≤
          ((analyticOrderAt q z).map (fun m : ℕ => (m : ℤ))).untop₀ := by
        simp
      refine mul_nonneg (by exact_mod_cast hord) ?_
      apply Real.log_nonneg
      have hdist : ‖c - z‖ ≤ R := by
        simpa [mem_closedBall, dist_eq_norm', norm_sub_rev, abs_of_pos hR] using hz
      have hn : ‖c - z‖ ≠ 0 := by
        simpa [sub_eq_zero] using (Ne.symm hzc)
      simpa [field] using hdist
  · simp [hz]

/-- A version of the continuous-majorant deficit calculation which only
requires continuity along the actual boundary parametrization. -/
theorem circleDeficit_coe_le_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℝ} (x v : E) {r C : ℝ} (w : EReal)
    (hg : IntervalIntegrable (fun t : ℝ => g (x + circleMap 0 r t • v))
      MeasureTheory.volume 0 (2 * Real.pi))
    (hC : ∀ t : ℝ, g (x + circleMap 0 r t • v) ≤ C)
    (hw : w ≤ ((Real.circleAverage (fun z : ℂ => g (x + z • v)) 0 r : ℝ) : EReal)) :
    circleDeficit (fun y => (g y : EReal)) x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - w).toENNReal := by
  have hp : 0 ≤ 2 * Real.pi := by positivity
  have havg :
      (2 * Real.pi) * C -
          ∫ t in 0..2 * Real.pi, g (x + circleMap 0 r t • v) =
        (2 * Real.pi) *
          (C - Real.circleAverage (fun z : ℂ => g (x + z • v)) 0 r) := by
    rw [Real.circleAverage]
    simp only [smul_eq_mul]
    field_simp [Real.pi_ne_zero]
  have heq : circleDeficit (fun y => (g y : EReal)) x v r C =
      ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) -
          ((Real.circleAverage (fun z : ℂ => g (x + z • v)) 0 r : ℝ) : EReal)).toENNReal := by
    rw [circleDeficit_coe_eq x v r C hg hC, ← EReal.coe_sub,
      EReal.real_coe_toENNReal, ← ENNReal.ofReal_mul hp]
    congr 1
  rw [heq]
  gcongr
  exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hw)

/-- Decreasing real majorants along a single affine disc imply the exact
extended-real deficit inequality.  No global continuity away from the disc
is assumed. -/
theorem circleSubmean_of_intervalContinuous_antitone_majorants
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {w : E → EReal} (x v : E) {r C : ℝ} (g : ℕ → E → ℝ)
    (hg : ∀ n, Continuous fun t : ℝ => g n (x + circleMap 0 r t • v))
    (hC : ∀ n t, g n (x + circleMap 0 r t • v) ≤ C)
    (hanti : ∀ t : ℝ, Antitone fun n =>
      (g n (x + circleMap 0 r t • v) : EReal))
    (hinf : ∀ t : ℝ, (⨅ n, (g n (x + circleMap 0 r t • v) : EReal)) =
      w (x + circleMap 0 r t • v))
    (hcenter : ∀ n, w x ≤
      ((Real.circleAverage (fun z : ℂ => g n (x + z • v)) 0 r : ℝ) : EReal)) :
    circleDeficit w x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - w x).toENNReal := by
  let u : ℕ → E → EReal := fun n y => (g n y : EReal)
  have hm : ∀ n, Measurable fun t : ℝ =>
      ((C : EReal) - u n (x + circleMap 0 r t • v)).toENNReal := by
    intro n
    exact (continuous_finiteDeficit C).measurable.comp
      (continuous_coe_real_ereal.comp (hg n)).measurable
  have hdef : circleDeficit w x v r C =
      ⨆ n, circleDeficit (u n) x v r C := by
    rw [← circleDeficit_iInf_of_antitone_of_measurable x v C hm hanti]
    unfold circleDeficit
    apply MeasureTheory.lintegral_congr
    intro t
    simp only [u]
    rw [hinf t]
  rw [hdef]
  apply iSup_le
  intro n
  exact circleDeficit_coe_le_of_intervalIntegrable x v (w x)
    ((hg n).intervalIntegrable _ _) (hC n) (hcenter n)

/-- The squared norm logarithm of a finite holomorphic family at a nonzero
centre is below every positively regularized boundary average. -/
theorem log_generatorNormSq_le_circleAverage_regularized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} {f : Fin n → E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    {x v : E} {r ε : ℝ} (hr : 0 < r)
    (hD : affineClosedDisc x v r ⊆ U) (hε : 0 < ε)
    (hx : generatorVector f x ≠ 0) :
    Real.log (generatorNormSq f x) ≤
      Real.circleAverage
        (fun z : ℂ => regularizedLogNormSq ε (generatorVector f (x + z • v))) 0 r := by
  let line : ℂ → E := fun z => x + z • v
  let D : Set ℂ := line ⁻¹' U
  let a : EuclideanSpace ℂ (Fin n) := generatorVector f x
  let q : ℂ → ℂ := fun z => inner ℂ a (generatorVector f (line z)) / ‖a‖
  have hline : Differentiable ℂ line := by
    dsimp [line]
    fun_prop
  have hDopen : IsOpen D := hU.preimage hline.continuous
  have hclosedD : closedBall (0 : ℂ) r ⊆ D := by
    intro z hz
    exact hD ⟨z, hz, rfl⟩
  have hvec : DifferentiableOn ℂ (fun z => generatorVector f (line z)) D := by
    rw [differentiableOn_piLp]
    intro j
    have hmap : MapsTo line D U := fun _ hz => hz
    simpa only [generatorVector, PiLp.toLp_apply] using
      (hf j).fun_comp hline.differentiableOn hmap
  have hqdiff : DifferentiableOn ℂ q D := by
    have hclm : DifferentiableOn ℂ
        (fun _ : ℂ => innerSL ℂ a) D := differentiableOn_const _
    exact (hclm.clm_apply hvec).div_const ‖a‖
  have hq : AnalyticOnNhd ℂ q (closedBall 0 r) :=
    (hqdiff.analyticOnNhd hDopen).mono hclosedD
  have hqAbs : AnalyticOnNhd ℂ q (closedBall 0 |r|) := by
    simpa [abs_of_pos hr] using hq
  have ha : a ≠ 0 := by
    simpa only [a] using hx
  have hnorma : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hq0 : q 0 = (‖a‖ : ℂ) := by
    dsimp [q, line]
    simp only [zero_smul, add_zero]
    change inner ℂ a a / (‖a‖ : ℂ) = (‖a‖ : ℂ)
    rw [inner_self_eq_norm_sq_to_K]
    field_simp [hnorma]
    rfl
  have hq0ne : q 0 ≠ 0 := by
    rw [hq0, Complex.ofReal_ne_zero]
    exact hnorma
  have hjensen := log_norm_le_circleAverage_of_analyticOnNhd hr hq hq0ne
  let lhs : ℂ → ℝ := fun z => 2 * Real.log ‖q z‖
  let rhs : ℂ → ℝ := fun z =>
    regularizedLogNormSq ε (generatorVector f (line z))
  let patched : ℂ → ℝ := fun z => if q z = 0 then rhs z else lhs z
  have hcodClosed : q ⁻¹' ({0} : Set ℂ)ᶜ ∈
      codiscreteWithin (closedBall (0 : ℂ) r) :=
    hq.preimage_zero_mem_codiscreteWithin hq0ne
      (by simp [hr.le]) (isConnected_closedBall hr.le)
  have hcod : q ⁻¹' ({0} : Set ℂ)ᶜ ∈
      codiscreteWithin (sphere (0 : ℂ) |r|) := by
    apply codiscreteWithin_mono sphere_subset_closedBall
    simpa [abs_of_pos hr] using hcodClosed
  have heq : lhs =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] patched := by
    filter_upwards [hcod] with z hz
    have hz' : q z ≠ 0 := by simpa using hz
    simp [patched, hz']
  have hlogInt : CircleIntegrable (fun z => Real.log ‖q z‖) 0 r :=
    (hqAbs.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hlhsInt : CircleIntegrable lhs 0 r := by
    exact hlogInt.const_mul 2
  have hpatchedInt : CircleIntegrable patched 0 r :=
    CircleIntegrable.congr_codiscreteWithin heq hlhsInt
  have hrhsParam : Continuous (fun t : ℝ => rhs (circleMap 0 r t)) := by
    have hpath : Continuous (fun t : ℝ => line (circleMap 0 r t)) := by
      fun_prop
    have hvecDiff : DifferentiableOn ℂ (generatorVector f) U := by
      rw [differentiableOn_piLp]
      exact hf
    have hvecCont : ContinuousOn (generatorVector f) U := hvecDiff.continuousOn
    have hreg : Continuous
        (regularizedLogNormSq (E := EuclideanSpace ℂ (Fin n)) ε) :=
      (contDiff_regularizedLogNormSq (n := 0) hε).continuous
    exact hreg.comp (hvecCont.comp_continuous hpath fun t =>
      hD (circle_mem_affineClosedDisc x v hr.le t))
  have hrhsInt : CircleIntegrable rhs 0 r :=
    hrhsParam.intervalIntegrable _ _
  have hpatched_le : ∀ z ∈ sphere (0 : ℂ) |r|, patched z ≤ rhs z := by
    intro z hz
    by_cases hqz : q z = 0
    · simp [patched, hqz]
    · simp only [patched, if_neg hqz, lhs, rhs, regularizedLogNormSq]
      have hqnorm : ‖q z‖ ≤ ‖generatorVector f (line z)‖ := by
        dsimp [q]
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a)]
        calc
          ‖inner ℂ a (generatorVector f (line z))‖ / ‖a‖ ≤
              (‖a‖ * ‖generatorVector f (line z)‖) / ‖a‖ := by
            gcongr
            exact norm_inner_le_norm _ _
          _ = ‖generatorVector f (line z)‖ := by field_simp [hnorma]
      rw [show 2 * Real.log ‖q z‖ = Real.log (‖q z‖ ^ (2 : ℕ)) by
        rw [Real.log_pow]
        norm_num]
      apply Real.log_le_log (sq_pos_of_pos (norm_pos_iff.mpr hqz))
      calc
        ‖q z‖ ^ 2 ≤ ‖generatorVector f (line z)‖ ^ 2 := by gcongr
        _ ≤ ‖generatorVector f (line z)‖ ^ 2 + ε := le_add_of_nonneg_right hε.le
  have havg_le : Real.circleAverage lhs 0 r ≤ Real.circleAverage rhs 0 r := by
    rw [Real.circleAverage_congr_codiscreteWithin heq hr.ne']
    exact Real.circleAverage_mono hpatchedInt hrhsInt hpatched_le
  calc
    Real.log (generatorNormSq f x) = 2 * Real.log ‖q 0‖ := by
      rw [hq0, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a),
        ← generatorVector_norm_sq]
      change Real.log (‖a‖ ^ 2) = 2 * Real.log ‖a‖
      rw [Real.log_pow]
      norm_num
    _ ≤ 2 * Real.circleAverage (fun z => Real.log ‖q z‖) 0 r := by
      gcongr
    _ = Real.circleAverage lhs 0 r := by
      simpa only [lhs, smul_eq_mul] using
        (Real.circleAverage_fun_smul
          (f := fun z : ℂ => Real.log ‖q z‖) (c := 0) (R := r)
          (a := (2 : ℝ))).symm
    _ ≤ Real.circleAverage rhs 0 r := havg_le
    _ = _ := rfl

end Hironaka.HolomorphicJensen

namespace Hironaka

/-- Restriction to a complex affine disc, scalar Jensen, and decreasing
positive regularization give the logarithmic submean inequality, including
common zeros and the identically-zero family. No measure on the ambient space
is needed for the disc-based PSH definition. -/
theorem plurisubharmonicAt_scaled_generatorLog
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {n : ℕ} {f : Fin n → E → ℂ} {x : E}
    (hf : HolomorphicGeneratorsAt f x) {c : ℝ} (hc : 0 < c) :
    PlurisubharmonicAt (fun y => (c : EReal) * generatorLog f y) x := by
  obtain ⟨U, hU, hxU, hf⟩ := hf
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let g : ℕ → E → ℝ := fun i y =>
    c * regularizedLogNormSq (ε i) (generatorVector f y)
  have hε (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεanti : Antitone ε := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hvec : DifferentiableOn ℂ (generatorVector f) U := by
    rw [differentiableOn_piLp]
    exact hf
  have hvecCont : ContinuousOn (generatorVector f) U := hvec.continuousOn
  have hgCont (i : ℕ) : ContinuousOn (g i) U := by
    have hreg : Continuous
        (regularizedLogNormSq (E := EuclideanSpace ℂ (Fin n)) (ε i)) :=
      (contDiff_regularizedLogNormSq (n := 0) (hε i)).continuous
    exact (continuous_const.mul hreg).comp_continuousOn' hvecCont
  have hganti (y : E) : Antitone fun n => (g n y : EReal) := by
    intro m n hmn
    change (c : EReal) *
        (regularizedLogNormSq (ε n) (generatorVector f y) : EReal) ≤
      (c : EReal) *
        (regularizedLogNormSq (ε m) (generatorVector f y) : EReal)
    exact Hironaka.monotone_eReal_const_mul hc.le
      (antitone_regularizedLogNormSq hε hεanti (generatorVector f y) hmn)
  have hginf (y : E) :
      (⨅ n, (g n y : EReal)) = (c : EReal) * generatorLog f y := by
    have htend : Tendsto (fun n => (g n y : EReal)) atTop
        (𝓝 ((c : EReal) * generatorLog f y)) := by
      have hmul := (Hironaka.continuous_eReal_const_mul hc.ne').continuousAt.tendsto.comp
        (tendsto_regularizedLogNormSq hε hεlim (generatorVector f y))
      have hmul' : Tendsto (fun n => (c : EReal) *
          (regularizedLogNormSq (ε n) (generatorVector f y) : EReal)) atTop
          (𝓝 ((c : EReal) * logNormSq (generatorVector f y))) := by
        exact hmul
      simpa only [g, EReal.coe_mul, generatorLog] using hmul'
    exact tendsto_nhds_unique (tendsto_atTop_iInf (hganti y)) htend
  have hlogCont : ContinuousOn (generatorLog f) U := by
    change ContinuousOn (fun y => logNormSq (generatorVector f y)) U
    exact continuous_logNormSq.comp_continuousOn' hvecCont
  refine ⟨U, hU, hxU, ⟨?_, ?_, ?_⟩⟩
  · intro y _
    exact Hironaka.eReal_const_mul_ne_top hc.le (generatorLog_ne_top f y)
  · exact Hironaka.upperSemicontinuousOn_eReal_const_mul
      hlogCont.upperSemicontinuousOn hc.le
  · intro y v r hr hD C hC
    have hdiscNonempty : (affineClosedDisc y v r).Nonempty :=
      ⟨y, center_mem_affineClosedDisc y v hr.le⟩
    obtain ⟨p, hp, hpmax⟩ :=
      (isCompact_affineClosedDisc y v r).exists_isMaxOn hdiscNonempty
        ((hgCont 0).mono hD)
    let B : ℝ := g 0 p
    let a : ℝ := Max.max 0 (B - C)
    have ha : 0 ≤ a := le_max_left _ _
    have hBC : B ≤ C + a := by
      have : B - C ≤ a := le_max_right _ _
      linarith
    have hbound : ∀ i t, g i (y + circleMap 0 r t • v) ≤ C + a := by
      intro i t
      have hz : y + circleMap 0 r t • v ∈ affineClosedDisc y v r :=
        circle_mem_affineClosedDisc y v hr.le t
      calc
        g i (y + circleMap 0 r t • v) ≤ g 0 (y + circleMap 0 r t • v) :=
          EReal.coe_le_coe_iff.mp (hganti _ (Nat.zero_le i))
        _ ≤ B := hpmax hz
        _ ≤ C + a := hBC
    have hparam (i : ℕ) : Continuous fun t : ℝ =>
        g i (y + circleMap 0 r t • v) := by
      have hpath : Continuous fun t : ℝ => y + circleMap 0 r t • v := by
        fun_prop
      exact (hgCont i).comp_continuous hpath fun t =>
        hD (circle_mem_affineClosedDisc y v hr.le t)
    have hcenter (i : ℕ) :
        (c : EReal) * generatorLog f y ≤
          ((Real.circleAverage (fun z : ℂ => g i (y + z • v)) 0 r : ℝ) : EReal) := by
      by_cases hy : generatorVector f y = 0
      · have hybot : generatorLog f y = ⊥ := by
          rw [generatorLog_eq_bot_iff]
          exact (generatorVector_eq_zero_iff f y).mp hy
        rw [hybot, EReal.coe_mul_bot_of_pos hc]
        exact bot_le
      · have hnonzero : ∃ j, f j y ≠ 0 := by
          contrapose! hy
          exact (generatorVector_eq_zero_iff f y).mpr hy
        have hbase :=
          HolomorphicJensen.log_generatorNormSq_le_circleAverage_regularized
            hU hf hr hD (hε i) hy
        have hreal : c * Real.log (generatorNormSq f y) ≤
            Real.circleAverage (fun z : ℂ => g i (y + z • v)) 0 r := by
          calc
            c * Real.log (generatorNormSq f y) ≤
                c * Real.circleAverage
                  (fun z : ℂ => regularizedLogNormSq (ε i)
                    (generatorVector f (y + z • v))) 0 r :=
              mul_le_mul_of_nonneg_left hbase hc.le
            _ = Real.circleAverage (fun z : ℂ => g i (y + z • v)) 0 r := by
              simpa only [g, smul_eq_mul] using
                (Real.circleAverage_fun_smul
                  (f := fun z : ℂ => regularizedLogNormSq (ε i)
                    (generatorVector f (y + z • v)))
                  (c := 0) (R := r) (a := c)).symm
        rw [generatorLog_of_nonzero hnonzero]
        simpa only [← EReal.coe_mul] using EReal.coe_le_coe_iff.mpr hreal
    apply (discSubmean_add_bound_iff y v hr.le C a ha hC).mp
    exact HolomorphicJensen.circleSubmean_of_intervalContinuous_antitone_majorants
      y v g hparam hbound
      (fun t => hganti (y + circleMap 0 r t • v))
      (fun t => hginf (y + circleMap 0 r t • v)) hcenter

/-- A smooth logarithmic presentation gives the actual quasi-PSH decomposition.
Nondegeneracy is still separate, since the generators could all vanish on a
neighborhood. The real scalar structure is explicitly the restricted complex one. -/
theorem SmoothLogarithmicTypeAt.quasiPlurisubharmonicAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {u : E → EReal} {c : ℝ} {n : ℕ} {f : Fin n → E → ℂ} {x : E}
    (hu : Hironaka.SmoothLogarithmicTypeAt u c f x) :
    QuasiPlurisubharmonicAt u x := by
  obtain ⟨hc, hf, b, hb, heq⟩ := hu
  exact ⟨fun y => (c : EReal) * generatorLog f y, b,
    plurisubharmonicAt_scaled_generatorLog hf hc, hb, heq⟩

/-- If `g = A f` and the squared Hilbert--Schmidt norm of the actual
holomorphic coefficient matrix is at most `M > 0`, then `ψ_g ≤ ψ_f + log M`.
All neighborhood and coefficient hypotheses are explicit. The proof is finite
Cauchy--Schwarz followed by monotonicity of the extended logarithm. -/
theorem generatorLog_le_of_holomorphic_matrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n m : ℕ} {U : Set E} (_hU : IsOpen U)
    (f : Fin n → E → ℂ) (g : Fin m → E → ℂ)
    (A : Fin m → Fin n → E → ℂ)
    (_hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (_hg : ∀ i, DifferentiableOn ℂ (g i) U)
    (_hA : ∀ i j, DifferentiableOn ℂ (A i j) U)
    (hgf : ∀ y ∈ U, ∀ i, g i y = ∑ j, A i j y * f j y)
    {M : ℝ} (hM : 0 < M)
    (hbound : ∀ y ∈ U, (∑ i, ∑ j, ‖A i j y‖ ^ 2) ≤ M) :
    ∀ y ∈ U, generatorLog g y ≤ generatorLog f y + (Real.log M : EReal) := by
  intro y hy
  have hrow (i : Fin m) :
      ‖g i y‖ ^ 2 ≤
        (∑ j, ‖A i j y‖ ^ 2) * ∑ j, ‖f j y‖ ^ 2 := by
    rw [hgf y hy i]
    calc
      ‖∑ j, A i j y * f j y‖ ^ 2 ≤
          (∑ j, ‖A i j y * f j y‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
      _ = (∑ j, ‖A i j y‖ * ‖f j y‖) ^ 2 := by
        simp_rw [norm_mul]
      _ ≤ (∑ j, ‖A i j y‖ ^ 2) * ∑ j, ‖f j y‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hnorm : generatorNormSq g y ≤ M * generatorNormSq f y := by
    rw [generatorNormSq, generatorNormSq]
    calc
      (∑ i, ‖g i y‖ ^ 2) ≤
          ∑ i, (∑ j, ‖A i j y‖ ^ 2) * ∑ j, ‖f j y‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = (∑ i, ∑ j, ‖A i j y‖ ^ 2) * ∑ j, ‖f j y‖ ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ M * ∑ j, ‖f j y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hbound y hy)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  calc
    ENNReal.log (ENNReal.ofReal (∑ i, ‖g i y‖ ^ 2)) ≤
        ENNReal.log (ENNReal.ofReal (M * ∑ j, ‖f j y‖ ^ 2)) :=
      ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hnorm)
    _ = ENNReal.log (ENNReal.ofReal M *
        ENNReal.ofReal (∑ j, ‖f j y‖ ^ 2)) := by
      rw [ENNReal.ofReal_mul hM.le]
    _ = ENNReal.log (ENNReal.ofReal (∑ j, ‖f j y‖ ^ 2)) +
        (Real.log M : EReal) := by
      rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hM, add_comm]

/-- The same explicit matrix data give the manuscript's direction of local
singularity comparison: combinations of `f` are more singular than `f`. -/
theorem moreSingularAt_of_holomorphic_matrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n m : ℕ} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (f : Fin n → E → ℂ) (g : Fin m → E → ℂ)
    (A : Fin m → Fin n → E → ℂ)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    (hA : ∀ i j, DifferentiableOn ℂ (A i j) U)
    (hgf : ∀ y ∈ U, ∀ i, g i y = ∑ j, A i j y * f j y)
    {M : ℝ} (hM : 0 < M)
    (hbound : ∀ y ∈ U, (∑ i, ∑ j, ‖A i j y‖ ^ 2) ≤ M) :
    MoreSingularAt (generatorLog g) (generatorLog f) x := by
  have hcomp : MoreSingularOn (generatorLog g) (generatorLog f) U :=
    ⟨Real.log M, generatorLog_le_of_holomorphic_matrix hU f g A hf hg hA hgf hM hbound⟩
  exact hcomp.moreSingularAt (hU.mem_nhds hx)

/-- Two actual matrices, one in each direction, suffice for equality of the
local singularity types. Their bounds are local hypotheses, not an assertion
that a coherent ideal or its transition data has already been constructed. -/
theorem sameSingularityTypeAt_of_holomorphic_matrices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n m : ℕ} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (f : Fin n → E → ℂ) (g : Fin m → E → ℂ)
    (A : Fin m → Fin n → E → ℂ) (B : Fin n → Fin m → E → ℂ)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    (hA : ∀ i j, DifferentiableOn ℂ (A i j) U)
    (hB : ∀ j i, DifferentiableOn ℂ (B j i) U)
    (hgf : ∀ y ∈ U, ∀ i, g i y = ∑ j, A i j y * f j y)
    (hfg : ∀ y ∈ U, ∀ j, f j y = ∑ i, B j i y * g i y)
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hboundA : ∀ y ∈ U, (∑ i, ∑ j, ‖A i j y‖ ^ 2) ≤ M)
    (hboundB : ∀ y ∈ U, (∑ j, ∑ i, ‖B j i y‖ ^ 2) ≤ N) :
    SameSingularityTypeAt (generatorLog f) (generatorLog g) x := by
  exact ⟨moreSingularAt_of_holomorphic_matrix hU hx g f B hg hf hB hfg hN hboundB,
    moreSingularAt_of_holomorphic_matrix hU hx f g A hf hg hA hgf hM hboundA⟩

end Hironaka
