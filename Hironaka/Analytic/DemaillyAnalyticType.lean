import Hironaka.Analytic.DemaillyApproximation

set_option autoImplicit false

/-!
# Analytic singularity types of local Bergman approximants

Source: Demailly, *Analytic methods in algebraic geometry*, Theorem 13.2;
Hironaka, Theorem 1.6.2 (`xia-sgpt:page-0049`).

`DemaillyApproximation.exists_weightedL2_generators` constructs, near each
point of a plurisubharmonic weight `P`, finitely many holomorphic weighted
Bergman generators `gᵢ`.  This module records the interface fact needed by the
global regularization argument: the normalized logarithmic weight
`m⁻¹ log ∑ᵢ |gᵢ|²` has the manuscript's *rational, bounded-remainder* analytic
singularity type.  Its remainder is zero and its coefficient is the rational
number `1 / m`.

This is only the local analytic-type part of Demailly regularization.  Gluing
these local weights into a decreasing global theta-PSH sequence, with the
multiplier-ideal inclusions, remains the outstanding step in
`QuasiEquisingularApproximation`.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Hironaka.DemaillyAnalyticType



variable {n : ℕ}

/-- A finite holomorphic Bergman generator family gives the expected rational
logarithmic singularity type for its normalized logarithm. -/
theorem hasAnalyticSingularityTypeAt_inv_nat_generatorLog
    {O : Set (ComplexModel n)} {m N : ℕ} {g : Fin N → ComplexModel n → ℂ}
    (hm : 0 < m) (hO : IsOpen O) (hg : ∀ l, AnalyticOnNhd ℂ (g l) O)
    {y : ComplexModel n} (hy : y ∈ O) :
    HasAnalyticSingularityTypeAt
      (fun x => (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g x) y := by
  refine ⟨(m : ℚ)⁻¹, N, g, ?_⟩
  refine ⟨?_, ⟨O, hO, hy, fun l => (hg l).differentiableOn⟩,
    0, boundedRealGermAt_of_continuousAt continuousAt_const, ?_⟩
  · exact_mod_cast inv_pos.mpr (Nat.cast_pos.mpr hm)
  · filter_upwards [] with x
    simp only [Pi.zero_apply, EReal.coe_zero, add_zero]
    have hcoef : (((((m : ℚ)⁻¹ : ℚ) : ℝ) : EReal)) =
        ((((m : ℝ)⁻¹ : ℝ) : EReal)) := by
      congr 1
      norm_num
    rw [hcoef]

/-- The local Bergman logarithm already satisfies the stronger CT22 analytic
singularity convention: its coefficient is a positive real and its remainder
is identically zero, hence smooth. -/
theorem hasSmoothAnalyticSingularitiesAt_inv_nat_generatorLog
    {O : Set (ComplexModel n)} {m N : ℕ} {g : Fin N → ComplexModel n → ℂ}
    (hm : 0 < m) (hO : IsOpen O) (hg : ∀ l, AnalyticOnNhd ℂ (g l) O)
    {y : ComplexModel n} (hy : y ∈ O) :
    HasSmoothAnalyticSingularitiesAt
      (fun x => (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g x) y := by
  refine ⟨(m : ℝ)⁻¹, N, g, ?_⟩
  refine ⟨inv_pos.mpr (Nat.cast_pos.mpr hm),
    ⟨O, hO, hy, fun l => (hg l).differentiableOn⟩,
    0, ?_, ?_⟩
  · filter_upwards [] with x
    exact contDiffAt_const
  · filter_upwards [] with x
    simp

/-- **Local analytic-type half of Demailly regularization.**  The finite
weighted Bergman generators supplied by the `L²` extension construction define
an analytic-singularity-type normalized logarithmic weight on their common
neighborhood. -/
theorem exists_weightedL2_generators_with_analyticSingularityType :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ (W : Set (ComplexModel n)) (P : ComplexModel n → EReal), IsOpen W →
        PlurisubharmonicOn P W → ∀ z ∈ W, ∀ m : ℕ, 0 < m →
          ∃ O : Set (ComplexModel n), IsOpen O ∧ z ∈ O ∧ O ⊆ W ∧
            ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ) (C : ℝ≥0∞), C ≠ ⊤ ∧
              (∀ l, AnalyticOnNhd ℂ (g l) O) ∧
              (∀ l, WeightedL2On P m (g l) O volume) ∧
              (∀ y ∈ O, EReal.exp ((m : EReal) * P y) ≤
                C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2)) ∧
              ∀ y ∈ O, HasAnalyticSingularityTypeAt
                (fun x => (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g x) y := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro W P hW hP z hz m hm
  obtain ⟨O, hO, hzO, hOW, N, g, C, hC, hg, hL2, hdom⟩ :=
    DemaillyApproximation.exists_weightedL2_generators W P hW hP z hz m hm
  exact ⟨O, hO, hzO, hOW, N, g, C, hC, hg, hL2, hdom,
    fun y hy => hasAnalyticSingularityTypeAt_inv_nat_generatorLog hm hO hg hy⟩

/-- The weighted Bergman generators from the local `L²` construction also
produce the strong smooth-remainder analytic singularities required in the
restricted-volume definition.  This is a local statement only: producing a
decreasing global current sequence remains the separate gluing problem. -/
theorem exists_weightedL2_generators_with_smoothAnalyticSingularities :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ (W : Set (ComplexModel n)) (P : ComplexModel n → EReal), IsOpen W →
        PlurisubharmonicOn P W → ∀ z ∈ W, ∀ m : ℕ, 0 < m →
          ∃ O : Set (ComplexModel n), IsOpen O ∧ z ∈ O ∧ O ⊆ W ∧
            ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ) (C : ℝ≥0∞), C ≠ ⊤ ∧
              (∀ l, AnalyticOnNhd ℂ (g l) O) ∧
              (∀ l, WeightedL2On P m (g l) O volume) ∧
              (∀ y ∈ O, EReal.exp ((m : EReal) * P y) ≤
                C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2)) ∧
              ∀ y ∈ O, HasSmoothAnalyticSingularitiesAt
                (fun x => (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g x) y := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro W P hW hP z hz m hm
  obtain ⟨O, hO, hzO, hOW, N, g, C, hC, hg, hL2, hdom⟩ :=
    DemaillyApproximation.exists_weightedL2_generators W P hW hP z hz m hm
  exact ⟨O, hO, hzO, hOW, N, g, C, hC, hg, hL2, hdom,
    fun y hy => hasSmoothAnalyticSingularitiesAt_inv_nat_generatorLog hm hO hg hy⟩


/-- A weighted Bergman generator is an actual member of the local multiplier
ideal of the original weight.  This is the direct compatibility between the
`L²` side of the local construction and the multiplier-ideal side of a
quasi-equisingular approximation. -/
theorem weightedL2On_multiplierIntegrableAt :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ {P : ComplexModel n → EReal} {O : Set (ComplexModel n)} {m N : ℕ}
        {g : Fin N → ComplexModel n → ℂ}, 0 < m → IsOpen O →
        (∀ l, AnalyticOnNhd ℂ (g l) O) → (∀ l, WeightedL2On P m (g l) O volume) →
        ∀ l {y : ComplexModel n}, y ∈ O →
          MultiplierIntegrableAt P (m : ℝ) (g l) y volume := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro P O m N g hm hO hg hL2 l y hy
  exact ⟨by exact_mod_cast hm, O, hO, hy, (hg l).differentiableOn, hL2 l⟩



/-- Analytic singularity type is invariant under an explicitly bounded real
remainder.  This is the local type-compatibility used when a Bergman logarithm
is transported through chart normalizations or a bounded gluing correction. -/
theorem HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E} (hu : HasAnalyticSingularityTypeAt u x)
    {b : E → ℝ} (hb : BoundedRealGermAt b x)
    (hvu : v =ᶠ[𝓝 x] fun y => u y + (b y : EReal)) :
    HasAnalyticSingularityTypeAt v x := by
  obtain ⟨c, N, f, hc, hf, r, hr, hur⟩ := hu
  refine ⟨c, N, f, hc, hf, fun y => r y + b y, ?_, ?_⟩
  · obtain ⟨Cr, hCr0, hCr⟩ := hr
    obtain ⟨Cb, hCb0, hCb⟩ := hb
    refine ⟨Cr + Cb, add_nonneg hCr0 hCb0, ?_⟩
    filter_upwards [hCr, hCb] with y hyr hyb
    exact (abs_add_le _ _).trans (add_le_add hyr hyb)
  · filter_upwards [hvu, hur] with y hyu hur
    rw [hyu, hur, EReal.coe_add]
    ac_rfl



/-- The maximum of two logarithmic presentations with the same coefficient and
same generators is again a logarithmic presentation. -/
theorem LogarithmicTypeAt.max_of_same_generators
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E} {c : ℝ} {N : ℕ} {f : Fin N → E → ℂ}
    (hu : LogarithmicTypeAt u c f x) (hv : LogarithmicTypeAt v c f x) :
    LogarithmicTypeAt (fun y => max (u y) (v y)) c f x := by
  obtain ⟨hc, hf, b, hb, hub⟩ := hu
  obtain ⟨-, -, d, hd, hvd⟩ := hv
  refine ⟨hc, hf, fun y => max (b y) (d y), ?_, ?_⟩
  · obtain ⟨Cb, hCb0, hCb⟩ := hb
    obtain ⟨Cd, hCd0, hCd⟩ := hd
    refine ⟨Cb + Cd, add_nonneg hCb0 hCd0, ?_⟩
    filter_upwards [hCb, hCd] with y hyb hyd
    rw [abs_le]
    constructor
    · calc -(Cb + Cd) ≤ -Cb := by linarith
        _ ≤ b y := (abs_le.mp hyb).1
        _ ≤ max (b y) (d y) := le_max_left _ _
    · exact max_le ((abs_le.mp hyb).2.trans (by linarith))
        ((abs_le.mp hyd).2.trans (by linarith))
  · filter_upwards [hub, hvd] with y huy hvy
    rw [huy, hvy]
    exact max_add_add_left _ _ _

/-- The corresponding rational analytic singularity type is preserved by a
maximum whenever both local presentations use the same generator family. -/
theorem HasAnalyticSingularityTypeAt.max_of_same_generators
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E} {c : ℚ} {N : ℕ} {f : Fin N → E → ℂ}
    (hu : LogarithmicTypeAt u (c : ℝ) f x) (hv : LogarithmicTypeAt v (c : ℝ) f x) :
    HasAnalyticSingularityTypeAt (fun y => max (u y) (v y)) x :=
  ⟨c, N, f, LogarithmicTypeAt.max_of_same_generators hu hv⟩


lemma generatorNormSq_append
    {E : Type*} {m n : ℕ} (f : Fin m → E → ℂ) (g : Fin n → E → ℂ) (y : E) :
    generatorNormSq (Fin.append f g) y = generatorNormSq f y + generatorNormSq g y := by
  rw [generatorNormSq, generatorNormSq, generatorNormSq, Fin.sum_univ_add]
  simp

lemma generatorLog_append_eq_log_add
    {E : Type*} {m n : ℕ} (f : Fin m → E → ℂ) (g : Fin n → E → ℂ) (y : E) :
    generatorLog (Fin.append f g) y =
      ENNReal.log (ENNReal.ofReal (generatorNormSq f y + generatorNormSq g y)) := by
  rw [generatorLog_eq_log_sum]
  change ENNReal.log (ENNReal.ofReal (generatorNormSq (Fin.append f g) y)) = _
  rw [generatorNormSq_append]

lemma generatorLog_le_append
    {E : Type*} {m n : ℕ} (f : Fin m → E → ℂ) (g : Fin n → E → ℂ) (y : E) :
    generatorLog f y ≤ generatorLog (Fin.append f g) y := by
  rw [generatorLog_eq_log_sum, generatorLog_append_eq_log_add]
  apply ENNReal.log_monotone
  apply ENNReal.ofReal_le_ofReal
  exact le_add_of_nonneg_right (generatorNormSq_nonneg g y)

lemma generatorLog_append_le_max_add_log_two
    {E : Type*} {m n : ℕ} (f : Fin m → E → ℂ) (g : Fin n → E → ℂ) (y : E) :
    generatorLog (Fin.append f g) y ≤
      max (generatorLog f y) (generatorLog g y) + (Real.log 2 : EReal) := by
  let F := generatorNormSq f y
  let G := generatorNormSq g y
  have hF : 0 ≤ F := generatorNormSq_nonneg f y
  have hG : 0 ≤ G := generatorNormSq_nonneg g y
  by_cases hF0 : F = 0
  · have hlogF : generatorLog f y = ⊥ := by
      rw [generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal F) = ⊥
      simp [hF0]
    have happ : generatorLog (Fin.append f g) y = generatorLog g y := by
      rw [generatorLog_append_eq_log_add, generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal (F + G)) = ENNReal.log (ENNReal.ofReal G)
      rw [hF0, zero_add]
    rw [happ, hlogF]
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simpa using (le_add_of_nonneg_right (EReal.coe_nonneg.mpr hlog2))
  by_cases hG0 : G = 0
  · have hlogG : generatorLog g y = ⊥ := by
      rw [generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal G) = ⊥
      simp [hG0]
    have happ : generatorLog (Fin.append f g) y = generatorLog f y := by
      rw [generatorLog_append_eq_log_add, generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal (F + G)) = ENNReal.log (ENNReal.ofReal F)
      rw [hG0, add_zero]
    rw [happ, hlogG]
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simpa using (le_add_of_nonneg_right (EReal.coe_nonneg.mpr hlog2))
  have hFpos : 0 < F := lt_of_le_of_ne hF (Ne.symm hF0)
  have hGpos : 0 < G := lt_of_le_of_ne hG (Ne.symm hG0)
  have hsumpos : 0 < F + G := add_pos_of_pos_of_nonneg hFpos hG
  have hlogf : generatorLog f y = ENNReal.log (ENNReal.ofReal F) := by
    rw [generatorLog_eq_log_sum]
    rfl
  have hlogg : generatorLog g y = ENNReal.log (ENNReal.ofReal G) := by
    rw [generatorLog_eq_log_sum]
    rfl
  rw [generatorLog_append_eq_log_add, hlogf, hlogg,
    ENNReal.log_ofReal_of_pos hsumpos, ENNReal.log_ofReal_of_pos hFpos,
    ENNReal.log_ofReal_of_pos hGpos]
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases le_total F G with hFG | hGF
  · have hlogFG : Real.log F ≤ Real.log G := Real.log_le_log hFpos hFG
    rw [max_eq_right (EReal.coe_le_coe_iff.mpr hlogFG)]
    refine EReal.coe_le_coe_iff.mpr ?_
    calc
      Real.log (F + G) ≤ Real.log (2 * G) :=
        Real.log_le_log hsumpos (by nlinarith)
      _ = Real.log G + Real.log 2 := by
        rw [Real.log_mul (by norm_num) hGpos.ne']
        ring
  · have hlogGF : Real.log G ≤ Real.log F := Real.log_le_log hGpos hGF
    rw [max_eq_left (EReal.coe_le_coe_iff.mpr hlogGF)]
    refine EReal.coe_le_coe_iff.mpr ?_
    calc
      Real.log (F + G) ≤ Real.log (2 * F) :=
        Real.log_le_log hsumpos (by nlinarith)
      _ = Real.log F + Real.log 2 := by
        rw [Real.log_mul (by norm_num) hFpos.ne']
        ring


lemma HolomorphicGeneratorsAt.append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m n : ℕ} {f : Fin m → E → ℂ} {g : Fin n → E → ℂ} {x : E}
    (hf : HolomorphicGeneratorsAt f x) (hg : HolomorphicGeneratorsAt g x) :
    HolomorphicGeneratorsAt (Fin.append f g) x := by
  obtain ⟨U, hU, hxU, hUf⟩ := hf
  obtain ⟨V, hV, hxV, hVg⟩ := hg
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [Fin.append] using (hUf j).mono inter_subset_left
  · intro j
    simpa [Fin.append] using (hVg j).mono inter_subset_right


lemma eventualEq_max_append_presentation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E} {c : ℝ} {m n : ℕ}
    {f : Fin m → E → ℂ} {g : Fin n → E → ℂ}
    (hc : 0 < c) {b d : E → ℝ}
    (hub : u =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog f y + (b y : EReal))
    (hvd : v =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog g y + (d y : EReal)) :
    let r : E → ℝ := fun y =>
      if generatorNormSq f y = 0 then d y
      else if generatorNormSq g y = 0 then b y
      else (max (u y) (v y)).toReal -
        (((c : EReal) * generatorLog (Fin.append f g) y).toReal)
    (fun y => max (u y) (v y)) =ᶠ[𝓝 x]
      fun y => (c : EReal) * generatorLog (Fin.append f g) y + (r y : EReal) := by
  dsimp
  filter_upwards [hub, hvd] with y huy hvy
  by_cases hf : generatorNormSq f y = 0
  · have hlogf : generatorLog f y = ⊥ := by
      rw [generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal (generatorNormSq f y)) = ⊥
      simp [hf]
    have happ : generatorLog (Fin.append f g) y = generatorLog g y := by
      rw [generatorLog_append_eq_log_add, generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal
        (generatorNormSq f y + generatorNormSq g y)) =
        ENNReal.log (ENNReal.ofReal (generatorNormSq g y))
      rw [hf, zero_add]
    rw [if_pos hf]
    rw [huy, hlogf, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hc), EReal.bot_add,
      max_eq_right bot_le, happ, hvy]
  by_cases hg : generatorNormSq g y = 0
  · have hlogg : generatorLog g y = ⊥ := by
      rw [generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal (generatorNormSq g y)) = ⊥
      simp [hg]
    have happ : generatorLog (Fin.append f g) y = generatorLog f y := by
      rw [generatorLog_append_eq_log_add, generatorLog_eq_log_sum]
      change ENNReal.log (ENNReal.ofReal
        (generatorNormSq f y + generatorNormSq g y)) =
        ENNReal.log (ENNReal.ofReal (generatorNormSq f y))
      rw [hg, add_zero]
    rw [if_neg hf, if_pos hg]
    rw [hvy, hlogg, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hc), EReal.bot_add,
      max_eq_left bot_le, happ, huy]
  have hFpos : 0 < generatorNormSq f y :=
    lt_of_le_of_ne (generatorNormSq_nonneg f y) (Ne.symm hf)
  have hGpos : 0 < generatorNormSq g y :=
    lt_of_le_of_ne (generatorNormSq_nonneg g y) (Ne.symm hg)
  have hHpos : 0 < generatorNormSq f y + generatorNormSq g y :=
    add_pos_of_pos_of_nonneg hFpos (generatorNormSq_nonneg g y)
  have hlogf : generatorLog f y = (Real.log (generatorNormSq f y) : EReal) := by
    rw [generatorLog_eq_log_sum]
    exact ENNReal.log_ofReal_of_pos hFpos
  have hlogg : generatorLog g y = (Real.log (generatorNormSq g y) : EReal) := by
    rw [generatorLog_eq_log_sum]
    exact ENNReal.log_ofReal_of_pos hGpos
  have hlogh : generatorLog (Fin.append f g) y =
      (Real.log (generatorNormSq f y + generatorNormSq g y) : EReal) := by
    rw [generatorLog_append_eq_log_add]
    exact ENNReal.log_ofReal_of_pos hHpos
  have hucoe : u y =
      ((c * Real.log (generatorNormSq f y) + b y : ℝ) : EReal) := by
    rw [huy, hlogf, ← EReal.coe_mul, ← EReal.coe_add]
  have hvcoe : v y =
      ((c * Real.log (generatorNormSq g y) + d y : ℝ) : EReal) := by
    rw [hvy, hlogg, ← EReal.coe_mul, ← EReal.coe_add]
  have hhcoe : (c : EReal) * generatorLog (Fin.append f g) y =
      ((c * Real.log (generatorNormSq f y + generatorNormSq g y) : ℝ) : EReal) := by
    rw [hlogh, ← EReal.coe_mul]
  let A : ℝ := c * Real.log (generatorNormSq f y) + b y
  let B : ℝ := c * Real.log (generatorNormSq g y) + d y
  let H : ℝ := c * Real.log (generatorNormSq f y + generatorNormSq g y)
  have hmaxcoe : max (u y) (v y) = ((max A B : ℝ) : EReal) := by
    rw [hucoe, hvcoe]
    change max ((A : ℝ) : EReal) ((B : ℝ) : EReal) = ((max A B : ℝ) : EReal)
    rcases le_total A B with hAB | hBA
    · rw [max_eq_right (EReal.coe_le_coe_iff.mpr hAB), max_eq_right hAB]
    · rw [max_eq_left (EReal.coe_le_coe_iff.mpr hBA), max_eq_left hBA]
  have hhcoe' : (c : EReal) * generatorLog (Fin.append f g) y = (H : EReal) := by
    exact hhcoe
  rw [if_neg hf, if_neg hg, hmaxcoe, hhcoe']
  simp only [EReal.toReal_coe]
  rw [← EReal.coe_add]
  congr 1
  ring



lemma boundedRealGermAt_max_append_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E} {c : ℝ} {m n : ℕ}
    {f : Fin m → E → ℂ} {g : Fin n → E → ℂ}
    (hc : 0 < c) {b d : E → ℝ}
    (hb : BoundedRealGermAt b x) (hd : BoundedRealGermAt d x)
    (hub : u =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog f y + (b y : EReal))
    (hvd : v =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog g y + (d y : EReal)) :
    let r : E → ℝ := fun y =>
      if generatorNormSq f y = 0 then d y
      else if generatorNormSq g y = 0 then b y
      else (max (u y) (v y)).toReal -
        (((c : EReal) * generatorLog (Fin.append f g) y).toReal)
    BoundedRealGermAt r x := by
  dsimp
  obtain ⟨Cb, hCb0, hCb⟩ := hb
  obtain ⟨Cd, hCd0, hCd⟩ := hd
  let K : ℝ := Cb + Cd + c * Real.log 2
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hcLog2 : 0 ≤ c * Real.log 2 := mul_nonneg hc.le hlog2
  have hK0 : 0 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK0, ?_⟩
  filter_upwards [hCb, hCd, hub, hvd] with y hyb hyd huy hvy
  by_cases hf : generatorNormSq f y = 0
  · rw [if_pos hf]
    calc
      |d y| ≤ Cd := hyd
      _ ≤ K := by dsimp [K]; linarith
  by_cases hg : generatorNormSq g y = 0
  · rw [if_neg hf, if_pos hg]
    calc
      |b y| ≤ Cb := hyb
      _ ≤ K := by dsimp [K]; linarith
  let F : ℝ := generatorNormSq f y
  let G : ℝ := generatorNormSq g y
  have hF0 : 0 ≤ F := generatorNormSq_nonneg f y
  have hG0 : 0 ≤ G := generatorNormSq_nonneg g y
  have hFpos : 0 < F := lt_of_le_of_ne hF0 (Ne.symm hf)
  have hGpos : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hg)
  have hSpos : 0 < F + G := add_pos_of_pos_of_nonneg hFpos hG0
  have hlogf : generatorLog f y = (Real.log F : EReal) := by
    rw [generatorLog_eq_log_sum]
    exact ENNReal.log_ofReal_of_pos hFpos
  have hlogg : generatorLog g y = (Real.log G : EReal) := by
    rw [generatorLog_eq_log_sum]
    exact ENNReal.log_ofReal_of_pos hGpos
  have hlogh : generatorLog (Fin.append f g) y = (Real.log (F + G) : EReal) := by
    rw [generatorLog_append_eq_log_add]
    exact ENNReal.log_ofReal_of_pos hSpos
  let A : ℝ := c * Real.log F + b y
  let B : ℝ := c * Real.log G + d y
  let H : ℝ := c * Real.log (F + G)
  have hucoe : u y = (A : EReal) := by
    rw [huy, hlogf, ← EReal.coe_mul, ← EReal.coe_add]
  have hvcoe : v y = (B : EReal) := by
    rw [hvy, hlogg, ← EReal.coe_mul, ← EReal.coe_add]
  have hhcoe : (c : EReal) * generatorLog (Fin.append f g) y = (H : EReal) := by
    rw [hlogh, ← EReal.coe_mul]
  have hmaxcoe : max (u y) (v y) = ((max A B : ℝ) : EReal) := by
    rw [hucoe, hvcoe]
    rcases le_total A B with hAB | hBA
    · rw [max_eq_right (EReal.coe_le_coe_iff.mpr hAB), max_eq_right hAB]
    · rw [max_eq_left (EReal.coe_le_coe_iff.mpr hBA), max_eq_left hBA]
  rw [if_neg hf, if_neg hg, hmaxcoe, hhcoe]
  simp only [EReal.toReal_coe]
  have hlogF : Real.log F ≤ Real.log (F + G) :=
    Real.log_le_log hFpos (le_add_of_nonneg_right hG0)
  have hlogG : Real.log G ≤ Real.log (F + G) :=
    Real.log_le_log hGpos (le_add_of_nonneg_left hF0)
  have hAupper : A ≤ H + (Cb + Cd) := by
    dsimp [A, H]
    have hmul := mul_le_mul_of_nonneg_left hlogF hc.le
    have hbupper := (abs_le.mp hyb).2
    linarith
  have hBupper : B ≤ H + (Cb + Cd) := by
    dsimp [B, H]
    have hmul := mul_le_mul_of_nonneg_left hlogG hc.le
    have hdupper := (abs_le.mp hyd).2
    linarith
  have hupper : max A B ≤ H + (Cb + Cd) := max_le hAupper hBupper
  have hlower : H ≤ max A B + K := by
    rcases le_total F G with hFG | hGF
    · have hlog : Real.log (F + G) ≤ Real.log G + Real.log 2 := by
        calc
          Real.log (F + G) ≤ Real.log (2 * G) :=
            Real.log_le_log hSpos (by nlinarith)
          _ = Real.log G + Real.log 2 := by
            rw [Real.log_mul (by norm_num) hGpos.ne']
            ring
      have hBbelow : c * Real.log G ≤ B + Cd := by
        dsimp [B]
        have hdlower := (abs_le.mp hyd).1
        linarith
      dsimp [H, K]
      nlinarith [mul_le_mul_of_nonneg_left hlog hc.le, le_max_right A B]
    · have hlog : Real.log (F + G) ≤ Real.log F + Real.log 2 := by
        calc
          Real.log (F + G) ≤ Real.log (2 * F) :=
            Real.log_le_log hSpos (by nlinarith)
          _ = Real.log F + Real.log 2 := by
            rw [Real.log_mul (by norm_num) hFpos.ne']
            ring
      have hAbelow : c * Real.log F ≤ A + Cb := by
        dsimp [A]
        have hblower := (abs_le.mp hyb).1
        linarith
      dsimp [H, K]
      nlinarith [mul_le_mul_of_nonneg_left hlog hc.le, le_max_left A B]
  rw [abs_le]
  constructor <;> dsimp [K] at * <;> nlinarith


/-- A finite maximum of logarithmic presentations with one positive coefficient
is represented by the concatenated generator family.  The bounded remainder is
explicit: on the nonzero locus it is the difference between the maximum and
the concatenated logarithm, and on either zero locus it is the remaining
original remainder. -/
theorem LogarithmicTypeAt.max_of_generators
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E} {c : ℝ} {m n : ℕ}
    {f : Fin m → E → ℂ} {g : Fin n → E → ℂ}
    (hu : LogarithmicTypeAt u c f x) (hv : LogarithmicTypeAt v c g x) :
    LogarithmicTypeAt (fun y => max (u y) (v y)) c (Fin.append f g) x := by
  obtain ⟨hc, hf, b, hb, hub⟩ := hu
  obtain ⟨-, hg, d, hd, hvd⟩ := hv
  let r : E → ℝ := fun y =>
    if generatorNormSq f y = 0 then d y
    else if generatorNormSq g y = 0 then b y
    else (max (u y) (v y)).toReal -
      (((c : EReal) * generatorLog (Fin.append f g) y).toReal)
  refine ⟨hc, HolomorphicGeneratorsAt.append hf hg, r, ?_, ?_⟩
  · exact boundedRealGermAt_max_append_remainder hc hb hd hub hvd
  · exact eventualEq_max_append_presentation hc hub hvd

/-- The rational analytic-singularity convention is closed under a maximum of
two arbitrary finite generator presentations having the same coefficient. -/
theorem HasAnalyticSingularityTypeAt.max_of_generators
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E} {c : ℚ} {m n : ℕ}
    {f : Fin m → E → ℂ} {g : Fin n → E → ℂ}
    (hu : LogarithmicTypeAt u (c : ℝ) f x)
    (hv : LogarithmicTypeAt v (c : ℝ) g x) :
    HasAnalyticSingularityTypeAt (fun y => max (u y) (v y)) x :=
  ⟨c, m + n, Fin.append f g, LogarithmicTypeAt.max_of_generators hu hv⟩

end Hironaka.DemaillyAnalyticType
