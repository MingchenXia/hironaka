import Hironaka.Analytic.PshBallSupSlope
import Hironaka.Analytic.PshBallDeficitComparison
import Hironaka.Analytic.PshDiscLocalGlobal
import Hironaka.Analytic.PotentialTheory.LocalPshDiscControl

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# Subadditivity of Lelong exponents, locally on a ball

Source: Demailly, *Complex analytic and differential geometry*, III.5.

This is the analytic heart of `LelongNumberAdditivity.lelongNumber_add_le`.  Let `P, Q` be
plurisubharmonic on `ball p R`, neither identically `⊥`, with ball-supremum slopes `sP, sQ` at
`-∞` (`Hironaka.PshBallSupSlope`).  If `γ ≥ 0` is an admissible logarithmic exponent for the
**sum**, i.e. `P + Q ≤ γ log ‖· - p‖ + C` on a punctured ball, then `γ ≤ sP + sQ`.

The argument is the Harnack sandwich, run on the *unnormalised* deficit integral over
`ball p (K r)` with `r = e^t`:

* the admissible bound for the sum gives a **lower** bound for that integral, of size
  `μ (ball p (K r)) · (C_P + C_Q - γ log (K r) - C)`;
* the integral **splits** as a sum of the two deficit integrals of `P` and `Q`;
* each summand is bounded **above**, by the Harnack comparison, by
  `μ (ball 0 ((K+1) r))` times the pointwise deficit at a point where the potential is within
  `1` of its supremum on `closedBall p r`, and there the slope's lower bound applies.

The factor `r^{dim}` cancels between the two ball volumes, leaving
`(K/(K+1))^{dim} · γ ≤ sP + sQ + 2ε` for every `ε > 0` and every `K ≥ 1`.  Letting `ε → 0` and
`K → ∞` (with Bernoulli's inequality `1 - d/(K+1) ≤ (K/(K+1))^d` making the last step explicit)
gives `γ ≤ sP + sQ`.

No module in the root import closure imports this file.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PshLocalLelongSubadditive

open Hironaka Hironaka.PshBallSup Hironaka.PshBallSupSlope
  Hironaka.PshBallDeficitComparison

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- A value strictly below the ball supremum is attained strictly, at some point of the ball. -/
theorem exists_lt_of_lt_ballSup {u : E → EReal} {p : E} {t : ℝ} {a : EReal}
    (h : a < ballSup u p t) : ∃ z ∈ closedBall p (Real.exp t), a < u z := by
  rw [ballSup] at h
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp h
  obtain ⟨hmem, hval⟩ := lt_iSup_iff.mp hz
  exact ⟨z, hmem, hval⟩

/-- Bernoulli's inequality in the form used to let `K → ∞`. -/
theorem one_sub_div_le_div_pow {K : ℝ} (hK : 1 ≤ K) (d : ℕ) :
    1 - (d : ℝ) / (K + 1) ≤ K ^ d / (K + 1) ^ d := by
  have hK1 : (0:ℝ) < K + 1 := by linarith
  have hb : (-2 : ℝ) ≤ -(1 / (K + 1)) := by
    have : 1 / (K + 1) ≤ 1 := by
      rw [div_le_one hK1]; linarith
    linarith
  have hpow := one_add_mul_le_pow hb d
  have hbase : 1 + -(1 / (K + 1)) = K / (K + 1) := by
    field_simp
    ring
  rw [hbase] at hpow
  rw [← div_pow]
  calc 1 - (d : ℝ) / (K + 1) = 1 + (d : ℝ) * -(1 / (K + 1)) := by ring
    _ ≤ (K / (K + 1)) ^ d := hpow

/-- **Subadditivity of admissible logarithmic exponents, on a ball.**  An admissible exponent
for `P + Q` is bounded by the sum of the ball-supremum slopes of `P` and of `Q`. -/
theorem le_slope_add_of_admissible_sum [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {P Q : E → EReal} {p : E} {R : ℝ} (hR : 0 < R)
    (hP : PlurisubharmonicOn P (ball p R)) (hQ : PlurisubharmonicOn Q (ball p R))
    (hneP : ∃ a ∈ ball p R, P a ≠ ⊥) (hneQ : ∃ a ∈ ball p R, Q a ≠ ⊥)
    {sP sQ : ℝ}
    (hslP : ∀ ε : ℝ, 0 < ε → ∃ t₁ C' : ℝ, ∀ t < t₁,
      ((sP + ε) * t + C' : ℝ) ≤ (ballSup P p t).toReal)
    (hslQ : ∀ ε : ℝ, 0 < ε → ∃ t₁ C' : ℝ, ∀ t < t₁,
      ((sQ + ε) * t + C' : ℝ) ≤ (ballSup Q p t).toReal)
    {γ C ρ : ℝ} (hγ : 0 ≤ γ) (hρ : 0 < ρ)
    (hadm : ∀ z : E, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
      P z + Q z ≤ ((γ * Real.log ‖z - p‖ + C : ℝ) : EReal)) :
    γ ≤ sP + sQ := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd
  set V : ℝ≥0∞ := μ (ball (0 : E) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  -- a slightly smaller radius, on which both potentials are bounded above
  set Rq : ℝ := R / 2 with hRq
  have hRq0 : 0 < Rq := by simp [hRq]; linarith
  have hRqR : Rq < R := by simp [hRq]; linarith
  have hclsub : closedBall p Rq ⊆ ball p R := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hRqR)
  obtain ⟨CP, -, hCP⟩ :=
    hP.exists_nonnegative_compact_upper_bound (isCompact_closedBall p Rq) hclsub
  obtain ⟨CQ, -, hCQ⟩ :=
    hQ.exists_nonnegative_compact_upper_bound (isCompact_closedBall p Rq) hclsub
  have hballsub : ball p Rq ⊆ ball p R := ball_subset_ball hRqR.le
  have hCPball : ∀ z ∈ ball p Rq, P z ≤ (CP : EReal) := fun z hz =>
    hCP z (ball_subset_closedBall hz)
  have hCQball : ∀ z ∈ ball p Rq, Q z ≤ (CQ : EReal) := fun z hz =>
    hCQ z (ball_subset_closedBall hz)
  have hdiscP : DiscPshOn P (ball p Rq) :=
    _root_.Hironaka.PotentialTheory.LocalToGlobal.PlurisubharmonicOn.discPshOn (hP.mono hballsub)
  have hdiscQ : DiscPshOn Q (ball p Rq) :=
    _root_.Hironaka.PotentialTheory.LocalToGlobal.PlurisubharmonicOn.discPshOn (hQ.mono hballsub)
  -- the master inequality, for every tolerance `ε` and every Harnack parameter `K`
  have master : ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, 1 ≤ K →
      K ^ d / (K + 1) ^ d * γ ≤ sP + sQ + 2 * ε := by
    intro ε hε K hK
    have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK
    have hK1 : (0:ℝ) < K + 1 := by linarith
    have hK2 : (0:ℝ) < K + 2 := by linarith
    obtain ⟨t₁P, C'P, hsP⟩ := hslP ε hε
    obtain ⟨t₁Q, C'Q, hsQ⟩ := hslQ ε hε
    set m : ℝ := min (Rq / (K + 2)) (ρ / K) with hm
    have hm0 : 0 < m := lt_min (by positivity) (by positivity)
    set Tb : ℝ := min (min 0 (min t₁P t₁Q)) (Real.log m) with hTb
    set c : ℝ := K ^ d / (K + 1) ^ d with hc
    set S : ℝ := sP + sQ + 2 * ε with hS
    set B : ℝ := CP + CQ - γ * Real.log K - C with hB
    set B' : ℝ := CP + CQ - C'P - C'Q + 2 with hB'
    have key : ∀ t < Tb, (S - c * γ) * t ≤ B' - c * B := by
      intro t ht
      have ht0 : t < 0 :=
        lt_of_lt_of_le ht ((min_le_left _ _).trans (min_le_left _ _))
      have htP : t < t₁P :=
        lt_of_lt_of_le ht ((min_le_left _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
      have htQ : t < t₁Q :=
        lt_of_lt_of_le ht ((min_le_left _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))
      have htm : t < Real.log m := lt_of_lt_of_le ht (min_le_right _ _)
      set r : ℝ := Real.exp t with hr
      have hr0 : 0 < r := Real.exp_pos t
      have hrm : r < m := (Real.lt_log_iff_exp_lt hm0).mp htm
      have hrK2 : (K + 2) * r ≤ Rq := by
        have : r < Rq / (K + 2) := lt_of_lt_of_le hrm (min_le_left _ _)
        rw [lt_div_iff₀ hK2] at this
        linarith [this]
      have hrρ : K * r ≤ ρ := by
        have : r < ρ / K := lt_of_lt_of_le hrm (min_le_right _ _)
        rw [lt_div_iff₀ hK0] at this
        linarith [this]
      have hKr0 : 0 < K * r := by positivity
      have hKrRq : K * r < Rq := by nlinarith
      have hrR : r < R := by nlinarith
      have hsubKr : ball p (K * r) ⊆ ball p Rq := ball_subset_ball hKrRq.le
      -- a near-maximal point for `P` on the small closed ball
      have hzP : (((sP + ε) * t + C'P - 1 : ℝ) : EReal) < ballSup P p t := by
        rw [ballSup_eq_coe_toReal (μ := μ) hP hneP hrR]
        exact EReal.coe_lt_coe_iff.mpr (by linarith [hsP t htP])
      obtain ⟨z₀, hz₀mem, hz₀val⟩ := exists_lt_of_lt_ballSup hzP
      have hzQ : (((sQ + ε) * t + C'Q - 1 : ℝ) : EReal) < ballSup Q p t := by
        rw [ballSup_eq_coe_toReal (μ := μ) hQ hneQ hrR]
        exact EReal.coe_lt_coe_iff.mpr (by linarith [hsQ t htQ])
      obtain ⟨z₁, hz₁mem, hz₁val⟩ := exists_lt_of_lt_ballSup hzQ
      have hz₀norm : ‖z₀ - p‖ ≤ r := by
        rw [mem_closedBall, dist_eq_norm] at hz₀mem; exact hz₀mem
      have hz₁norm : ‖z₁ - p‖ ≤ r := by
        rw [mem_closedBall, dist_eq_norm] at hz₁mem; exact hz₁mem
      have hz₀Rq : z₀ ∈ ball p Rq := by
        rw [mem_ball, dist_eq_norm]; nlinarith
      have hz₁Rq : z₁ ∈ ball p Rq := by
        rw [mem_ball, dist_eq_norm]; nlinarith
      set DP : ℝ := CP - ((sP + ε) * t + C'P - 1) with hDP
      set DQ : ℝ := CQ - ((sQ + ε) * t + C'Q - 1) with hDQ
      have hDP0 : 0 ≤ DP := by
        have := hz₀val.trans_le (hCPball z₀ hz₀Rq)
        have h' : (sP + ε) * t + C'P - 1 < CP := EReal.coe_lt_coe_iff.mp this
        simp [hDP]; linarith
      have hDQ0 : 0 ≤ DQ := by
        have := hz₁val.trans_le (hCQball z₁ hz₁Rq)
        have h' : (sQ + ε) * t + C'Q - 1 < CQ := EReal.coe_lt_coe_iff.mp this
        simp [hDQ]; linarith
      have hdefP : ((CP : EReal) - P z₀).toENNReal ≤ ENNReal.ofReal DP := by
        calc ((CP : EReal) - P z₀).toENNReal
            ≤ ((CP : EReal) - (((sP + ε) * t + C'P - 1 : ℝ) : EReal)).toENNReal :=
              EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hz₀val.le)
          _ = ENNReal.ofReal DP := by rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
      have hdefQ : ((CQ : EReal) - Q z₁).toENNReal ≤ ENNReal.ofReal DQ := by
        calc ((CQ : EReal) - Q z₁).toENNReal
            ≤ ((CQ : EReal) - (((sQ + ε) * t + C'Q - 1 : ℝ) : EReal)).toENNReal :=
              EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hz₁val.le)
          _ = ENNReal.ofReal DQ := by rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
      -- the deficit chain
      set A : ℝ := CP + CQ - (γ * Real.log (K * r) + C) with hA
      have hchain : ENNReal.ofReal A * μ (ball p (K * r)) ≤
          μ (ball (0 : E) ((K + 1) * r)) * ENNReal.ofReal (DP + DQ) := by
        have hlow := le_deficitInt_of_log_bound (μ := μ) (w := fun z => P z + Q z)
          (Cw := CP + CQ) (γ := γ) (C := C) (ρ := ρ) hγ hadm (r := K * r) hrρ
        have hadd := deficitInt_add (u := P) (v := Q) (U := ball p Rq)
          (s := ball p (K * r)) hdiscP measurableSet_ball hsubKr
          (Cu := CP) (Cv := CQ) (fun z hz => hCPball z (hsubKr hz))
          (fun z hz => hCQball z (hsubKr hz)) μ
        have hHP := deficitInt_le_of_near_center (μ := μ) hdiscP hCPball
          (r := r) (K := K) hrK2 hz₀norm
        have hHQ := deficitInt_le_of_near_center (μ := μ) hdiscQ hCQball
          (r := r) (K := K) hrK2 hz₁norm
        calc ENNReal.ofReal A * μ (ball p (K * r))
            ≤ ∫⁻ z in ball p (K * r),
                (((CP + CQ : ℝ) : EReal) - (P z + Q z)).toENNReal ∂μ := hlow
          _ = (∫⁻ z in ball p (K * r), ((CP : EReal) - P z).toENNReal ∂μ) +
                ∫⁻ z in ball p (K * r), ((CQ : EReal) - Q z).toENNReal ∂μ := hadd
          _ ≤ μ (ball (0 : E) ((K + 1) * r)) * ((CP : EReal) - P z₀).toENNReal +
                μ (ball (0 : E) ((K + 1) * r)) * ((CQ : EReal) - Q z₁).toENNReal :=
              add_le_add hHP hHQ
          _ ≤ μ (ball (0 : E) ((K + 1) * r)) * ENNReal.ofReal DP +
                μ (ball (0 : E) ((K + 1) * r)) * ENNReal.ofReal DQ :=
              add_le_add (by gcongr) (by gcongr)
          _ = μ (ball (0 : E) ((K + 1) * r)) * (ENNReal.ofReal DP + ENNReal.ofReal DQ) :=
              (mul_add _ _ _).symm
          _ = μ (ball (0 : E) ((K + 1) * r)) * ENNReal.ofReal (DP + DQ) := by
              rw [ENNReal.ofReal_add hDP0 hDQ0]
      -- turn the volumes into powers and cancel `r ^ d`
      rw [Measure.addHaar_ball_of_pos μ p hKr0,
        Measure.addHaar_ball_of_pos μ (0 : E) (by positivity : (0:ℝ) < (K + 1) * r)] at hchain
      have hrw1 : ENNReal.ofReal A * (ENNReal.ofReal ((K * r) ^ d) * V) =
          ENNReal.ofReal ((K * r) ^ d * A) * V := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (K * r) ^ d)]
        ring
      have hrw2 : ENNReal.ofReal (((K + 1) * r) ^ d) * V * ENNReal.ofReal (DP + DQ) =
          ENNReal.ofReal (((K + 1) * r) ^ d * (DP + DQ)) * V := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((K + 1) * r) ^ d)]
        ring
      rw [hrw1, hrw2] at hchain
      have hreal : (K * r) ^ d * A ≤ ((K + 1) * r) ^ d * (DP + DQ) := by
        have hcancel := (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp hchain
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcancel
      -- divide by `r ^ d` and by `(K + 1) ^ d`
      have hrd : (0:ℝ) < r ^ d := by positivity
      have hK1d : (0:ℝ) < (K + 1) ^ d := by positivity
      have hsplit : K ^ d * A ≤ (K + 1) ^ d * (DP + DQ) := by
        rw [mul_pow, mul_pow] at hreal
        have h' : K ^ d * A * r ^ d ≤ (K + 1) ^ d * (DP + DQ) * r ^ d := by nlinarith [hreal]
        exact le_of_mul_le_mul_right (by linarith [h']) hrd
      have hcA : c * A ≤ DP + DQ := by
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ hK1d]
        nlinarith [hsplit]
      -- rewrite `A` and `DP + DQ` affinely in `t`
      have hlogKr : Real.log (K * r) = Real.log K + t := by
        rw [Real.log_mul hK0.ne' hr0.ne', hr, Real.log_exp]
      have hAt : A = B - γ * t := by rw [hA, hB, hlogKr]; ring
      have hDt : DP + DQ = B' - S * t := by rw [hDP, hDQ, hB', hS]; ring
      rw [hAt, hDt] at hcA
      nlinarith [hcA]
    -- the master inequality follows from `key` by letting `t → -∞`
    by_contra hcon
    rw [not_le] at hcon
    have hpos : 0 < c * γ - S := by simp only [hc, hS] at hcon ⊢; linarith
    set X : ℝ := B' - c * B with hX
    set a : ℝ := c * γ - S with ha
    have hchoice : ∃ t : ℝ, t < Tb ∧ |X| + 1 ≤ a * (-t) := by
      refine ⟨min (Tb - 1) (-((|X| + 1) / a)), lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
      have h1 : min (Tb - 1) (-((|X| + 1) / a)) ≤ -((|X| + 1) / a) := min_le_right _ _
      have h2 : (|X| + 1) / a ≤ -min (Tb - 1) (-((|X| + 1) / a)) := by linarith
      have := (div_le_iff₀ hpos).mp h2
      nlinarith [this]
    obtain ⟨t, htTb, hta⟩ := hchoice
    have := key t htTb
    have habs : X ≤ |X| := le_abs_self X
    nlinarith [this, hta, habs]
  -- let `ε → 0` and `K → ∞`
  refine le_of_forall_pos_le_add ?_
  intro ε' hε'
  set K : ℝ := 1 + 2 * (γ * (d : ℝ)) / ε' with hK
  have hd0 : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 ≤ 2 * (γ * (d : ℝ)) / ε' := by positivity
    linarith
  have hK1pos : (0:ℝ) < K + 1 := by linarith
  have hmaster := master (ε' / 4) (by linarith) K hK1
  have hbern := one_sub_div_le_div_pow hK1 d
  have hstep : γ * (1 - (d : ℝ) / (K + 1)) ≤ K ^ d / (K + 1) ^ d * γ := by
    nlinarith [hbern, hγ]
  have htail : γ * (d : ℝ) / (K + 1) ≤ ε' / 2 := by
    rw [div_le_iff₀ hK1pos, hK]
    have hexp : ε' / 2 * (1 + 2 * (γ * (d : ℝ)) / ε' + 1) = ε' + γ * (d : ℝ) := by
      field_simp
      ring
    rw [hexp]
    nlinarith [mul_nonneg hγ hd0]
  have hfinal : γ - γ * (d : ℝ) / (K + 1) ≤ sP + sQ + 2 * (ε' / 4) := by
    have hrw : γ * (1 - (d : ℝ) / (K + 1)) = γ - γ * (d : ℝ) / (K + 1) := by ring
    linarith [hstep.trans hmaster, hrw]
  linarith [hfinal, htail]

end

end Hironaka.PshLocalLelongSubadditive
