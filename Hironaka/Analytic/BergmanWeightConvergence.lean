import Hironaka.Analytic.BergmanSubadditivity

set_option autoImplicit false

/-!
# Pointwise convergence of the Bergman weights

For a plurisubharmonic `P` on a bounded open convex domain `B ⊆ ℂ^d`, the Bergman weights
`φ_m = m⁻¹ log K_{mP}` (with `K_{mP} = bergmanSup B e^{-mP}` the Bergman kernel on the diagonal)
converge to `P` at every point of `B`, including the poles (`tendsto_bergmanWeight`).  This is
Demailly's convergence statement (Demailly 1992, Prop. 3.1; *Analytic methods*, Thm 13.2(a)),
programme step A8 of `TN.3.3.DEMPROVE`, in its local form.  The two estimates are:

* `le_bergmanWeight` (Ohsawa--Takegoshi from a point, `BergmanSupWeight.exists_one_le_mul_bergmanSup`):
  `P(y) - (log C)/m ≤ φ_m(y)`, with `C` depending only on `d` and the radius of `B`;
* `bergmanWeight_le` (sub-mean value inequality for `|f|²`): if `closedBall y r ⊆ B` and `P ≤ b`
  on `ball y r`, then `φ_m(y) ≤ b - m⁻¹ log vol(ball y r)`.

The upper semicontinuity of `P` then squeezes `φ_m(y)` to `P(y)`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.BergmanWeightConvergence

noncomputable section

open BergmanSupWeight BergmanSubadditivity

section MeanValue

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- **The mean-value upper bound for the kernel.**  If `closedBall y r ⊆ B` and `P ≤ b` on
`ball y r`, then `vol(ball y r) · K_{cP}(y) ≤ e^{cb}`. -/
theorem volume_mul_bergmanSup_le {B : Set (ComplexModel d)} (hB : IsOpen B)
    {P : ComplexModel d → EReal} {c : ℝ} (hc : 0 < c) {y : ComplexModel d} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall y r ⊆ B) {b : ℝ} (hb : ∀ z ∈ ball y r, P z ≤ b) :
    volume (ball y r) * bergmanSup B (fun z => multiplierWeight c (P z)) y ≤
      ENNReal.ofReal (Real.exp (c * b)) := by
  have hV0 : volume (ball y r) ≠ 0 := (measure_ball_pos volume y hr).ne'
  have hVtop : volume (ball y r) ≠ ⊤ := measure_ball_lt_top.ne
  have key : bergmanSup B (fun z => multiplierWeight c (P z)) y ≤
      ENNReal.ofReal (Real.exp (c * b)) / volume (ball y r) := by
    refine bergmanSup_le fun f hf => ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop), mul_comm]
    have hmv := lintegral_ball_normSq_ge hB hf.1 hr hsub
    refine hmv.trans ?_
    have hw : ∀ z ∈ ball y r, ENNReal.ofReal (‖f z‖ ^ 2) ≤
        ENNReal.ofReal (Real.exp (c * b)) *
          (ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight c (P z)) := by
      intro z hz
      have hlow : ENNReal.ofReal (Real.exp (-(c * b))) ≤ multiplierWeight c (P z) := by
        rw [← multiplierWeight_coe]
        exact multiplierWeight_antitone hc.le (hb z hz)
      calc ENNReal.ofReal (‖f z‖ ^ 2)
          = ENNReal.ofReal (Real.exp (c * b)) * ENNReal.ofReal (Real.exp (-(c * b))) *
              ENNReal.ofReal (‖f z‖ ^ 2) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
              Real.exp_zero, ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (c * b)) * multiplierWeight c (P z) *
              ENNReal.ofReal (‖f z‖ ^ 2) := by gcongr
        _ = _ := by ring
    calc ∫⁻ x in ball y r, ENNReal.ofReal (‖f x‖ ^ 2)
        ≤ ∫⁻ x in ball y r, ENNReal.ofReal (Real.exp (c * b)) *
            (ENNReal.ofReal (‖f x‖ ^ 2) * multiplierWeight c (P x)) :=
          setLIntegral_mono' measurableSet_ball hw
      _ = ENNReal.ofReal (Real.exp (c * b)) *
            ∫⁻ x in ball y r, ENNReal.ofReal (‖f x‖ ^ 2) * multiplierWeight c (P x) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (c * b)) *
            ∫⁻ x in B, ENNReal.ofReal (‖f x‖ ^ 2) * multiplierWeight c (P x) := by
          gcongr
          exact ball_subset_closedBall.trans hsub
      _ ≤ ENNReal.ofReal (Real.exp (c * b)) * 1 := by gcongr; exact hf.2
      _ = _ := mul_one _
  calc volume (ball y r) * bergmanSup B (fun z => multiplierWeight c (P z)) y
      ≤ volume (ball y r) * (ENNReal.ofReal (Real.exp (c * b)) / volume (ball y r)) := by
        gcongr
    _ = _ := ENNReal.mul_div_cancel hV0 hVtop

end MeanValue

/-- The Bergman weight `m⁻¹ log K_{mP}(y)` (an extended real; `-∞` where the kernel vanishes). -/
def bergmanWeight {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]
    (B : Set (ComplexModel d)) (P : ComplexModel d → EReal) (m : ℕ) (y : ComplexModel d) :
    EReal :=
  (((m : ℝ)⁻¹ : ℝ) : EReal) * bergmanLog B (fun z => multiplierWeight (m : ℝ) (P z)) y

section Bounds

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- `m⁻¹ log K ≤ b - m⁻¹ log v` from `v K ≤ e^{mb}`. -/
theorem bergmanWeight_le {B : Set (ComplexModel d)} (hB : IsOpen B)
    {P : ComplexModel d → EReal} {m : ℕ} (hm : 1 ≤ m) {y : ComplexModel d} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall y r ⊆ B) {b : ℝ} (hb : ∀ z ∈ ball y r, P z ≤ b) :
    bergmanWeight B P m y ≤
      ((b - (m : ℝ)⁻¹ * Real.log (volume (ball y r)).toReal : ℝ) : EReal) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set K := bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z)) y with hKdef
  have hmain := volume_mul_bergmanSup_le hB hmpos hr hsub hb
  rw [← hKdef] at hmain
  have hV0 : volume (ball y r) ≠ 0 := (measure_ball_pos volume y hr).ne'
  have hVtop : volume (ball y r) ≠ ⊤ := measure_ball_lt_top.ne
  set v : ℝ := (volume (ball y r)).toReal with hvdef
  have hv : 0 < v := ENNReal.toReal_pos hV0 hVtop
  have hKtop : K ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hV0] at hmain
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hmain)
  by_cases hK0 : K = 0
  · simp only [bergmanWeight, bergmanLog, ← hKdef, hK0, ENNReal.log_zero]
    rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr hmpos))]
    exact bot_le
  · set k : ℝ := K.toReal with hkdef
    have hk : 0 < k := ENNReal.toReal_pos hK0 hKtop
    have hKk : K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKtop).symm
    have hreal : v * k ≤ Real.exp (m * b) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    have hlog : Real.log v + Real.log k ≤ m * b := by
      rw [← Real.log_mul hv.ne' hk.ne', ← Real.log_exp (m * b)]
      exact Real.log_le_log (mul_pos hv hk) hreal
    simp only [bergmanWeight, bergmanLog, ← hKdef, hKk, ENNReal.log_ofReal_of_pos hk,
      ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have : (m : ℝ)⁻¹ * Real.log k ≤ (m : ℝ)⁻¹ * (m * b - Real.log v) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hmpos.le)
    calc (m : ℝ)⁻¹ * Real.log k ≤ (m : ℝ)⁻¹ * (m * b - Real.log v) := this
      _ = b - (m : ℝ)⁻¹ * Real.log v := by field_simp

end Bounds

/-- **The Ohsawa--Takegoshi lower bound for the Bergman weight**: `P(y) - (log C)/m ≤ φ_m(y)`. -/
theorem le_bergmanWeight (d : ℕ) : by
    letI : MeasurableSpace (ComplexModel d) := borel _
    letI : BorelSpace (ComplexModel d) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B → ∀ m : ℕ, 1 ≤ m →
      ∀ y ∈ B, ∀ p : ℝ, P y = p →
        (((p - (m : ℝ)⁻¹ * Real.log C : ℝ)) : EReal) ≤ bergmanWeight B P m y := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, hOT⟩ := exists_one_le_mul_bergmanSup d R hR
  refine ⟨C, hC, fun B hB hconv hbd P hP m hm y hy p hp => ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hPy : P y ≠ ⊥ := by rw [hp]; exact EReal.coe_ne_bot p
  obtain ⟨hmain, hpos, -⟩ := hOT B hB hconv hbd P hP (m : ℝ) hmpos y hy hPy
  set K := bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z)) y with hKdef
  have hKtop : K ≠ ⊤ := bergmanSup_multiplierWeight_ne_top hB hP hmpos hy
  set k : ℝ := K.toReal with hkdef
  have hk : 0 < k := ENNReal.toReal_pos hpos.ne' hKtop
  have hKk : K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKtop).symm
  rw [hp, multiplierWeight_coe, hKk, ← ENNReal.ofReal_mul hC.le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  have hlog : (m : ℝ) * p - Real.log C ≤ Real.log k := by
    have h1 : Real.log 1 ≤ Real.log (C * Real.exp (-((m : ℝ) * p)) * k) :=
      Real.log_le_log one_pos hmain
    rw [Real.log_one, Real.log_mul (by positivity) hk.ne', Real.log_mul hC.ne'
      (Real.exp_pos _).ne', Real.log_exp] at h1
    linarith
  simp only [bergmanWeight, bergmanLog, ← hKdef, hKk, ENNReal.log_ofReal_of_pos hk,
    ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have : (m : ℝ)⁻¹ * ((m : ℝ) * p - Real.log C) ≤ (m : ℝ)⁻¹ * Real.log k :=
    mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hmpos.le)
  calc p - (m : ℝ)⁻¹ * Real.log C = (m : ℝ)⁻¹ * ((m : ℝ) * p - Real.log C) := by field_simp
    _ ≤ _ := this

/-- **Demailly's Bergman weights converge pointwise** (local form): on a bounded open convex
`B ⊆ ℂ^d`, for `P` plurisubharmonic on `B`, `m⁻¹ log K_{mP}(y) → P(y)` at every `y ∈ B`
(in `EReal`, so poles included). -/
theorem tendsto_bergmanWeight (d : ℕ) : by
    letI : MeasurableSpace (ComplexModel d) := borel _
    letI : BorelSpace (ComplexModel d) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R →
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B →
      ∀ y ∈ B, Tendsto (fun m : ℕ => bergmanWeight B P m y) atTop (𝓝 (P y)) := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  intro R hR B hB hconv hbd P hP y hy
  obtain ⟨C, hC, hlow⟩ := le_bergmanWeight d R hR
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- below: `a < P y`, so `P y` is finite
    have hPtop : P y ≠ ⊤ := (hP y hy).ne_top
    have hPbot : P y ≠ ⊥ := ne_bot_of_gt ha
    set p : ℝ := (P y).toReal with hpdef
    have hp : P y = p := (EReal.coe_toReal hPtop hPbot).symm
    obtain ⟨q, haq, hqp⟩ := EReal.lt_iff_exists_real_btwn.mp (hp ▸ ha)
    rw [EReal.coe_lt_coe_iff] at hqp
    have hlim : Tendsto (fun m : ℕ => p - (m : ℝ)⁻¹ * Real.log C) atTop (𝓝 p) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (Real.log C)
      simpa using tendsto_const_nhds.sub this
    filter_upwards [hlim.eventually (lt_mem_nhds hqp), eventually_ge_atTop 1] with m hm hm1
    exact haq.trans_le ((EReal.coe_le_coe_iff.mpr hm.le).trans
      (hlow B hB hconv hbd P hP m hm1 y hy p hp))
  · -- above: `P y < a`; use upper semicontinuity at `y`
    obtain ⟨b, hPb, hba⟩ := EReal.lt_iff_exists_real_btwn.mp ha
    have husc := (hP y hy).upperSemicontinuousAt (b : EReal) hPb
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (inter_mem husc (hB.mem_nhds hy))
    set r : ℝ := ε / 2 with hrdef
    have hr : 0 < r := by positivity
    have hsub : closedBall y r ⊆ B := fun z hz =>
      (hεsub (closedBall_subset_ball (by linarith) hz)).2
    have hbound : ∀ z ∈ ball y r, P z ≤ b := fun z hz =>
      (hεsub (ball_subset_ball (by linarith) hz)).1.le
    obtain ⟨b', hbb', hb'a⟩ := EReal.lt_iff_exists_real_btwn.mp hba
    rw [EReal.coe_lt_coe_iff] at hbb'
    set L : ℝ := Real.log (volume (ball y r)).toReal with hLdef
    have hlim : Tendsto (fun m : ℕ => b - (m : ℝ)⁻¹ * L) atTop (𝓝 b) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const L
      simpa using tendsto_const_nhds.sub this
    filter_upwards [hlim.eventually (gt_mem_nhds hbb'), eventually_ge_atTop 1] with m hm hm1
    exact (bergmanWeight_le hB hm1 hr hsub hbound).trans_lt
      ((EReal.coe_lt_coe_iff.mpr hm).trans hb'a)

/-- **Doubling the exponent** (Demailly's subadditivity, `BergmanSubadditivity`):
`φ_{2m}(y) ≤ (2m)⁻¹ log C + φ_m(y)`. -/
theorem bergmanWeight_two_mul_le (d : ℕ) : by
    letI : MeasurableSpace (ComplexModel d) := borel _
    letI : BorelSpace (ComplexModel d) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B → ∀ m : ℕ, 1 ≤ m → ∀ y ∈ B,
        bergmanWeight B P (2 * m) y ≤
          (((2 * (m : ℝ))⁻¹ * Real.log C : ℝ) : EReal) + bergmanWeight B P m y := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, hsub⟩ := bergmanSup_add_le d R hR
  refine ⟨C, hC, fun B hB hconv hbd P hP m hm y hy => ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h := hsub B hB hconv hbd P hP (m : ℝ) (m : ℝ) hmpos hmpos y hy
  have hcast : ((2 * m : ℕ) : ℝ) = (m : ℝ) + (m : ℝ) := by push_cast; ring
  set K₂ := bergmanSup B (fun z => multiplierWeight ((2 * m : ℕ) : ℝ) (P z)) y with hK₂def
  set K₁ := bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z)) y with hK₁def
  have hK : K₂ ≤ ENNReal.ofReal C * K₁ * K₁ := by
    rw [hK₂def, hcast]; exact h
  have hK₁top : K₁ ≠ ⊤ := bergmanSup_multiplierWeight_ne_top hB hP hmpos hy
  by_cases hK₂0 : K₂ = 0
  · simp only [bergmanWeight, bergmanLog, ← hK₂def, hK₂0, ENNReal.log_zero]
    rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (by positivity)))]
    exact bot_le
  · have hK₁0 : K₁ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hK
      exact hK₂0 (le_antisymm hK (by positivity))
    have hK₂top : K₂ ≠ ⊤ := ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK₁top) hK₁top) hK
    set k₂ : ℝ := K₂.toReal
    set k₁ : ℝ := K₁.toReal
    have hk₂ : 0 < k₂ := ENNReal.toReal_pos hK₂0 hK₂top
    have hk₁ : 0 < k₁ := ENNReal.toReal_pos hK₁0 hK₁top
    have hK₂k : K₂ = ENNReal.ofReal k₂ := (ENNReal.ofReal_toReal hK₂top).symm
    have hK₁k : K₁ = ENNReal.ofReal k₁ := (ENNReal.ofReal_toReal hK₁top).symm
    have hreal : k₂ ≤ C * k₁ * k₁ := by
      rw [hK₂k, hK₁k, ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at hK
      exact hK
    have hlog : Real.log k₂ ≤ Real.log C + 2 * Real.log k₁ := by
      have := Real.log_le_log hk₂ hreal
      rw [Real.log_mul (by positivity) hk₁.ne', Real.log_mul hC.ne' hk₁.ne'] at this
      linarith
    simp only [bergmanWeight, bergmanLog, ← hK₂def, ← hK₁def, hK₂k, hK₁k,
      ENNReal.log_ofReal_of_pos hk₂, ENNReal.log_ofReal_of_pos hk₁, ← EReal.coe_mul,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [h2m]
    have : (2 * (m : ℝ))⁻¹ * Real.log k₂ ≤ (2 * (m : ℝ))⁻¹ * (Real.log C + 2 * Real.log k₁) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    calc (2 * (m : ℝ))⁻¹ * Real.log k₂
        ≤ (2 * (m : ℝ))⁻¹ * (Real.log C + 2 * Real.log k₁) := this
      _ = (2 * (m : ℝ))⁻¹ * Real.log C + (m : ℝ)⁻¹ * Real.log k₁ := by field_simp

/-- **Demailly's decreasing approximation, local form.**  On a bounded open convex `B ⊆ ℂ^d`
there is `A ≥ 0` (depending only on `d` and the radius) such that for every `P` psh on `B` and
`y ∈ B`, the sequence `ψ_k(y) = φ_{2^k}(y) + A 2^{-k}` is nonincreasing in `k` and tends to
`P(y)`. -/
theorem antitone_tendsto_bergmanWeight_dyadic (d : ℕ) : by
    letI : MeasurableSpace (ComplexModel d) := borel _
    letI : BorelSpace (ComplexModel d) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ A : ℝ, 0 ≤ A ∧
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B → ∀ y ∈ B,
        Antitone (fun k : ℕ => bergmanWeight B P (2 ^ k) y + ((A * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal)) ∧
        Tendsto (fun k : ℕ => bergmanWeight B P (2 ^ k) y + ((A * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal))
          atTop (𝓝 (P y)) := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, hdouble⟩ := bergmanWeight_two_mul_le d R hR
  refine ⟨max (Real.log C) 0, le_max_right _ _, fun B hB hconv hbd P hP y hy => ⟨?_, ?_⟩⟩
  · refine antitone_nat_of_succ_le fun k => ?_
    set A : ℝ := max (Real.log C) 0 with hAdef
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h := hdouble B hB hconv hbd P hP (2 ^ k) hk1 y hy
    have hpow : (2 : ℕ) * 2 ^ k = 2 ^ (k + 1) := by ring
    rw [hpow] at h
    have hcastk : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    rw [hcastk] at h
    have hlogA : (2 * (2 : ℝ) ^ k)⁻¹ * Real.log C ≤ (2 * (2 : ℝ) ^ k)⁻¹ * A :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hsplit : A * ((2 : ℝ) ^ k)⁻¹ =
        (2 * (2 : ℝ) ^ k)⁻¹ * A + A * ((2 : ℝ) ^ (k + 1))⁻¹ := by
      rw [pow_succ]; field_simp; ring
    calc bergmanWeight B P (2 ^ (k + 1)) y + ((A * ((2 : ℝ) ^ (k + 1))⁻¹ : ℝ) : EReal)
        ≤ ((((2 * (2 : ℝ) ^ k)⁻¹ * Real.log C : ℝ) : EReal) + bergmanWeight B P (2 ^ k) y) +
            ((A * ((2 : ℝ) ^ (k + 1))⁻¹ : ℝ) : EReal) := by gcongr
      _ ≤ ((((2 * (2 : ℝ) ^ k)⁻¹ * A : ℝ) : EReal) + bergmanWeight B P (2 ^ k) y) +
            ((A * ((2 : ℝ) ^ (k + 1))⁻¹ : ℝ) : EReal) := by
          gcongr
      _ = bergmanWeight B P (2 ^ k) y + ((A * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal) := by
          rw [hsplit, EReal.coe_add, add_comm (((2 * (2 : ℝ) ^ k)⁻¹ * A : ℝ) : EReal),
            add_assoc]
  · have hφ : Tendsto (fun k : ℕ => bergmanWeight B P (2 ^ k) y) atTop (𝓝 (P y)) :=
      (tendsto_bergmanWeight d R hR B hB hconv hbd P hP y hy).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
    have hc : Tendsto (fun k : ℕ => ((max (Real.log C) 0 * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal))
        atTop (𝓝 ((0 : ℝ) : EReal)) := by
      refine (continuous_coe_real_ereal.tendsto _).comp ?_
      have := (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul
          (max (Real.log C) 0)
      simpa using this
    have hadd := (EReal.continuousAt_add (p := (P y, ((0 : ℝ) : EReal)))
      (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))).tendsto.comp
        (hφ.prodMk_nhds hc)
    have h0 : P y + ((0 : ℝ) : EReal) = P y := by rw [EReal.coe_zero, add_zero]
    rw [h0] at hadd
    exact hadd

end

end Hironaka.BergmanWeightConvergence
