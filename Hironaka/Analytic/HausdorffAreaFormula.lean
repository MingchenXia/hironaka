import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false

/-!
# The area formula for injective `C¹` maps into a larger inner product space

Let `E` be a finite-dimensional real inner product space of dimension `k` and `F` any real inner
product space.  For `f : E → F` of class `C¹` on an open set `U`, a measurable `s ⊆ U` on which
`f` is injective and whose points have injective differentials,

  `μHE[k] (f '' s) = ∫⁻ x in s, ‖Df(x)‖_det dλ`  (`euclideanHausdorffMeasure_image_eq_lintegral`),

where `μHE[k]` is Mathlib's `k`-dimensional Euclidean Hausdorff measure (normalised to agree with
Lebesgue measure on `k`-dimensional spaces) and `‖L‖_det = LinearMap.normDet L = √det(L*L)` is the
volume factor of a linear map.  Mathlib has this for linear maps
(`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`) and, when `F = E`, for
differentiable maps (`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image`).

## Proof

* `image_bounds`: if `‖f x - f y - A (x - y)‖ ≤ ε ‖A (x - y)‖` on `S` (with `ε < 1`), then
  `f '' S` is the image of `A '' S` under a `(1 + ε)`-Lipschitz map, and conversely with
  constant `(1 - ε)⁻¹`; the linear formula gives
  `μHE (f '' S) ≤ (1 + ε)ᵏ ‖A‖_det λ(S)` and `‖A‖_det λ(S) ≤ (1 - ε)⁻ᵏ μHE (f '' S)`.
* `exists_local_bounds`: near a point `x₀` with `Df(x₀)` injective, the mean value theorem gives
  that relative closeness on a small ball, and the same comparison applied to the linear maps
  `Df(x)` compares `‖Df(x)‖_det` with `‖Df(x₀)‖_det`.
* a countable cover of `s` by such balls, made disjoint, and countable additivity (the images are
  measurable by the Lusin--Souslin theorem and disjoint by injectivity) give
  `μHE (f '' s) ≤ c(ε) ∫ ‖Df‖_det` and `∫ ‖Df‖_det ≤ c(ε) μHE (f '' s)` with
  `c(ε) = ((1 + ε)/(1 - ε))ᵏ → 1`.

The measure form `restrict_euclideanHausdorffMeasure_image` and the integral forms
`lintegral_image_eq_lintegral` / `integral_image_eq_integral` follow by applying the set formula to
`s ∩ f⁻¹(B)`.
-/

open Set Filter MeasureTheory Measure Module Function
open scoped NNReal ENNReal Topology

noncomputable section

namespace Hironaka.HausdorffAreaFormula

section Lipschitz

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A `K`-Lipschitz map multiplies the `d`-dimensional Euclidean Hausdorff measure by at most
`Kᵈ`. -/
theorem euclideanHausdorffMeasure_image_le_of_lipschitzOnWith {g : X → Y} {T : Set X}
    {K : ℝ≥0} (h : LipschitzOnWith K g T) (d : ℕ) :
    μHE[d] (g '' T) ≤ (K : ℝ≥0∞) ^ d * μHE[d] T := by
  simp only [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply]
  have h' := h.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d)
  rw [ENNReal.rpow_natCast] at h'
  calc _ ≤ (volume.addHaarScalarFactor μH[(d : ℝ)] : ℝ≥0∞) * ((K : ℝ≥0∞) ^ d * μH[(d : ℝ)] T) :=
        by gcongr
    _ = _ := by ring

end Lipschitz

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The volume factor of a continuous linear map, as an extended nonnegative real. -/
def detFactor (A : E →L[ℝ] F) : ℝ≥0∞ := ENNReal.ofReal (A : E →ₗ[ℝ] F).normDet

theorem euclideanHausdorffMeasure_image_linear (A : E →L[ℝ] F) (S : Set E) :
    μHE[finrank ℝ E] (A '' S) = detFactor A * volume S :=
  (A : E →ₗ[ℝ] F).euclideanHausdorffMeasure_image_eq_normDet_mul_volume S

/-- **Upper comparison with a linear map.**  If `f` is relatively `ε`-close to `A` on `S`, then
`μHE (f '' S) ≤ (1 + ε)ᵏ ‖A‖_det λ(S)`. -/
theorem image_le_of_rel_close {A : E →L[ℝ] F} {ε : ℝ} (hε0 : 0 ≤ ε)
    {f : E → F} {S : Set E}
    (hf : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    μHE[finrank ℝ E] (f '' S) ≤
      (Real.toNNReal (1 + ε) : ℝ≥0∞) ^ finrank ℝ E * (detFactor A * volume S) := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  have : Nonempty E := ⟨hSne.some⟩
  -- `f` factors through `A` on `S`
  have hfac : ∀ x ∈ S, ∀ y ∈ S, A x = A y → f x = f y := by
    intro x hx y hy hxy
    have h := hf x hx y hy
    rw [map_sub, hxy, sub_self, norm_zero, mul_zero] at h
    have : f x - f y = 0 := by
      have h' : ‖f x - f y - 0‖ ≤ 0 := h
      rw [sub_zero] at h'
      exact norm_le_zero_iff.mp h'
    exact sub_eq_zero.mp this
  set Θ : F → F := fun z => f (invFunOn A S z) with hΘ
  have hΘA : ∀ x ∈ S, Θ (A x) = f x := by
    intro x hx
    have hex : ∃ a ∈ S, A a = A x := ⟨x, hx, rfl⟩
    exact hfac _ (invFunOn_mem hex) x hx (invFunOn_eq hex)
  have himg : f '' S = Θ '' (A '' S) := by
    rw [image_image]
    exact (image_congr fun x hx => (hΘA x hx).symm)
  have hlip : LipschitzOnWith (Real.toNNReal (1 + ε)) Θ (A '' S) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΘA x hx, hΘA y hy, dist_eq_norm, dist_eq_norm, ← map_sub,
      Real.coe_toNNReal _ (by linarith)]
    have h := hf x hx y hy
    calc ‖f x - f y‖ = ‖(f x - f y - A (x - y)) + A (x - y)‖ := by abel_nf
      _ ≤ ‖f x - f y - A (x - y)‖ + ‖A (x - y)‖ := norm_add_le _ _
      _ ≤ (1 + ε) * ‖A (x - y)‖ := by linarith
  rw [himg]
  calc μHE[finrank ℝ E] (Θ '' (A '' S))
      ≤ (Real.toNNReal (1 + ε) : ℝ≥0∞) ^ finrank ℝ E * μHE[finrank ℝ E] (A '' S) :=
        euclideanHausdorffMeasure_image_le_of_lipschitzOnWith hlip _
    _ = _ := by rw [euclideanHausdorffMeasure_image_linear]

/-- **Lower comparison with a linear map.**  If `f` is relatively `ε`-close to `A` on `S` with
`ε < 1`, then `‖A‖_det λ(S) ≤ (1 - ε)⁻ᵏ μHE (f '' S)`. -/
theorem le_image_of_rel_close {A : E →L[ℝ] F} {ε : ℝ} (hε1 : ε < 1)
    {f : E → F} {S : Set E}
    (hf : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    detFactor A * volume S ≤
      (Real.toNNReal (1 - ε)⁻¹ : ℝ≥0∞) ^ finrank ℝ E * μHE[finrank ℝ E] (f '' S) := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  have : Nonempty E := ⟨hSne.some⟩
  have hpos : 0 < 1 - ε := by linarith
  -- the basic two-sided estimate `(1 - ε) ‖A (x - y)‖ ≤ ‖f x - f y‖`
  have hlow : ∀ x ∈ S, ∀ y ∈ S, (1 - ε) * ‖A (x - y)‖ ≤ ‖f x - f y‖ := by
    intro x hx y hy
    have h := hf x hx y hy
    have : ‖A (x - y)‖ ≤ ‖f x - f y - A (x - y)‖ + ‖f x - f y‖ := by
      calc ‖A (x - y)‖ = ‖(f x - f y) - (f x - f y - A (x - y))‖ := by abel_nf
        _ ≤ ‖f x - f y‖ + ‖f x - f y - A (x - y)‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    nlinarith
  have hfac : ∀ x ∈ S, ∀ y ∈ S, f x = f y → A x = A y := by
    intro x hx y hy hxy
    have h := hlow x hx y hy
    rw [hxy, sub_self, norm_zero] at h
    have h0 : ‖A (x - y)‖ ≤ 0 := by
      by_contra hc
      have := mul_pos hpos (not_le.mp hc)
      linarith
    rw [map_sub] at h0
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  set Ψ : F → F := fun z => A (invFunOn f S z) with hΨ
  have hΨf : ∀ x ∈ S, Ψ (f x) = A x := by
    intro x hx
    have hex : ∃ a ∈ S, f a = f x := ⟨x, hx, rfl⟩
    exact hfac _ (invFunOn_mem hex) x hx (invFunOn_eq hex)
  have himg : (A : E → F) '' S = Ψ '' (f '' S) := by
    rw [image_image]
    exact (image_congr fun x hx => (hΨf x hx).symm)
  have hlip : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) Ψ (f '' S) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΨf x hx, hΨf y hy, dist_eq_norm, dist_eq_norm, ← map_sub,
      Real.coe_toNNReal _ (inv_nonneg.mpr hpos.le)]
    have h := hlow x hx y hy
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  rw [← euclideanHausdorffMeasure_image_linear, himg]
  exact euclideanHausdorffMeasure_image_le_of_lipschitzOnWith hlip _

end Linear

section Local

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The error factor `c(ε) = (1 + ε)ᵏ (1 - ε)⁻ᵏ` of the local comparisons. -/
def errorFactor (k : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  (Real.toNNReal (1 + ε) : ℝ≥0∞) ^ k * (Real.toNNReal (1 - ε)⁻¹ : ℝ≥0∞) ^ k

/-- A linear map relatively `ε`-close to `A` has a comparable volume factor. -/
theorem detFactor_bounds_of_rel_close {A L : E →L[ℝ] F} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hL : ∀ v, ‖L v - A v‖ ≤ ε * ‖A v‖) :
    detFactor L ≤ (Real.toNNReal (1 + ε) : ℝ≥0∞) ^ finrank ℝ E * detFactor A ∧
      detFactor A ≤ (Real.toNNReal (1 - ε)⁻¹ : ℝ≥0∞) ^ finrank ℝ E * detFactor L := by
  set B : Set E := Metric.ball 0 1
  have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume (0 : E) one_pos).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hclose : ∀ x ∈ B, ∀ y ∈ B, ‖L x - L y - A (x - y)‖ ≤ ε * ‖A (x - y)‖ := by
    intro x _ y _
    rw [← map_sub]
    exact hL (x - y)
  constructor
  · have h := image_le_of_rel_close hε0 hclose
    rw [euclideanHausdorffMeasure_image_linear, ← mul_assoc] at h
    exact (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp h
  · have h := le_image_of_rel_close hε1 hclose
    rw [euclideanHausdorffMeasure_image_linear, ← mul_assoc] at h
    exact (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp h

/-- **Local comparison.**  Near a point where the differential of a `C¹` map is injective, the
image measure of every subset of a small ball, and the volume factor of the differential, are
within the factors `(1 + ε)ᵏ` and `(1 - ε)⁻ᵏ` of the linear model at the centre. -/
theorem exists_local_bounds {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hinj : Injective (fderiv ℝ f x₀)) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ r > 0, Metric.ball x₀ r ⊆ U ∧
      (∀ S ⊆ Metric.ball x₀ r,
        μHE[finrank ℝ E] (f '' S) ≤
            (Real.toNNReal (1 + ε) : ℝ≥0∞) ^ finrank ℝ E *
              (detFactor (fderiv ℝ f x₀) * volume S) ∧
          detFactor (fderiv ℝ f x₀) * volume S ≤
            (Real.toNNReal (1 - ε)⁻¹ : ℝ≥0∞) ^ finrank ℝ E * μHE[finrank ℝ E] (f '' S)) ∧
      (∀ x ∈ Metric.ball x₀ r,
        detFactor (fderiv ℝ f x) ≤
            (Real.toNNReal (1 + ε) : ℝ≥0∞) ^ finrank ℝ E * detFactor (fderiv ℝ f x₀) ∧
          detFactor (fderiv ℝ f x₀) ≤
            (Real.toNNReal (1 - ε)⁻¹ : ℝ≥0∞) ^ finrank ℝ E * detFactor (fderiv ℝ f x)) := by
  set A := fderiv ℝ f x₀ with hA
  obtain ⟨K, hKpos, hK⟩ := ((A : E →ₗ[ℝ] F).injective_iff_antilipschitz).mp hinj
  have hKA : ∀ v, ‖v‖ ≤ (K : ℝ) * ‖A v‖ := by
    intro v
    have := hK.le_mul_dist v 0
    simpa [dist_eq_norm] using this
  have hKr : (0 : ℝ) < K := hKpos
  set δ : ℝ := ε / K with hδ
  have hδpos : 0 < δ := div_pos hε0 hKr
  -- relative closeness from absolute closeness
  have hrel : ∀ v, δ * ‖v‖ ≤ ε * ‖A v‖ := by
    intro v
    have := hKA v
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hKr]
    nlinarith
  -- continuity of the differential at `x₀`
  have hcont : ContinuousAt (fderiv ℝ f) x₀ :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx₀)
  obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  obtain ⟨r₂, hr₂, hr₂d⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (Metric.ball_mem_nhds A hδpos))
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (Metric.ball_subset_ball (min_le_left _ _)).trans hr₁U,
    ?_, ?_⟩
  · intro S hS
    have hball : Metric.ball x₀ (min r₁ r₂) ⊆ U :=
      (Metric.ball_subset_ball (min_le_left _ _)).trans hr₁U
    have hderiv : ∀ x ∈ Metric.ball x₀ (min r₁ r₂),
        HasFDerivWithinAt f (fderiv ℝ f x) (Metric.ball x₀ (min r₁ r₂)) x := by
      intro x hx
      exact ((hf.differentiableOn one_ne_zero).differentiableAt
        (hU.mem_nhds (hball hx))).hasFDerivAt.hasFDerivWithinAt
    have hbound : ∀ x ∈ Metric.ball x₀ (min r₁ r₂), ‖fderiv ℝ f x - A‖ ≤ δ := by
      intro x hx
      have hx2 : dist x x₀ < r₂ := lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
      have := hr₂d hx2
      rw [dist_eq_norm] at this
      exact this.le
    have hclose : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖ := by
      intro x hx y hy
      have h := (convex_ball x₀ (min r₁ r₂)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        hderiv hbound (hS hy) (hS hx)
      exact h.trans (hrel _)
    exact ⟨image_le_of_rel_close hε0.le hclose, le_image_of_rel_close hε1 hclose⟩
  · intro x hx
    have hx2 : dist x x₀ < r₂ := lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
    have hxA : ‖fderiv ℝ f x - A‖ < δ := by
      have := hr₂d hx2
      rwa [dist_eq_norm] at this
    refine detFactor_bounds_of_rel_close hε0.le hε1 fun v => ?_
    calc ‖fderiv ℝ f x v - A v‖ = ‖(fderiv ℝ f x - A) v‖ := rfl
      _ ≤ ‖fderiv ℝ f x - A‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * ‖v‖ := by gcongr
      _ ≤ ε * ‖A v‖ := hrel v

end Local

section Global

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Both inequalities up to the error factor.** -/
theorem image_le_and_le_image {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {s : Set E} (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hdinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    μHE[finrank ℝ E] (f '' s) ≤
        errorFactor (finrank ℝ E) ε * ∫⁻ x in s, detFactor (fderiv ℝ f x) ∧
      ∫⁻ x in s, detFactor (fderiv ℝ f x) ≤
        errorFactor (finrank ℝ E) ε * μHE[finrank ℝ E] (f '' s) := by
  set k := finrank ℝ E
  set c₁ : ℝ≥0∞ := (Real.toNNReal (1 + ε) : ℝ≥0∞) ^ k
  set c₂ : ℝ≥0∞ := (Real.toNNReal (1 - ε)⁻¹ : ℝ≥0∞) ^ k
  have hc₁ : c₁ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hc₂ : c₂ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  -- local radii
  have hloc : ∀ x, ∃ r : ℝ, 0 < r ∧ (x ∈ s → Metric.ball x r ⊆ U ∧
      (∀ S ⊆ Metric.ball x r,
        μHE[k] (f '' S) ≤ c₁ * (detFactor (fderiv ℝ f x) * volume S) ∧
          detFactor (fderiv ℝ f x) * volume S ≤ c₂ * μHE[k] (f '' S)) ∧
      (∀ y ∈ Metric.ball x r,
        detFactor (fderiv ℝ f y) ≤ c₁ * detFactor (fderiv ℝ f x) ∧
          detFactor (fderiv ℝ f x) ≤ c₂ * detFactor (fderiv ℝ f y))) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨r, hr, h1, h2, h3⟩ := exists_local_bounds hU hf (hsU hx) (hdinj x hx) hε0 hε1
      exact ⟨r, hr, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, one_pos, fun h => (hx h).elim⟩
  choose r hr hrs using hloc
  obtain ⟨t, hts, htc, hst⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => Metric.ball x (r x)) (s := s)
    (fun x _ => mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hr x)))
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hsne
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp (hst hx)
    exact ⟨y, hy⟩
  obtain ⟨c, rfl⟩ := htc.exists_eq_range htne
  set B : ℕ → Set E := fun j => Metric.ball (c j) (r (c j))
  set Q : ℕ → Set E := fun j => s ∩ disjointed B j
  have hcs : ∀ j, c j ∈ s := fun j => hts (mem_range_self j)
  have hQB : ∀ j, Q j ⊆ B j := fun j => inter_subset_right.trans (disjointed_subset B j)
  have hQs : ∀ j, Q j ⊆ s := fun j => inter_subset_left
  have hQm : ∀ j, MeasurableSet (Q j) := fun j =>
    hs.inter (MeasurableSet.disjointed (fun i => measurableSet_ball) j)
  have hQd : Pairwise (Disjoint on Q) := fun i j hij =>
    ((disjoint_disjointed B hij).mono inter_subset_right inter_subset_right)
  have hsQ : s = ⋃ j, Q j := by
    apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ ⋃ j, B j := by
        obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hst hx)
        obtain ⟨j, rfl⟩ := hy
        exact mem_iUnion.mpr ⟨j, hxy⟩
      rw [← iUnion_disjointed] at hx'
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
      exact mem_iUnion.mpr ⟨j, hx, hj⟩
    · exact iUnion_subset hQs
  -- images
  have hcont : ContinuousOn f s := (hf.continuousOn).mono hsU
  have hfQm : ∀ j, MeasurableSet (f '' Q j) := fun j =>
    (hQm j).image_of_continuousOn_injOn (hcont.mono (hQs j)) (hinj.mono (hQs j))
  have hfQd : Pairwise (Disjoint on fun j => f '' Q j) := fun i j hij =>
    Disjoint.image (hQd hij) hinj (hQs i) (hQs j)
  have himg : μHE[k] (f '' s) = ∑' j, μHE[k] (f '' Q j) := by
    conv_lhs => rw [hsQ, image_iUnion]
    exact measure_iUnion hfQd hfQm
  have hint : ∫⁻ x in s, detFactor (fderiv ℝ f x) =
      ∑' j, ∫⁻ x in Q j, detFactor (fderiv ℝ f x) := by
    conv_lhs => rw [hsQ]
    exact lintegral_iUnion hQm hQd _
  -- piecewise bounds
  have hpiece : ∀ j, μHE[k] (f '' Q j) ≤
      errorFactor k ε * ∫⁻ x in Q j, detFactor (fderiv ℝ f x) ∧
      ∫⁻ x in Q j, detFactor (fderiv ℝ f x) ≤ errorFactor k ε * μHE[k] (f '' Q j) := by
    intro j
    obtain ⟨-, himgb, hdetb⟩ := hrs (c j) (hcs j)
    obtain ⟨hup, hlow⟩ := himgb (Q j) (hQB j)
    set D₀ := detFactor (fderiv ℝ f (c j))
    have hconst : D₀ * volume (Q j) = ∫⁻ _ in Q j, D₀ := (setLIntegral_const _ _).symm
    constructor
    · calc μHE[k] (f '' Q j) ≤ c₁ * (D₀ * volume (Q j)) := hup
        _ = c₁ * ∫⁻ _ in Q j, D₀ := by rw [hconst]
        _ ≤ c₁ * ∫⁻ x in Q j, c₂ * detFactor (fderiv ℝ f x) := by
          exact mul_le_mul_right (setLIntegral_mono' (hQm j) fun x hx =>
            (hdetb x (hQB j hx)).2) _
        _ = c₁ * (c₂ * ∫⁻ x in Q j, detFactor (fderiv ℝ f x)) := by
          rw [lintegral_const_mul' _ _ hc₂]
        _ = errorFactor k ε * ∫⁻ x in Q j, detFactor (fderiv ℝ f x) := by
          rw [errorFactor, mul_assoc]
    · calc ∫⁻ x in Q j, detFactor (fderiv ℝ f x) ≤ ∫⁻ _ in Q j, c₁ * D₀ :=
            setLIntegral_mono' (hQm j) fun x hx => (hdetb x (hQB j hx)).1
        _ = c₁ * (D₀ * volume (Q j)) := by rw [setLIntegral_const, mul_assoc]
        _ ≤ c₁ * (c₂ * μHE[k] (f '' Q j)) := by gcongr
        _ = errorFactor k ε * μHE[k] (f '' Q j) := by rw [errorFactor, mul_assoc]
  constructor
  · rw [himg, hint, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => (hpiece j).1
  · rw [himg, hint, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => (hpiece j).2

theorem tendsto_errorFactor (k : ℕ) :
    Tendsto (fun j : ℕ => errorFactor k (1 / ((j : ℝ) + 2))) atTop (𝓝 1) := by
  have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun j => ?_
    simp only [comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hc : ContinuousAt (fun ε : ℝ =>
      (Real.toNNReal (1 + ε)) ^ k * (Real.toNNReal (1 - ε)⁻¹) ^ k) 0 := by
    have h1 : ContinuousAt (fun ε : ℝ => (1 - ε)⁻¹) 0 :=
      (continuousAt_const.sub continuousAt_id).inv₀ (by norm_num)
    exact ((continuous_real_toNNReal.continuousAt.comp
      (continuousAt_const.add continuousAt_id)).pow k).mul
      ((continuous_real_toNNReal.continuousAt.comp h1).pow k)
  have h := (hc.tendsto.comp h0)
  simp only [add_zero, sub_zero, inv_one, Real.toNNReal_one, one_pow, mul_one] at h
  have h' := ENNReal.tendsto_coe.mpr h
  refine h'.congr fun j => ?_
  simp [errorFactor, comp_apply, ENNReal.coe_mul, ENNReal.coe_pow]

/-- **The area formula.**  For `f` of class `C¹` on an open `U ⊇ s`, injective on the measurable
set `s`, with injective differentials on `s`, the `k`-dimensional Euclidean Hausdorff measure of
`f '' s` is the integral over `s` of the volume factor of `Df`. -/
theorem euclideanHausdorffMeasure_image_eq_lintegral {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {s : Set E} (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hdinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) :
    μHE[finrank ℝ E] (f '' s) = ∫⁻ x in s, detFactor (fderiv ℝ f x) := by
  have hε0 : ∀ j : ℕ, 0 < 1 / ((j : ℝ) + 2) := fun j => by positivity
  have hε1 : ∀ j : ℕ, 1 / ((j : ℝ) + 2) < 1 := fun j => by
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hb := fun j => image_le_and_le_image hU hf hs hsU hinj hdinj (hε0 j) (hε1 j)
  have ht := tendsto_errorFactor (finrank ℝ E)
  apply le_antisymm
  · have := ENNReal.Tendsto.mul_const ht (a := 1)
      (b := ∫⁻ x in s, detFactor (fderiv ℝ f x)) (Or.inl one_ne_zero)
    rw [one_mul] at this
    exact ge_of_tendsto' this fun j => (hb j).1
  · have := ENNReal.Tendsto.mul_const ht (a := 1) (b := μHE[finrank ℝ E] (f '' s))
      (Or.inl one_ne_zero)
    rw [one_mul] at this
    exact ge_of_tendsto' this fun j => (hb j).2

end Global

section MeasureForm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F]
  [BorelSpace F]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The volume factor is a continuous function of the linear map. -/
theorem continuous_normDet :
    Continuous fun L : E →L[ℝ] F => (L : E →ₗ[ℝ] F).normDet := by
  have heq : (fun L : E →L[ℝ] F => (L : E →ₗ[ℝ] F).normDet) =
      fun L => Real.sqrt ((ContinuousLinearMap.adjoint L).comp L).det := by
    funext L
    have h := ContinuousLinearMap.normDet_sq (𝕜 := ℝ) L
    simp only [RCLike.ofReal_real_eq_id, id] at h
    rw [← h, Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  rw [heq]
  exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous.clm_comp
      continuous_id))

omit [MeasurableSpace F] [BorelSpace F] in
theorem measurable_detFactor_fderiv (f : E → F) :
    Measurable fun x => detFactor (fderiv ℝ f x) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_normDet (E := E) (F := F)).measurable.comp (measurable_fderiv ℝ f))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem measurableSet_inter_preimage_of_continuousOn {f : E → F} {s : Set E}
    (hs : MeasurableSet s) (hf : ContinuousOn f s) {B : Set F} (hB : MeasurableSet B) :
    MeasurableSet (f ⁻¹' B ∩ s) := by
  classical
  rcases isEmpty_or_nonempty F with hF | hF
  · have : s = ∅ := by
      ext x
      exact iff_of_false (fun _ => hF.elim (f x)) (notMem_empty x)
    simp [this]
  obtain ⟨y₀⟩ := hF
  have hmeas : Measurable (s.piecewise f fun _ => y₀) :=
    hf.measurable_piecewise continuousOn_const hs
  have : f ⁻¹' B ∩ s = (s.piecewise f fun _ => y₀) ⁻¹' B ∩ s := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [piecewise_eq_of_mem _ _ _ h2], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [piecewise_eq_of_mem _ _ _ h2] at h1, h2⟩
  rw [this]
  exact (hmeas hB).inter hs

omit [CompleteSpace F] in
/-- **The area formula, measure form.**  The Euclidean Hausdorff measure on `f '' s` is the
push-forward of `‖Df‖_det λ` on `s`. -/
theorem restrict_euclideanHausdorffMeasure_image {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {s : Set E} (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hdinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) :
    (μHE[finrank ℝ E] : Measure F).restrict (f '' s) =
      Measure.map f ((volume.restrict s).withDensity fun x => detFactor (fderiv ℝ f x)) := by
  have hcont : ContinuousOn f s := hf.continuousOn.mono hsU
  have hfm : AEMeasurable f ((volume.restrict s).withDensity fun x => detFactor (fderiv ℝ f x)) :=
    (hcont.aemeasurable hs).mono_ac (withDensity_absolutelyContinuous _ _)
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply_of_aemeasurable hfm hB, withDensity_apply',
    Measure.restrict_restrict' hs]
  have hsB := measurableSet_inter_preimage_of_continuousOn hs hcont hB
  have himg : B ∩ f '' s = f '' (f ⁻¹' B ∩ s) := by
    ext y
    constructor
    · rintro ⟨hyB, x, hx, rfl⟩
      exact ⟨x, ⟨hyB, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hxB, hx⟩, rfl⟩
      exact ⟨hxB, x, hx, rfl⟩
  rw [himg]
  exact euclideanHausdorffMeasure_image_eq_lintegral hU hf hsB (inter_subset_right.trans hsU)
    (hinj.mono inter_subset_right) fun x hx => hdinj x hx.2

/-- **The area formula for nonnegative functions.** -/
theorem lintegral_image_eq_lintegral {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {s : Set E} (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hdinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) {φ : F → ℝ≥0∞}
    (hφ : Measurable φ) :
    ∫⁻ y in f '' s, φ y ∂(μHE[finrank ℝ E] : Measure F) =
      ∫⁻ x in s, detFactor (fderiv ℝ f x) * φ (f x) := by
  have hcont : ContinuousOn f s := hf.continuousOn.mono hsU
  have hfm : AEMeasurable f ((volume.restrict s).withDensity fun x => detFactor (fderiv ℝ f x)) :=
    (hcont.aemeasurable hs).mono_ac (withDensity_absolutelyContinuous _ _)
  rw [restrict_euclideanHausdorffMeasure_image hU hf hs hsU hinj hdinj,
    lintegral_map' hφ.aemeasurable hfm]
  exact lintegral_withDensity_eq_lintegral_mul₀ (measurable_detFactor_fderiv f).aemeasurable
      (hφ.comp_aemeasurable (hcont.aemeasurable hs))

/-- **The area formula for real functions.** -/
theorem integral_image_eq_integral {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {s : Set E} (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hdinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) {φ : F → ℝ}
    (hφ : AEStronglyMeasurable φ ((μHE[finrank ℝ E] : Measure F).restrict (f '' s))) :
    ∫ y in f '' s, φ y ∂(μHE[finrank ℝ E] : Measure F) =
      ∫ x in s, (fderiv ℝ f x : E →ₗ[ℝ] F).normDet * φ (f x) := by
  have hcont : ContinuousOn f s := hf.continuousOn.mono hsU
  have hfm : AEMeasurable f ((volume.restrict s).withDensity fun x => detFactor (fderiv ℝ f x)) :=
    (hcont.aemeasurable hs).mono_ac (withDensity_absolutelyContinuous _ _)
  rw [restrict_euclideanHausdorffMeasure_image hU hf hs hsU hinj hdinj] at hφ ⊢
  rw [integral_map hfm hφ, integral_withDensity_eq_integral_toReal_smul
    (measurable_detFactor_fderiv f) (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [detFactor, smul_eq_mul, ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)]

end MeasureForm

end Hironaka.HausdorffAreaFormula
