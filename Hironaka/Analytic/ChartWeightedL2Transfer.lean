import Hironaka.Analytic.PotentialTheory.MultiplierIdealsBasic
import Hironaka.Analytic.ERealChordUSC
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.HolomorphicMaps
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

/-!
# Weighted `L²` norms under a change of holomorphic coordinates

A weighted integral `∫ |f|² e^{-cφ}` is attached to a coordinate chart, because the
Lebesgue measure is.  Demailly's regularization compares such integrals across the balls
of a fixed finite cover of a compact manifold, whose charts are not the preferred charts
of the points involved, so the comparison has to be made explicit.  On a compact piece of
a chart overlap the real Jacobian of the transition map is bounded, and the comparison
costs only a constant.

`lintegral_image_le_of_abs_det_le` is the change-of-variables estimate
(`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` plus a bound on the
Jacobian), `exists_bound_abs_det_fderiv` produces the bound on a compact set from `C¹`
regularity, and `weightedL2_image_le` is the form used downstream: transporting the
weight along the map leaves the integrand unchanged, so only the Jacobian constant
appears.

The multiplier ideal `Hironaka.HolomorphicIdealSheaves.multiplierIdeal` tests weighted
integrability in the *preferred* chart `complexChartAt x` only;
`multiplierIntegrableAt_comp_of_holomorphic` and its chart corollary say that this is no
loss, since the predicate is invariant under a biholomorphic change of coordinates.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff

namespace Hironaka.ChartWeightedL2



noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Change of variables with a Jacobian bound.**  If `|det Df| ≤ C` on `s`, integrating a
nonnegative function over `f '' s` costs at most `C` times the integral of its pullback. -/
theorem lintegral_image_le_of_abs_det_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hinj : InjOn f s)
    {C : ℝ} (hC : ∀ x ∈ s, |(f' x).det| ≤ C) (g : E → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ ≤ ENNReal.ofReal C * ∫⁻ x in s, g (f x) ∂μ := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hf' hinj g,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hs fun x hx => ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hC x hx)) le_rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The real Jacobian of a `C¹` map is bounded on every compact subset of its domain. -/
theorem exists_bound_abs_det_fderiv {U K : Set E} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : E → E} (hf : ContDiffOn ℝ 1 f U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |(fderiv ℝ f x).det| ≤ C := by
  have hfd : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hcont : ContinuousOn (fun x => |(fderiv ℝ f x).det|) U :=
    (ContinuousLinearMap.continuous_det.continuousOn.comp hfd (mapsTo_univ _ _)).abs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x hx
  rw [Real.norm_eq_abs, abs_abs] at this
  exact this.trans (le_max_left _ _)

/-- **Weighted `L²` comparison along a change of coordinates.**  If the weight `ψ` pulls
back to `φ` along `f`, the weighted density of `F` pulls back to that of `F ∘ f`, so the
comparison of the two weighted integrals costs only the Jacobian constant. -/
theorem weightedL2_image_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hinj : InjOn f s)
    {C : ℝ} (hC : ∀ x ∈ s, |(f' x).det| ≤ C)
    {φ ψ : E → EReal} {c : ℝ} (hweight : ∀ x ∈ s, ψ (f x) = φ x) (F : E → ℂ) :
    ∫⁻ w in f '' s, multiplierDensity ψ c F w ∂μ ≤
      ENNReal.ofReal C * ∫⁻ x in s, multiplierDensity φ c (fun z => F (f z)) x ∂μ := by
  have hpull : ∫⁻ x in s, multiplierDensity ψ c F (f x) ∂μ =
      ∫⁻ x in s, multiplierDensity φ c (fun z => F (f z)) x ∂μ := by
    refine setLIntegral_congr_fun hs fun x hx => ?_
    simp [multiplierDensity, hweight x hx]
  refine (lintegral_image_le_of_abs_det_le μ hs hf' hinj hC
    (multiplierDensity ψ c F)).trans ?_
  rw [hpull]

end

section Local

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  {μ : Measure (ComplexModel n)} [μ.IsAddHaarMeasure]

/-- An upper semicontinuous extended-real function on an open set is a.e.-measurable for
every measure restricted to that set: extend it by `⊤` outside. -/
theorem aemeasurable_restrict_of_upperSemicontinuousOn {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X} {u : X → EReal} {U : Set X}
    (hu : UpperSemicontinuousOn u U) (hU : IsOpen U) : AEMeasurable u (ν.restrict U) := by
  classical
  let v : X → EReal := fun y => if y ∈ U then u y else ⊤
  have hv : UpperSemicontinuous v := by
    intro y a hya
    by_cases hy : y ∈ U
    · have hua : u y < a := by simpa [v, hy] using hya
      have hlocal := hu y hy a hua
      rw [hU.nhdsWithin_eq hy] at hlocal
      filter_upwards [hlocal, hU.mem_nhds hy] with z hz hzU
      simpa [v, hzU] using hz
    · simp [v, hy] at hya
  refine hv.measurable.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
  simp [v, hy]

/-- **Local weighted integrability is a biholomorphic invariant.**  The data `(τ, σ)` is a
biholomorphic pair between the open sets `A` and `B`, and the weight `ψ` on `B` pulls back
to `φ` on `A`.  Then weighted integrability of `F` at `τ x` gives weighted integrability of
`F ∘ τ` at `x`.  This is what makes the preferred-chart definition of
`Hironaka.HolomorphicIdealSheaves.multiplierIdeal` harmless. -/
theorem multiplierIntegrableAt_comp {φ ψ : ComplexModel n → EReal} {c : ℝ}
    {F : ComplexModel n → ℂ} {τ σ : ComplexModel n → ComplexModel n}
    {A B : Set (ComplexModel n)} (hA : IsOpen A) (hB : IsOpen B)
    (hτ : DifferentiableOn ℂ τ A) (hσ : ContDiffOn ℝ 1 σ B)
    (hτA : MapsTo τ A B) (hσB : MapsTo σ B A)
    (hστ : ∀ z ∈ A, σ (τ z) = z) (hτσ : ∀ w ∈ B, τ (σ w) = w)
    (hweight : ∀ z ∈ A, ψ (τ z) = φ z)
    (hφ : UpperSemicontinuousOn φ A) (hc : c ≠ 0)
    {x : ComplexModel n} (hx : x ∈ A)
    (h : MultiplierIntegrableAt ψ c F (τ x) μ) :
    MultiplierIntegrableAt φ c (fun z => F (τ z)) x μ := by
  classical
  obtain ⟨hcpos, U, hU, hxU, hFhol, hFmeas, hFint⟩ := h
  -- the source neighbourhood of `x`
  have hVopen : IsOpen (A ∩ τ ⁻¹' U) := hτ.continuousOn.isOpen_inter_preimage hA hU
  have hxV : x ∈ A ∩ τ ⁻¹' U := ⟨hx, hxU⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVopen x hxV
  set W : Set (ComplexModel n) := ball x r with hW
  set Kc : Set (ComplexModel n) := closedBall x (r / 2) with hKc
  set W' : Set (ComplexModel n) := ball x (r / 2) with hW'
  have hW'W : W' ⊆ W := ball_subset_ball (by linarith)
  have hKcW : Kc ⊆ W := closedBall_subset_ball (by linarith)
  have hWA : W ⊆ A := fun z hz => (hrV hz).1
  have hWU : ∀ z ∈ W, τ z ∈ U := fun z hz => (hrV hz).2
  -- `τ` restricted to the source is a homeomorphism onto its image
  have himage : ∀ {S : Set (ComplexModel n)}, S ⊆ A → τ '' S = B ∩ σ ⁻¹' S := by
    intro S hSA
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hτA (hSA hz), by simpa [hστ z (hSA hz)] using hz⟩
    · rintro ⟨hwB, hw⟩
      exact ⟨σ w, hw, hτσ w hwB⟩
  have hτW'open : IsOpen (τ '' W') := by
    rw [himage (hW'W.trans hWA)]
    exact hσ.continuousOn.isOpen_inter_preimage hB isOpen_ball
  have hτKc : IsCompact (τ '' Kc) :=
    (isCompact_closedBall x (r / 2)).image_of_continuousOn (hτ.continuousOn.mono (hKcW.trans hWA))
  have hτKcB : τ '' Kc ⊆ B := by
    rintro w ⟨z, hz, rfl⟩; exact hτA (hWA (hKcW hz))
  -- the Jacobian of the inverse is bounded on that compact image
  obtain ⟨C, hC0, hCbound⟩ := exists_bound_abs_det_fderiv hB hτKc hτKcB hσ
  have hsub : τ '' W' ⊆ τ '' Kc := image_mono (ball_subset_closedBall)
  -- change of variables: `σ` maps `τ '' W'` back to `W'`
  have hσimage : σ '' (τ '' W') = W' := by
    rw [image_image]
    exact image_congr (fun z hz => hστ z (hW'W.trans hWA <| hz)) ▸ image_id W'
  have hderiv : ∀ w ∈ τ '' W', HasFDerivWithinAt σ (fderiv ℝ σ w) (τ '' W') w := by
    intro w hw
    have hwB : w ∈ B := hτKcB (hsub hw)
    exact ((hσ.differentiableOn one_ne_zero w hwB).differentiableAt
      (hB.mem_nhds hwB)).hasFDerivAt.hasFDerivWithinAt
  have hinjσ : InjOn σ (τ '' W') := by
    intro w hw w' hw' hww
    have hwB : w ∈ B := hτKcB (hsub hw)
    have hw'B : w' ∈ B := hτKcB (hsub hw')
    rw [← hτσ w hwB, ← hτσ w' hw'B, hww]
  have hkey := weightedL2_image_le (E := ComplexModel n) μ
    hτW'open.measurableSet hderiv hinjσ
    (fun w hw => hCbound w (hsub hw)) (φ := ψ) (ψ := φ) (c := c)
    (fun w hw => by
      have hwB : w ∈ B := hτKcB (hsub hw)
      have := hweight (σ w) (hσB hwB)
      rw [hτσ w hwB] at this
      exact this.symm) (fun z => F (τ z))
  rw [hσimage] at hkey
  -- the right-hand side is the original weighted integral over `τ '' W' ⊆ U`
  have hRHS : ∫⁻ w in τ '' W', multiplierDensity ψ c (fun z => F (τ (σ z))) w ∂μ ≤
      ∫⁻ w in U, multiplierDensity ψ c F w ∂μ := by
    refine (setLIntegral_congr_fun hτW'open.measurableSet ?_).le.trans
      (lintegral_mono_set ?_)
    · intro w hw
      have hwB : w ∈ B := hτKcB (hsub hw)
      simp [multiplierDensity, hτσ w hwB]
    · rintro w ⟨z, hz, rfl⟩
      exact hWU _ (hW'W hz)
  refine ⟨hcpos, W', isOpen_ball, mem_ball_self (by linarith), ?_, ?_, ?_⟩
  · exact hFhol.comp (hτ.mono (hW'W.trans hWA)) fun z hz => hWU _ (hW'W hz)
  · -- measurability of the transported density
    have hφmeas : AEMeasurable φ (μ.restrict W') :=
      aemeasurable_restrict_of_upperSemicontinuousOn (hφ.mono (hW'W.trans hWA)) isOpen_ball
    have hweightmeas : AEMeasurable (fun y => multiplierWeight c (φ y))
        (μ.restrict W') := by
      have hcmul : AEMeasurable (fun y => (c : EReal) * φ y) (μ.restrict W') :=
        (continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hφmeas
      have hneg : AEMeasurable (fun y => -((c : EReal) * φ y)) (μ.restrict W') :=
        continuous_neg.measurable.comp_aemeasurable' hcmul
      simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg
    have hFcont : ContinuousOn (fun z => ENNReal.ofReal (‖F (τ z)‖ ^ 2)) W' := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine (continuous_norm.comp_continuousOn ?_).pow 2
      exact hFhol.continuousOn.comp (hτ.continuousOn.mono (hW'W.trans hWA))
        fun z hz => hWU _ (hW'W hz)
    exact (hFcont.aemeasurable isOpen_ball.measurableSet).mul hweightmeas
  · calc ∫⁻ z in W', multiplierDensity φ c (fun z => F (τ z)) z ∂μ
        ≤ ENNReal.ofReal C * ∫⁻ w in U, multiplierDensity ψ c F w ∂μ := by
          refine hkey.trans ?_
          exact mul_le_mul' le_rfl hRHS
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hFint

end Local


section Chart

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  {μ : Measure (ComplexModel n)} [μ.IsAddHaarMeasure]

/-- The overlap of two charts, read in the coordinates of the first one. -/
def overlapDomain (e f : ComplexChart n M) : Set (ComplexModel n) :=
  {z | z ∈ e.val.target ∧ e.val.symm z ∈ f.val.source}

omit [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
theorem isOpen_overlapDomain (e f : ComplexChart n M) : IsOpen (overlapDomain e f) := by
  have : overlapDomain e f = e.val.target ∩ e.val.symm ⁻¹' f.val.source := rfl
  rw [this]
  exact e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target f.val.open_source

omit [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
theorem mem_overlapDomain {e f : ComplexChart n M} {x : M} (hex : x ∈ e.val.source)
    (hfx : x ∈ f.val.source) : e.val x ∈ overlapDomain e f :=
  ⟨e.val.map_source hex, by rw [e.val.left_inv hex]; exact hfx⟩

/-- **Chart independence of local weighted integrability.**  If the weighted integral of
`g` against `e^{-c·u}` converges near `x` in the coordinates of one chart, it converges in
the coordinates of any other chart containing `x`.  In particular the preferred-chart
convention of `Hironaka.HolomorphicIdealSheaves.multiplierIdeal` costs nothing. -/
theorem multiplierIntegrableAt_chart {u : M → EReal} {c : ℝ} {g : M → ℂ}
    (e f : ComplexChart n M) {x : M} (hex : x ∈ e.val.source) (hfx : x ∈ f.val.source)
    (hu : UpperSemicontinuousOn (chartFunction u e) (overlapDomain e f)) (hc : c ≠ 0)
    (h : MultiplierIntegrableAt (chartFunction u f) c
      (fun z => g (f.val.symm z)) (f.val x) μ) :
    MultiplierIntegrableAt (chartFunction u e) c (fun z => g (e.val.symm z)) (e.val x) μ := by
  set A := overlapDomain e f with hA
  set B := overlapDomain f e with hB
  set τ : ComplexModel n → ComplexModel n := fun z => f.val (e.val.symm z) with hτdef
  set σ : ComplexModel n → ComplexModel n := fun w => e.val (f.val.symm w) with hσdef
  have hAsub : ∀ z ∈ A, e.val.symm z ∈ f.val.source := fun z hz => hz.2
  have hBsub : ∀ w ∈ B, f.val.symm w ∈ e.val.source := fun w hw => hw.2
  have hτA : MapsTo τ A B := by
    intro z hz
    refine ⟨f.val.map_source (hAsub z hz), ?_⟩
    rw [f.val.left_inv (hAsub z hz)]
    exact e.val.map_target hz.1
  have hσB : MapsTo σ B A := by
    intro w hw
    refine ⟨e.val.map_source (hBsub w hw), ?_⟩
    rw [e.val.left_inv (hBsub w hw)]
    exact f.val.map_target hw.1
  have hστ : ∀ z ∈ A, σ (τ z) = z := by
    intro z hz
    simp only [hσdef, hτdef, f.val.left_inv (hAsub z hz), e.val.right_inv hz.1]
  have hτσ : ∀ w ∈ B, τ (σ w) = w := by
    intro w hw
    simp only [hσdef, hτdef, e.val.left_inv (hBsub w hw), f.val.right_inv hw.1]
  have hweight : ∀ z ∈ A, chartFunction u f (τ z) = chartFunction u e z := by
    intro z hz
    simp only [chartFunction, hτdef, f.val.left_inv (hAsub z hz)]
  -- holomorphy of the two transition maps on their domains
  have htrans : ∀ (d d' : ComplexChart n M), ∀ z ∈ overlapDomain d d',
      ContDiffAt ℂ ∞ (fun y => d'.val (d.val.symm y)) z := by
    intro d d' z hz
    have hsrc : z ∈ (chartTransition d d').source := by
      simpa [chartTransition, OpenPartialHomeomorph.trans_source, overlapDomain] using hz
    have hcd := HolomorphicMaps.chartTransition_contDiffAt d d' hsrc
    refine hcd.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [chartTransition]
  have hτhol : DifferentiableOn ℂ τ A := fun z hz =>
    ((htrans e f z hz).differentiableAt (by simp)).differentiableWithinAt
  have hσsmooth : ContDiffOn ℝ 1 σ B := fun w hw =>
    (((htrans f e w hw).restrict_scalars ℝ).of_le (by simp)).contDiffWithinAt
  have hxA : e.val x ∈ A := mem_overlapDomain hex hfx
  have hτx : τ (e.val x) = f.val x := by
    simp only [hτdef, e.val.left_inv hex]
  have hmain := multiplierIntegrableAt_comp (μ := μ) (isOpen_overlapDomain e f)
    (isOpen_overlapDomain f e) hτhol hσsmooth hτA hσB hστ hτσ hweight hu hc hxA
    (by rw [hτx]; exact h)
  refine hmain.congr (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [(isOpen_overlapDomain e f).mem_nhds hxA] with z hz
  simp only [hτdef, f.val.left_inv (hAsub z hz)]

end Chart

end Hironaka.ChartWeightedL2
