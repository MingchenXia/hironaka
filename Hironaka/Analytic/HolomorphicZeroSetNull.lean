import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false

/-!
# Zero sets of holomorphic functions are null

Let `U` be a convex open subset of a finite-dimensional complex normed space `E`, equipped
with an additive Haar measure `μ`, and let `f : E → ℂ` be complex differentiable on `U` with
`f x₁ ≠ 0` for some `x₁ ∈ U`.  Then `μ (U ∩ f⁻¹(0)) = 0`.

* `volume_inter_preimage_zero_eq_zero_of_complex`: in one variable the zeros on a connected
  open set are codiscrete, hence null.
* `measure_eq_zero_of_forall_line_null`: a measurable set meeting every complex line
  parallel to a fixed vector in a planar null set is null (Tonelli and translation
  invariance).
* `measure_inter_preimage_zero_eq_zero`: near `x₀ ∈ U`, the lines parallel to `x₁ - x₀`
  through points close to `x₀` pass close to `x₁`, where `f ≠ 0`; each such line meets the
  zero set in a planar null set.  A countable cover finishes the argument.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.HolomorphicZeroSetNull

/-- **One variable.** A complex differentiable function on a connected open subset of `ℂ`
which does not vanish identically has a null zero set there. -/
theorem volume_inter_preimage_zero_eq_zero_of_complex {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsPreconnected D) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g D) {t₀ : ℂ}
    (ht₀ : t₀ ∈ D) (hg₀ : g t₀ ≠ 0) : volume (D ∩ g ⁻¹' {0}) = 0 := by
  have hc : g ⁻¹' {0}ᶜ ∈ codiscreteWithin D :=
    (hg.analyticOnNhd hDo).preimage_zero_mem_codiscreteWithin hg₀ ht₀ ⟨⟨t₀, ht₀⟩, hDc⟩
  have hae := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℂ)) hDo.measurableSet hc
  rw [mem_ae_iff, Measure.restrict_apply' hDo.measurableSet] at hae
  simpa [inter_comm] using hae

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℂ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Null by complex line slices.** A measurable set whose intersection with every complex
line parallel to `v` is planar null is null. -/
theorem measure_eq_zero_of_forall_line_null {Z : Set E} (hZ : MeasurableSet Z) (v : E)
    (h : ∀ x : E, volume {t : ℂ | x + t • v ∈ Z} = 0) : μ Z = 0 := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  have : SecondCountableTopology E := secondCountable_of_proper
  set F : E → ℂ → ℝ≥0∞ := fun x t => Z.indicator 1 (x + t • v) with hF
  have hmeas : Measurable (Function.uncurry F) :=
    (measurable_one.indicator hZ).comp
      (continuous_fst.add (continuous_snd.smul continuous_const)).measurable
  have h1 : ∫⁻ t : ℂ, ∫⁻ x, F x t ∂μ = μ Z * ∞ := by
    have : ∀ t : ℂ, ∫⁻ x, F x t ∂μ = μ Z := by
      intro t
      simp only [hF]
      rw [lintegral_add_right_eq_self (μ := μ) (fun x => Z.indicator (1 : E → ℝ≥0∞) x) (t • v),
        lintegral_indicator_one hZ]
    simp only [this, lintegral_const, measure_univ_of_isAddLeftInvariant]
  have h2 : ∫⁻ x, ∫⁻ t : ℂ, F x t ∂volume ∂μ = 0 := by
    have : ∀ x : E, ∫⁻ t : ℂ, F x t = 0 := by
      intro x
      have hpre : MeasurableSet {t : ℂ | x + t • v ∈ Z} :=
        hZ.preimage (by fun_prop)
      have : (fun t : ℂ => F x t) = {t : ℂ | x + t • v ∈ Z}.indicator 1 := by
        funext t
        simp [hF, Set.indicator]
      rw [this, lintegral_indicator_one hpre, h x]
    simp [this]
  rw [← lintegral_lintegral_swap hmeas.aemeasurable, h2] at h1
  rcases (mul_eq_zero.mp h1.symm) with h0 | h0
  · exact h0
  · exact absurd h0 ENNReal.top_ne_zero

/-- **Zero sets are null.** A function complex differentiable on a convex open set `U`
and nonzero at some point of `U` has a null zero set in `U`. -/
theorem measure_inter_preimage_zero_eq_zero {U : Set E} (hUo : IsOpen U)
    (hUc : Convex ℝ U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U) {x₁ : E} (hx₁ : x₁ ∈ U)
    (hfx₁ : f x₁ ≠ 0) : μ (U ∩ f ⁻¹' {0}) = 0 := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  have : SecondCountableTopology E := secondCountable_of_proper
  have hev : ∀ᶠ y in 𝓝 x₁, y ∈ U ∧ f y ≠ 0 :=
    (show ∀ᶠ y in 𝓝 x₁, y ∈ U from hUo.mem_nhds hx₁).and
      ((hf.continuousOn.continuousAt (hUo.mem_nhds hx₁)).eventually_ne hfx₁)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hZ : MeasurableSet (U ∩ f ⁻¹' {0}) := by
    have ho : IsOpen (U ∩ f ⁻¹' {0}ᶜ) :=
      hf.continuousOn.isOpen_inter_preimage hUo isOpen_compl_singleton
    have : U ∩ f ⁻¹' {0} = U \ (U ∩ f ⁻¹' {0}ᶜ) := by
      ext y; simp
    rw [this]
    exact hUo.measurableSet.diff ho.measurableSet
  refine measure_null_of_locally_null _ fun x₀ hx₀ => ?_
  refine ⟨(U ∩ f ⁻¹' {0}) ∩ ball x₀ δ, inter_mem_nhdsWithin _ (ball_mem_nhds x₀ hδ), ?_⟩
  refine measure_eq_zero_of_forall_line_null μ (hZ.inter measurableSet_ball) (x₁ - x₀) ?_
  intro x
  set v := x₁ - x₀ with hv
  rcases Set.eq_empty_or_nonempty {t : ℂ | x + t • v ∈ (U ∩ f ⁻¹' {0}) ∩ ball x₀ δ} with
    he | ⟨t₀, ht₀⟩
  · rw [he, measure_empty]
  set D : Set ℂ := {t : ℂ | x + t • v ∈ U} with hD
  have hlin : Continuous fun t : ℂ => x + t • v := by fun_prop
  have hDo : IsOpen D := hUo.preimage hlin
  have hDc : Convex ℝ D := by
    have h1 : Convex ℝ ((fun y => x + y) ⁻¹' U) := hUc.translate_preimage_right x
    have h2 : IsLinearMap ℝ fun t : ℂ => t • v :=
      ⟨fun a b => add_smul a b v, fun c a => by rw [smul_assoc]⟩
    exact h1.is_linear_preimage h2
  have hgd : DifferentiableOn ℂ (fun t : ℂ => f (x + t • v)) D :=
    hf.comp (by fun_prop : Differentiable ℂ fun t : ℂ => x + t • v).differentiableOn
      (fun t ht => ht)
  have hmem : x + (t₀ + 1) • v ∈ ball x₁ δ := by
    have heq : x + (t₀ + 1) • v - x₁ = (x + t₀ • v) - x₀ := by
      rw [hv, add_smul, one_smul]; abel
    rw [mem_ball, dist_eq_norm, heq, ← dist_eq_norm]
    exact ht₀.2
  refine measure_mono_null ?_ (volume_inter_preimage_zero_eq_zero_of_complex hDo
    hDc.isPreconnected hgd (t₀ := t₀ + 1) (hball _ hmem).1 (hball _ hmem).2)
  intro t ht
  exact ⟨ht.1.1, ht.1.2⟩

/-- Ball version of `measure_inter_preimage_zero_eq_zero`. -/
theorem measure_ball_inter_preimage_zero_eq_zero {c : E} {r : ℝ} {f : E → ℂ}
    (hf : DifferentiableOn ℂ f (ball c r)) {x₁ : E} (hx₁ : x₁ ∈ ball c r)
    (hfx₁ : f x₁ ≠ 0) : μ (ball c r ∩ f ⁻¹' {0}) = 0 :=
  measure_inter_preimage_zero_eq_zero μ isOpen_ball (convex_ball c r) hf hx₁ hfx₁

end Hironaka.HolomorphicZeroSetNull
