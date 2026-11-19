import Hironaka.Analytic.QuantitativeRegularizationCanonicalWeights

set_option autoImplicit false

/-! # Uniform canonical point-pole extension bounds -/

open MeasureTheory
open scoped ENNReal ContDiff

namespace Hironaka.QuantitativeRegularizationCanonicalExtensions

noncomputable section

open Hormander PointPole

variable {d p : ℕ}

/-- Applying the point-pole Hörmander construction at every canonical radius
produces a single family with a radius-independent weighted `L²` bound. -/
theorem exists_canonical_poleExtension_residual_family
    (hH : HormanderL2Estimate d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) {r : ℝ} (hr : 0 < r)
    {φ : ComplexModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ D)
    (hφL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm φ z ξ) {Bφ : ℝ}
    (hBφ : ∀ z ∈ D, -Bφ ≤ φ z) (x : ComplexModel d)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (hθ1 : ∀ z ∈ Metric.ball x r, θ z = 1)
    {W : Set (ComplexModel d)} (hW : IsOpen W) (hts : tsupport θ ⊆ W)
    (htsD : tsupport θ ⊆ D) {f : ComplexModel d → ℂ}
    (hf : DifferentiableOn ℂ f W) {Mθ : ℝ}
    (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {K Kc : Set (ComplexModel d)} (hKo : IsOpen K) (hKKc : K ⊆ Kc)
    (hKc : IsCompact Kc) (hKcD : Kc ⊆ D) :
    ∃ G : ℕ → ComplexModel d → ℂ,
      (∀ i, DifferentiableOn ℂ (G i) K) ∧
      ∀ i, ∫⁻ z in K,
        ENNReal.ofReal (‖cutProd θ f z - G i z‖ ^ 2) *
          QuantitativeRegularizationCanonicalWeights.canonicalWeight p φ x i z ≤
        ENNReal.ofReal (2 * (Mθ ^ 2 * ((r ^ 2) ^ p)⁻¹) *
          ∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-φ z)) := by
  have hsingle : ∀ i : ℕ, ∃ G : ComplexModel d → ℂ, DifferentiableOn ℂ G K ∧
      ∫⁻ z in K, ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2 *
        Real.exp (-PointPole.poleWeight p φ x
          (QuantitativeRegularizationCanonicalRadii.canonicalRadius i) z)) ≤
        ENNReal.ofReal (2 * (Mθ ^ 2 * ((r ^ 2) ^ p)⁻¹) *
          ∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-φ z)) := by
    intro i
    exact Hironaka.PointPole.exists_poleExtension_delta
      (p := p) hH hDo hDc hDb
      (QuantitativeRegularizationCanonicalRadii.canonicalRadius_pos i) hr hφ hφL hBφ x
      hθ hθcs hθ1 hW hts htsD hf hMθ hKo hKKc hKc hKcD
  choose G hG hbound using hsingle
  refine ⟨G, hG, fun i => ?_⟩
  simpa [QuantitativeRegularizationCanonicalWeights.canonicalWeight] using hbound i

/-- If the cut-off product is holomorphic on the chosen local domain, the
Hörmander residual family supplies exactly the holomorphic weighted-bound
premise required by the canonical pole-limit corollary. -/
theorem exists_canonical_holomorphic_residual_family
    (hH : HormanderL2Estimate d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) {r : ℝ} (hr : 0 < r)
    {φ : ComplexModel d → ℝ} (hφ : ContDiffOn ℝ ∞ φ D)
    (hφL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm φ z ξ) {Bφ : ℝ}
    (hBφ : ∀ z ∈ D, -Bφ ≤ φ z) (x : ComplexModel d)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (hθ1 : ∀ z ∈ Metric.ball x r, θ z = 1)
    {W : Set (ComplexModel d)} (hW : IsOpen W) (hts : tsupport θ ⊆ W)
    (htsD : tsupport θ ⊆ D) {f : ComplexModel d → ℂ}
    (hf : DifferentiableOn ℂ f W) {Mθ : ℝ}
    (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {K Kc : Set (ComplexModel d)} (hKo : IsOpen K) (hKKc : K ⊆ Kc)
    (hKc : IsCompact Kc) (hKcD : Kc ⊆ D)
    (hcut : DifferentiableOn ℂ (cutProd θ f) K) :
    ∃ F : ℕ → ComplexModel d → ℂ,
      (∀ i, DifferentiableOn ℂ (F i) K) ∧
      ∀ i, ∫⁻ z in K, ENNReal.ofReal (‖F i z‖ ^ 2) *
        QuantitativeRegularizationCanonicalWeights.canonicalWeight p φ x i z ≤
        ENNReal.ofReal (2 * (Mθ ^ 2 * ((r ^ 2) ^ p)⁻¹) *
          ∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-φ z)) := by
  obtain ⟨G, hG, hbound⟩ := exists_canonical_poleExtension_residual_family
    (p := p) hH hDo hDc hDb hr hφ hφL hBφ x hθ hθcs hθ1 hW hts htsD hf hMθ
    hKo hKKc hKc hKcD
  refine ⟨fun i => cutProd θ f - G i, fun i => hcut.sub (hG i), ?_⟩
  intro i
  simpa using hbound i

end

end Hironaka.QuantitativeRegularizationCanonicalExtensions
