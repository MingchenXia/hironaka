import Hironaka.Analytic.PointPoleExtension

set_option autoImplicit false

/-!
# Pole-weighted holomorphic limits for quantitative regularization

This is the limiting part of the point-pole extension used in Step 2 of
Copy-4 `lem:regularization`. The Hoermander construction supplies, for every
regularizing pole radius, a holomorphic correction with one uniform weighted
`L²` bound. `WeightedL2ExtensionLimit` gives a strict subsequence converging
locally uniformly to a holomorphic limit. If the supremum of the weights
dominates every regularized pole, that actual limit vanishes at the pole by
`PointPole.eq_zero_of_lintegral_pole_bounded`.

The result deliberately contains no global chart or cover data.  It is the
analytic bridge from a parameterwise point-pole estimate to the
point-interpolating extension which the finite-cover construction needs.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace Hironaka.QuantitativeRegularizationPoleLimit

noncomputable section



variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- A monotone family of weighted holomorphic bounds has a strict subsequence
with locally uniform limit `G`; if the limiting weight dominates every
regularized pole at `x`, this actual limit vanishes at `x`. -/
theorem exists_subseq_differentiableOn_vanishing_limit_of_pole_dominated_bounds
    {U : Set (ComplexModel d)} (hU : IsOpen U) {x : ComplexModel d} (hx : x ∈ U)
    {w : ℕ → ComplexModel d → ℝ≥0∞}
    (hwm : ∀ z ∈ U, Monotone fun i => w i z)
    (hwmeas : ∀ i, AEMeasurable (w i) (volume.restrict U))
    (hlow : ∀ z ∈ U, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball z r, ENNReal.ofReal δ ≤ w 0 y)
    {F : ℕ → ComplexModel d → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ i, ∫⁻ z in U, ENNReal.ofReal (‖F i z‖ ^ 2) * w i z ≤ A)
    (hd : 0 < d) {c : ℝ} (hc : 0 < c)
    (hpole : ∀ η : ℝ, 0 < η → ∀ z ∈ U,
      ENNReal.ofReal c *
          ENNReal.ofReal (((‖z - x‖ ^ 2 + η ^ 2) ^ (d + 1))⁻¹) ≤ ⨆ i, w i z) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel d → ℂ), StrictMono ψ ∧
      DifferentiableOn ℂ G U ∧
      TendstoLocallyUniformlyOn (fun i => F (ψ i)) G atTop U ∧
      G x = 0 ∧
      ∫⁻ z in U, ENNReal.ofReal (‖G z‖ ^ 2) * ⨆ i, w i z ≤ A := by
  let Uconst : ℕ → Set (ComplexModel d) := fun _ => U
  have hUconst : (⋃ i, Uconst i) = U := by
    ext z
    simp [Uconst]
  have hwm' : ∀ z ∈ ⋃ i, Uconst i, Monotone fun i => w i z := by
    rw [hUconst]
    exact hwm
  have hwmeas' : ∀ i, AEMeasurable (w i) (volume.restrict (⋃ j, Uconst j)) := by
    intro i
    rw [hUconst]
    exact hwmeas i
  have hlow' : ∀ z ∈ ⋃ i, Uconst i, ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball z r, ENNReal.ofReal δ ≤ w 0 y := by
    rw [hUconst]
    exact hlow
  obtain ⟨ψ, G, hψ, hG, hconv, -, hGint⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds
      (U := Uconst) (w := w) (α := Empty)
      (ι := fun e : Empty => e.elim) (g := fun e : Empty => e.elim)
      (fun _ => hU) (fun _ _ _ => subset_rfl) hwm' hwmeas' hlow'
      (by simpa [Uconst] using hF) (fun _ e _ => e.elim) hA
      (by simpa [Uconst] using hbound)
  have hGU : DifferentiableOn ℂ G U := by
    rw [← hUconst]
    exact hG
  have hGintU : ∫⁻ z in U, ENNReal.ofReal (‖G z‖ ^ 2) * ⨆ i, w i z ≤ A := by
    rw [← hUconst]
    exact hGint
  have hconvU : TendstoLocallyUniformlyOn (fun i => F (ψ i)) G atTop U := by
    rw [← hUconst]
    exact hconv
  refine ⟨ψ, G, hψ, hGU, hconvU, ?_, hGintU⟩
  apply PointPole.eq_zero_of_lintegral_pole_bounded hd hU hx hGU hc hA
  intro η hη
  refine (setLIntegral_mono' hU.measurableSet fun z hz => ?_).trans hGintU
  calc
    ENNReal.ofReal (c * ‖G z‖ ^ 2) *
        ENNReal.ofReal (((‖z - x‖ ^ 2 + η ^ 2) ^ (d + 1))⁻¹) =
        ENNReal.ofReal (‖G z‖ ^ 2) *
          (ENNReal.ofReal c *
            ENNReal.ofReal (((‖z - x‖ ^ 2 + η ^ 2) ^ (d + 1))⁻¹)) := by
      rw [ENNReal.ofReal_mul hc.le]
      ring
    _ ≤ ENNReal.ofReal (‖G z‖ ^ 2) * ⨆ i, w i z := by
      gcongr
      exact hpole η hη z hz

end

end Hironaka.QuantitativeRegularizationPoleLimit
