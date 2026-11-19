import Hironaka.Analytic.LocalBergmanMeasureTransport
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false

/-! # Actual Haar transport under complex linear coordinates -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Hironaka.MultiplierHaarLinearTransport

noncomputable section

/-- A positive finite scale of the actual measure preserves both weighted clauses. -/
theorem weightedL2On_nnreal_smul_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    {φ : E → EReal} {c : ℝ} {f : E → ℂ} {U : Set E}
    {s : ℝ≥0} (hs : s ≠ 0) :
    WeightedL2On φ c f U (s • μ) ↔ WeightedL2On φ c f U μ := by
  unfold WeightedL2On
  rw [Measure.restrict_smul, lintegral_smul_measure]
  have hs' : (s : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs
  change (AEMeasurable (multiplierDensity φ c f) ((s : ℝ≥0∞) • μ.restrict U) ∧
    s • (∫⁻ y, multiplierDensity φ c f y ∂μ.restrict U) < ⊤) ↔ _
  rw [aemeasurable_smul_measure_iff hs', ENNReal.nnreal_smul_lt_top_iff hs]

private theorem multiplierIntegrableAt_of_linear_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [LocallyCompactSpace F] [SecondCountableTopology F]
    (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (L : E ≃L[ℂ] F) {φ : F → EReal} {c : ℝ} {f : F → ℂ} {x : E}
    (hf : MultiplierIntegrableAt (φ ∘ L) c (f ∘ L) x μ) :
    MultiplierIntegrableAt φ c f (L x) ν := by
  let e : E ≃ᵐ F := L.toHomeomorph.toMeasurableEquiv
  let μ' : Measure F := μ.map L
  have : μ'.IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  let s : ℝ≥0 := μ'.addHaarScalarFactor ν
  have hs : s ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' ν).ne'
  have hμ : μ' = s • ν := Measure.isAddLeftInvariant_eq_smul μ' ν
  obtain ⟨hc, U, hU, hxU, hhol, hL2⟩ := hf
  have he : MeasurePreserving e μ μ' := ⟨e.measurable, rfl⟩
  have hL2image := weightedL2On_map_measurableEquiv e he hL2
  have hL2' : WeightedL2On φ c f (L '' U) μ' := by
    change WeightedL2On ((φ ∘ L) ∘ L.symm) c ((f ∘ L) ∘ L.symm) (L '' U) μ'
      at hL2image
    simpa only [Function.comp_def, L.apply_symm_apply] using hL2image
  rw [hμ] at hL2'
  have hL2ν := (weightedL2On_nnreal_smul_iff hs).mp hL2'
  have hmaps : MapsTo L.symm (L '' U) U := by
    rintro y ⟨z, hz, rfl⟩
    simpa only [L.symm_apply_apply] using hz
  have hhol' : DifferentiableOn ℂ f (L '' U) := by
    have hh := hhol.comp L.symm.differentiableOn hmaps
    have heq : (f ∘ L) ∘ L.symm = f := by
      funext y
      exact congrArg f (L.apply_symm_apply y)
    simpa only [heq] using hh
  exact ⟨hc, L '' U, L.toHomeomorph.isOpenMap U hU, ⟨x, hxU, rfl⟩, hhol', hL2ν⟩

/-- Actual Haar measures and inverse linear coordinates preserve literal multiplier germs. -/
theorem multiplierIntegrableAt_continuousLinearEquiv_iff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [LocallyCompactSpace E] [SecondCountableTopology E]
    [LocallyCompactSpace F] [SecondCountableTopology F]
    (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (L : E ≃L[ℂ] F) {φ : F → EReal} {c : ℝ} {f : F → ℂ} {x : E} :
    MultiplierIntegrableAt (φ ∘ L) c (f ∘ L) x μ ↔
      MultiplierIntegrableAt φ c f (L x) ν := by
  constructor
  · exact multiplierIntegrableAt_of_linear_pullback μ ν L
  · intro hf
    have hφ : (φ ∘ L) ∘ L.symm = φ := by
      funext y
      exact congrArg φ (L.apply_symm_apply y)
    have hf' : (f ∘ L) ∘ L.symm = f := by
      funext y
      exact congrArg f (L.apply_symm_apply y)
    have h := multiplierIntegrableAt_of_linear_pullback ν μ L.symm
      (x := L x) (φ := φ ∘ L) (f := f ∘ L)
      (by simpa only [hφ, hf'] using hf)
    simpa only [L.symm_apply_apply] using h

end
end Hironaka.MultiplierHaarLinearTransport
