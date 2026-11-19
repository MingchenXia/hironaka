import Hironaka.Analytic.HolomorphicIdealSheaves
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false

/-!
# Transporting local Bergman mass to the preferred multiplier measure

The finite Bergman construction deliberately uses the Borel measurable space
on a coordinate model.  The global multiplier ideal instead uses the preferred
`WithLp` measurable-space instance inherited by `ComplexModel`.  This module
relates the two measures through actual measure-preserving linear isometries to
a common Euclidean model; it never treats the two `MeasureSpace` instances as
definitionally equal.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka



noncomputable section

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {φ : E → EReal} {c : ℝ} {f : E → ℂ} {U : Set E}
  {μ : Measure E} {ν : Measure F}

/-- A measurable equivalence which preserves the ambient measures transports
both clauses of `WeightedL2On`. -/
theorem weightedL2On_map_measurableEquiv
    (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν)
    (h : WeightedL2On φ c f U μ) :
    WeightedL2On (φ ∘ e.symm) c (f ∘ e.symm) (e '' U) ν := by
  have hdensity :
      multiplierDensity (φ ∘ e.symm) c (f ∘ e.symm) ∘ e =
        multiplierDensity φ c f := by
    funext x
    simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, multiplierDensity]
  constructor
  · rw [← he.map_eq, e.restrict_map, e.preimage_image]
    rw [aemeasurable_map_equiv_iff]
    simpa only [hdensity] using h.1
  · rw [← he.setLIntegral_comp_emb e.measurableEmbedding]
    change (∫⁻ x in U,
      (multiplierDensity (φ ∘ e.symm) c (f ∘ e.symm) ∘ e) x ∂μ) < ∞
    rw [hdensity]
    exact h.2

/-- Appending an empty coordinate block gives a real linear isometry from the
complex model to an ordinary Euclidean model. -/
noncomputable def localBergmanShiftZero (n : ℕ) : ComplexModel n ≃ₗᵢ[ℝ]
    EuclideanSpace ℂ (Fin n ⊕ Fin 0) :=
  { toLinearEquiv :=
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.sumEmpty (Fin n) (Fin 0)).symm).toLinearEquiv.restrictScalars ℝ
    norm_map' := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sumEmpty (Fin n) (Fin 0)).symm).norm_map }

private theorem localBergmanShiftZero_measurePreserving (n : ℕ) :
    MeasurePreserving (localBergmanShiftZero n) :=
  LinearIsometryEquiv.measurePreserving (localBergmanShiftZero n)

/-- A finite local weighted mass proved using Borel volume is also a finite
weighted mass for the preferred `ComplexModel` volume.  The proof explicitly
passes through a common Euclidean model, using the Borel and `WithLp` measures
in separate steps. -/
theorem weightedL2On_of_borelVolume
    {n : ℕ} {φ : ComplexModel n → EReal} {c : ℝ}
    {f : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (h : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact WeightedL2On φ c f U volume) :
    WeightedL2On φ c f U volume := by
  have hcommon : WeightedL2On (φ ∘ (localBergmanShiftZero n).symm) c
      (f ∘ (localBergmanShiftZero n).symm)
      ((localBergmanShiftZero n) '' U) volume := by
    let _ : MeasurableSpace (ComplexModel n) := borel _
    have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
    let e : ComplexModel n ≃ᵐ EuclideanSpace ℂ (Fin n ⊕ Fin 0) :=
      (localBergmanShiftZero n).toMeasurableEquiv
    have he : MeasurePreserving e volume volume := by
      change MeasurePreserving (localBergmanShiftZero n) volume volume
      exact LinearIsometryEquiv.measurePreserving (localBergmanShiftZero n)
    exact weightedL2On_map_measurableEquiv e he h
  let e : ComplexModel n ≃ᵐ EuclideanSpace ℂ (Fin n ⊕ Fin 0) :=
    (localBergmanShiftZero n).toMeasurableEquiv
  have hback := weightedL2On_map_measurableEquiv e.symm
    (localBergmanShiftZero_measurePreserving n).symm hcommon
  have hback' :
      WeightedL2On
        ((φ ∘ (localBergmanShiftZero n).symm) ∘ (localBergmanShiftZero n)) c
        ((f ∘ (localBergmanShiftZero n).symm) ∘ (localBergmanShiftZero n))
        ((fun x : ComplexModel n => x) '' U) volume := by
    simpa only [e, LinearIsometryEquiv.coe_toMeasurableEquiv,
      LinearIsometryEquiv.coe_symm_toMeasurableEquiv, MeasurableEquiv.symm_symm,
      Function.comp_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, Set.image_image] using hback
  have hφ : (φ ∘ (localBergmanShiftZero n).symm) ∘
      (localBergmanShiftZero n) = φ := by
    funext z
    change φ ((localBergmanShiftZero n).symm ((localBergmanShiftZero n) z)) = φ z
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hf : (f ∘ (localBergmanShiftZero n).symm) ∘
      (localBergmanShiftZero n) = f := by
    funext z
    change f ((localBergmanShiftZero n).symm ((localBergmanShiftZero n) z)) = f z
    rw [LinearIsometryEquiv.symm_apply_apply]
  simpa only [hφ, hf, Set.image_id'] using hback'

/-- The preceding finite-mass transport preserves the other local-germ data,
so it transports `MultiplierIntegrableAt` from the Borel formulation used by
the atlas to the preferred multiplier-ideal formulation. -/
theorem multiplierIntegrableAt_of_borelVolume
    {n : ℕ} {φ : ComplexModel n → EReal} {c : ℝ}
    {f : ComplexModel n → ℂ} {x : ComplexModel n}
    (h : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact MultiplierIntegrableAt φ c f x volume) :
    MultiplierIntegrableAt φ c f x volume := by
  rcases h with ⟨hc, U, hU, hx, hf, hL2⟩
  exact ⟨hc, U, hU, hx, hf, weightedL2On_of_borelVolume hL2⟩

end

end Hironaka
