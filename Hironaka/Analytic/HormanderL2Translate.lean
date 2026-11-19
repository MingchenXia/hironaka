import Hironaka.Analytic.HormanderL2Spaces

set_option autoImplicit false

/-!
# From `L²` classes back to functions

Translation lemmas between elements of the weighted `L²` spaces and the function-level
statements of `HormanderL2Estimate`: square norms and inner products of `toLp` classes are
weighted integrals, `e^{-w} dλ|_D`-a.e. equality is Lebesgue-a.e. equality on `D`, and weak
holomorphy of an `L²` function is orthogonality to the range of `T*`.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate ContDiff Topology InnerProductSpace ENNReal

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

variable {n : ℕ} {D : Set (ComplexModel n)}

theorem memLp_formVec_of_components {μ : Measure (ComplexModel n)}
    {f : Fin n → ComplexModel n → ℂ} (hf : ∀ j, MemLp (f j) 2 μ) :
    MemLp (formVec f) 2 μ := by
  have h : formVec f = fun x ↦ ∑ j, f j x • (EuclideanSpace.single j (1 : ℂ)) := by
    funext x; ext i
    simp [formVec, Finset.sum_apply, Pi.single_apply]
  rw [h]
  have := memLp_finsetSum Finset.univ fun j _ ↦
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single j (1 : ℂ))).comp_memLp' (hf j)
  simpa [Function.comp_def] using this

theorem norm_sq_toLp_eq_integral {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {μ : Measure (ComplexModel n)} {f : ComplexModel n → V} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := inner_toLp_eq_integral hf (hf.toLp f)
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ∫ x, ⟪f x, (hf.toLp f) x⟫_ℂ ∂μ = ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h2, integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h)

theorem ae_restrict_of_ae_weightedVolume (hD : IsOpen D) {w : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) {p : ComplexModel n → Prop}
    (h : ∀ᵐ x ∂(weightedVolume D w), p x) : ∀ᵐ x ∂(volume.restrict D), p x := by
  have hac : volume.restrict D ≪ weightedVolume D w := by
    rw [weightedVolume_eq_withDensity_weightDensity hD]
    refine withDensity_absolutelyContinuous' (measurable_weightDensity hD hw).aemeasurable ?_
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    simp [weightDensity, hx, Real.exp_pos]
  exact hac.ae_le h

section Weights

variable {w₁ w₂ ψ₀ : ComplexModel n → ℝ}

theorem integral_setD_conj_mul_eq_inner (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D)
    {h u : ComplexModel n → ℂ} (hh : MemLp h 2 (weightedVolume D w₁))
    (hu : MemLp u 2 (weightedVolume D w₁)) :
    ∫ x in D, conj (h x) * u x * Real.exp (-w₁ x) = ⟪hh.toLp h, hu.toLp u⟫_ℂ := by
  rw [inner_toLp_eq_integral]
  have h1 : ∫ x, ⟪h x, (hu.toLp u) x⟫_ℂ ∂(weightedVolume D w₁) =
      ∫ x, ⟪h x, u x⟫_ℂ ∂(weightedVolume D w₁) := by
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with x hx
    rw [hx]
  rw [h1, integral_weightedVolume hD hw₁]
  refine setIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
  simp only [RCLike.inner_apply, Complex.real_smul]
  ring

/-- An `L²` class is weakly holomorphic iff it is orthogonal to the range of `T*`. -/
theorem weakDbarEq_zero_iff_inner_tstar (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D)
    (hw₂ : ContDiffOn ℝ ∞ w₂ D) (hψ : ContinuousOn ψ₀ D) (h12 : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x)
    (H : Lp ℂ 2 (weightedVolume D w₁)) :
    WeakDbarEq D (H : ComplexModel n → ℂ) 0 ↔
      ∀ α : testForms D, ⟪tstarToL2 hD hw₁ hw₂ hψ α, H⟫_ℂ = 0 := by
  constructor
  · intro hH α
    rw [inner_tstarToL2]
    have := adjoint_pairing_of_weakDbarEq hD hw₁ hw₂ hψ h12 (Lp.memLp H) hH α.2
    simpa using this
  · intro hH
    refine weakDbarEq_of_adjoint_pairing hD hw₁ hw₂ h12 fun α hα ↦ ?_
    have := hH ⟨α, hα⟩
    rw [inner_tstarToL2] at this
    simpa using this

/-- Weak `∂̄ u = f` is the solution property of the abstract Hilbert-space argument. -/
theorem weakDbarEq_iff_inner (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D)
    (hw₂ : ContDiffOn ℝ ∞ w₂ D) (hψ : ContinuousOn ψ₀ D) (h12 : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x)
    {u : ComplexModel n → ℂ} (hu : MemLp u 2 (weightedVolume D w₁))
    {f : Fin n → ComplexModel n → ℂ} (hf : ∀ j, MemLp (f j) 2 (weightedVolume D w₂)) :
    WeakDbarEq D u f ↔ ∀ α : testForms D,
      ⟪tstarToL2 hD hw₁ hw₂ hψ α, hu.toLp u⟫_ℂ =
        ⟪formToL2 hD hw₂.continuousOn α, (memLp_formVec_of_components hf).toLp (formVec f)⟫_ℂ := by
  have hL : ∀ α : testForms D, ⟪tstarToL2 hD hw₁ hw₂ hψ α, hu.toLp u⟫_ℂ =
      ∫ x, conj (tstarForm w₂ ψ₀ α x) * u x ∂(weightedVolume D w₁) := by
    intro α
    rw [inner_tstarToL2]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with x hx
    rw [hx]
  have hR : ∀ α : testForms D, ⟪formToL2 hD hw₂.continuousOn α,
      (memLp_formVec_of_components hf).toLp (formVec f)⟫_ℂ =
      ∑ j, ∫ x, conj ((α : Fin n → ComplexModel n → ℂ) j x) * f j x ∂(weightedVolume D w₂) := by
    intro α
    rw [inner_formToL2]
    refine Finset.sum_congr rfl fun j _ ↦ integral_congr_ae ?_
    filter_upwards [(memLp_formVec_of_components hf).coeFn_toLp] with x hx
    rw [hx, formVec_apply]
  constructor
  · intro hweak α
    rw [hL, hR]
    exact adjoint_pairing_of_weakDbarEq hD hw₁ hw₂ hψ h12 hu hweak α.2
  · intro hinner
    refine weakDbarEq_of_adjoint_pairing hD hw₁ hw₂ h12 fun α hα ↦ ?_
    have := hinner ⟨α, hα⟩
    rwa [hL, hR] at this

end Weights

end

end Hironaka.Hormander
