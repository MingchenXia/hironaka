import Hironaka.Analytic.HormanderL2Translate

set_option autoImplicit false

/-!
# Hörmander's theorem from the bound on the pairing

If `‖⟪α, f⟫‖ ≤ √M ‖T* α‖` for all test forms `α`, then `∂̄ u = f` has a solution in
`L²(D, e^{-w₁})` orthogonal to all weakly holomorphic `L²` functions, and every such orthogonal
solution satisfies `∫_D |u|² e^{-w₁} ≤ M`.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate ContDiff Topology InnerProductSpace

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

variable {n : ℕ} {D : Set (ComplexModel n)} {w₁ w₂ ψ₀ : ComplexModel n → ℝ}

theorem hormander_of_pairing_bound (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D)
    (hw₂ : ContDiffOn ℝ ∞ w₂ D) (hψ : ContinuousOn ψ₀ D) (h12 : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x)
    {f : Fin n → ComplexModel n → ℂ} (hf : ∀ j, MemLp (f j) 2 (weightedVolume D w₂))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ α : testForms D,
      ‖⟪formToL2 hD hw₂.continuousOn α, (memLp_formVec_of_components hf).toLp (formVec f)⟫_ℂ‖ ≤
        Real.sqrt M * ‖tstarToL2 hD hw₁ hw₂ hψ α‖) :
    (∃ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D w₁) ∧ WeakDbarEq D u f ∧
      ∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D w₁) → WeakDbarEq D h 0 →
        ∫ x in D, conj (h x) * u x * Real.exp (-w₁ x) = 0) ∧
    ∀ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D w₁) → WeakDbarEq D u f →
      (∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D w₁) → WeakDbarEq D h 0 →
        ∫ x in D, conj (h x) * u x * Real.exp (-w₁ x) = 0) →
      ∫ x in D, ‖u x‖ ^ 2 * Real.exp (-w₁ x) ≤ M := by
  set a := formToL2 hD hw₂.continuousOn (w₂ := w₂)
  set A := tstarToL2 hD hw₁ hw₂ hψ
  set F := (memLp_formVec_of_components hf).toLp (formVec f)
  -- weakly holomorphic `L²` functions are orthogonal to `range A`
  have hker : ∀ {h : ComplexModel n → ℂ} (hh : MemLp h 2 (weightedVolume D w₁)),
      WeakDbarEq D h 0 → ∀ α : testForms D, ⟪A α, hh.toLp h⟫_ℂ = 0 := by
    intro h hh hweak α
    have hH : WeakDbarEq D (⇑(hh.toLp h)) 0 := by
      intro g hg j
      have hae := ae_restrict_of_ae_weightedVolume hD hw₁ hh.coeFn_toLp
      have hz : ∀ (F : ComplexModel n → ℂ), ∀ x ∉ D, F x * dbarDir (coordVec j) g x = 0 :=
        fun F x hx ↦ by simp [dbarDir_eq_zero_of_notMem_tsupport fun h' ↦ hx (hg.2.2 h')]
      have e1 : ∫ x, (hh.toLp h) x * dbarDir (coordVec j) g x =
          ∫ x, h x * dbarDir (coordVec j) g x := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D) (hz ⇑(hh.toLp h)),
          ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D) (hz h)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx]
      rw [e1]
      exact hweak g hg j
    exact (weakDbarEq_zero_iff_inner_tstar hD hw₁ hw₂ hψ h12 _).mp hH α
  constructor
  · obtain ⟨U, hUcl, -, hUsol⟩ :=
      Hormander.exists_solution_of_bound a A F (Real.sqrt_nonneg M) hbound
    refine ⟨⇑U, Lp.memLp U, ?_, fun h hh hweak ↦ ?_⟩
    · refine (weakDbarEq_iff_inner hD hw₁ hw₂ hψ h12 (Lp.memLp U) hf).mpr fun α ↦ ?_
      rw [Lp.toLp_coeFn]
      exact hUsol α
    · rw [integral_setD_conj_mul_eq_inner hD hw₁ hh (Lp.memLp U), Lp.toLp_coeFn]
      have horth : hh.toLp h ∈ (LinearMap.range A)ᗮ := by
        rw [Submodule.mem_orthogonal]
        rintro _ ⟨α, rfl⟩
        exact hker hh hweak α
      rw [← Submodule.orthogonal_orthogonal_eq_closure] at hUcl
      exact Submodule.inner_right_of_mem_orthogonal horth hUcl
  · intro u hu hweak horth
    set U := hu.toLp u
    have hsol : ∀ α, ⟪A α, U⟫_ℂ = ⟪a α, F⟫_ℂ :=
      (weakDbarEq_iff_inner hD hw₁ hw₂ hψ h12 hu hf).mp hweak
    have hUcl : U ∈ (LinearMap.range A).topologicalClosure := by
      refine mem_closure_range_of_orthogonal A fun H hH ↦ ?_
      have hHw : WeakDbarEq D (⇑H) 0 :=
        (weakDbarEq_zero_iff_inner_tstar hD hw₁ hw₂ hψ h12 H).mpr hH
      have := horth _ (Lp.memLp H) hHw
      rwa [integral_setD_conj_mul_eq_inner hD hw₁ (Lp.memLp H) hu, Lp.toLp_coeFn] at this
    have hnorm := norm_le_of_mem_closure_range a A F (Real.sqrt_nonneg M) hbound hUcl hsol
    have hsq : ‖U‖ ^ 2 ≤ M := by
      calc ‖U‖ ^ 2 ≤ Real.sqrt M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = M := Real.sq_sqrt hM
    rw [norm_sq_toLp_eq_integral, integral_weightedVolume hD hw₁] at hsq
    simpa [mul_comm] using hsq

end

end Hironaka.Hormander
