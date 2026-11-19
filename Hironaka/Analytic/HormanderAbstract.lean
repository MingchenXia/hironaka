import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option autoImplicit false

/-!
# The Hilbert-space core of Hörmander's `L²` method

No unbounded operators are introduced.  Test objects form a complex vector space `V` with two
linear maps: `a : V → H₂` (the test form itself) and `A : V → H₁` (its formal adjoint `T* α`).
An element `u ∈ H₁` *solves* `T u = f` when `⟪A α, u⟫ = ⟪a α, f⟫` for every test `α`.

* `exists_solution_of_bound`: if `‖⟪a α, f⟫‖ ≤ C ‖A α‖` for all `α`, there is a solution `u` with
  `‖u‖ ≤ C` in the closure of `range A` (Hahn--Banach and Riesz).
* `norm_le_of_mem_closure_range`: every solution in the closure of `range A` (the *minimal*
  solution, orthogonal to the weak kernel of `T`) has `‖u‖ ≤ C`.
* `norm_inner_le_of_approx`: the bound `‖⟪a α, f⟫‖ ≤ √M ‖A α‖` follows from the a priori estimate
  `‖⟪a α, f⟫‖² ≤ M (‖A α‖² + ‖B α‖²)` when `f` lies in a closed subspace `W` (the kernel of `S`)
  and the projection of `a α` to `W` is a limit of test forms `α_k` with `A α_k → A α` and
  `B α_k → 0` (density of test forms in `dom T* ∩ ker S`).
-/

open Filter
open scoped InnerProductSpace Topology

namespace Hironaka.Hormander

noncomputable section

variable {V H₁ H₂ H₃ : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃]

/-- **Existence with a norm bound** (Hahn--Banach and Riesz). -/
theorem exists_solution_of_bound [CompleteSpace H₁] (a : V →ₗ[ℂ] H₂) (A : V →ₗ[ℂ] H₁)
    (f : H₂) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ α, ‖⟪a α, f⟫_ℂ‖ ≤ C * ‖A α‖) :
    ∃ u ∈ (LinearMap.range A).topologicalClosure,
      ‖u‖ ≤ C ∧ ∀ α, ⟪A α, u⟫_ℂ = ⟪a α, f⟫_ℂ := by
  set ℓ₀ : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ f).comp a with hℓ₀
  have hℓ₀a : ∀ α, ℓ₀ α = ⟪f, a α⟫_ℂ := fun α ↦ rfl
  have hker : LinearMap.ker A ≤ LinearMap.ker ℓ₀ := by
    intro α hα
    rw [LinearMap.mem_ker] at hα ⊢
    have h := hb α
    rw [hα, norm_zero, mul_zero] at h
    rw [hℓ₀a, ← inner_conj_symm, norm_le_zero_iff.mp h, map_zero]
  set ℓ₁ : LinearMap.range A →ₗ[ℂ] ℂ :=
    ((LinearMap.ker A).liftQ ℓ₀ hker).comp A.quotKerEquivRange.symm.toLinearMap with hℓ₁
  have hℓ₁a : ∀ α, ℓ₁ ⟨A α, LinearMap.mem_range_self A α⟩ = ⟪f, a α⟫_ℂ := by
    intro α
    have : A.quotKerEquivRange.symm ⟨A α, LinearMap.mem_range_self A α⟩ =
        Submodule.Quotient.mk α := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [hℓ₁, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    exact hℓ₀a α
  have hbound : ∀ y : LinearMap.range A, ‖ℓ₁ y‖ ≤ C * ‖y‖ := by
    rintro ⟨y, α, rfl⟩
    rw [hℓ₁a, ← inner_conj_symm, RCLike.norm_conj]
    exact hb α
  set ℓ : StrongDual ℂ (LinearMap.range A) := ℓ₁.mkContinuous C hbound
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq (LinearMap.range A) ℓ
  set N := (LinearMap.range A).topologicalClosure
  have : CompleteSpace N :=
    (Submodule.isClosed_topologicalClosure (LinearMap.range A)).completeSpace_coe
  set u₀ := (InnerProductSpace.toDual ℂ H₁).symm g
  refine ⟨N.starProjection u₀, N.starProjection_apply_mem u₀, ?_, fun α ↦ ?_⟩
  · calc ‖N.starProjection u₀‖ ≤ ‖u₀‖ := N.norm_starProjection_apply_le u₀
      _ = ‖g‖ := by simp [u₀]
      _ = ‖ℓ‖ := hgn
      _ ≤ C := LinearMap.mkContinuous_norm_le _ hC _
  · have hmem : A α ∈ N := (LinearMap.range A).le_topologicalClosure
      (LinearMap.mem_range_self A α)
    rw [← inner_conj_symm, Submodule.inner_starProjection_left_eq_right,
      N.starProjection_eq_self_iff.mpr hmem, InnerProductSpace.toDual_symm_apply,
      hg ⟨A α, LinearMap.mem_range_self A α⟩, LinearMap.mkContinuous_apply, hℓ₁a,
      inner_conj_symm]

/-- **The minimal solution satisfies the bound.** -/
theorem norm_le_of_mem_closure_range (a : V →ₗ[ℂ] H₂) (A : V →ₗ[ℂ] H₁) (f : H₂) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ α, ‖⟪a α, f⟫_ℂ‖ ≤ C * ‖A α‖) {u : H₁}
    (hu : u ∈ (LinearMap.range A).topologicalClosure)
    (hsol : ∀ α, ⟪A α, u⟫_ℂ = ⟪a α, f⟫_ℂ) : ‖u‖ ≤ C := by
  have hu' : u ∈ closure (LinearMap.range A : Set H₁) := by
    rw [← Submodule.topologicalClosure_coe]; exact hu
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp hu'
  choose α hα using fun k ↦ (hy k : y k ∈ LinearMap.range A)
  have h1 : Tendsto (fun k ↦ ‖⟪y k, u⟫_ℂ‖) atTop (𝓝 ‖⟪u, u⟫_ℂ‖) :=
    ((hlim.inner tendsto_const_nhds).norm)
  have h2 : Tendsto (fun k ↦ C * ‖y k‖) atTop (𝓝 (C * ‖u‖)) :=
    (hlim.norm.const_mul C)
  have hle : ‖⟪u, u⟫_ℂ‖ ≤ C * ‖u‖ :=
    le_of_tendsto_of_tendsto' h1 h2 fun k ↦ by
      rw [← hα k, hsol]; exact (hb (α k)).trans (by rw [hα k])
  simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hle
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hC
  · nlinarith

/-- **From the a priori estimate to the bound on the functional.** -/
theorem norm_inner_le_of_approx (a : V →ₗ[ℂ] H₂) (A : V →ₗ[ℂ] H₁) (B : V →ₗ[ℂ] H₃)
    (W : Submodule ℂ H₂) [W.HasOrthogonalProjection] {f : H₂} (hf : f ∈ W) {M : ℝ}
    (hM : 0 ≤ M) (hest : ∀ α, ‖⟪a α, f⟫_ℂ‖ ^ 2 ≤ M * (‖A α‖ ^ 2 + ‖B α‖ ^ 2))
    (happrox : ∀ α, ∃ β : ℕ → V, Tendsto (fun k ↦ a (β k)) atTop (𝓝 (W.starProjection (a α))) ∧
      Tendsto (fun k ↦ A (β k)) atTop (𝓝 (A α)) ∧ Tendsto (fun k ↦ B (β k)) atTop (𝓝 0))
    (α : V) : ‖⟪a α, f⟫_ℂ‖ ≤ Real.sqrt M * ‖A α‖ := by
  obtain ⟨β, h1, h2, h3⟩ := happrox α
  have hproj : ⟪a α, f⟫_ℂ = ⟪W.starProjection (a α), f⟫_ℂ := by
    rw [Submodule.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.mpr hf]
  have hlim : Tendsto (fun k ↦ ‖⟪a (β k), f⟫_ℂ‖ ^ 2) atTop (𝓝 (‖⟪a α, f⟫_ℂ‖ ^ 2)) := by
    rw [hproj]
    exact ((h1.inner tendsto_const_nhds).norm).pow 2
  have hlim2 : Tendsto (fun k ↦ M * (‖A (β k)‖ ^ 2 + ‖B (β k)‖ ^ 2)) atTop
      (𝓝 (M * (‖A α‖ ^ 2 + ‖(0 : H₃)‖ ^ 2))) :=
    ((h2.norm.pow 2).add (h3.norm.pow 2)).const_mul M
  have hle := le_of_tendsto_of_tendsto' hlim hlim2 fun k ↦ hest (β k)
  rw [norm_zero, zero_pow two_ne_zero, add_zero] at hle
  calc ‖⟪a α, f⟫_ℂ‖ = Real.sqrt (‖⟪a α, f⟫_ℂ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (M * ‖A α‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt M * ‖A α‖ := by
      rw [Real.sqrt_mul hM, Real.sqrt_sq (norm_nonneg _)]

/-- Variant of `norm_inner_le_of_approx` with a nonnegative functional `Q` in place of `‖B ·‖²`. -/
theorem norm_inner_le_of_approx' (a : V →ₗ[ℂ] H₂) (A : V →ₗ[ℂ] H₁) (Q : V → ℝ)
    (W : Submodule ℂ H₂) [W.HasOrthogonalProjection] {f : H₂} (hf : f ∈ W) {M : ℝ}
    (hM : 0 ≤ M) (hest : ∀ α, ‖⟪a α, f⟫_ℂ‖ ^ 2 ≤ M * (‖A α‖ ^ 2 + Q α))
    (happrox : ∀ α, ∃ β : ℕ → V, Tendsto (fun k ↦ a (β k)) atTop (𝓝 (W.starProjection (a α))) ∧
      Tendsto (fun k ↦ A (β k)) atTop (𝓝 (A α)) ∧ Tendsto (fun k ↦ Q (β k)) atTop (𝓝 0))
    (α : V) : ‖⟪a α, f⟫_ℂ‖ ≤ Real.sqrt M * ‖A α‖ := by
  obtain ⟨β, h1, h2, h3⟩ := happrox α
  have hproj : ⟪a α, f⟫_ℂ = ⟪W.starProjection (a α), f⟫_ℂ := by
    rw [Submodule.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.mpr hf]
  have hlim : Tendsto (fun k ↦ ‖⟪a (β k), f⟫_ℂ‖ ^ 2) atTop (𝓝 (‖⟪a α, f⟫_ℂ‖ ^ 2)) := by
    rw [hproj]
    exact ((h1.inner tendsto_const_nhds).norm).pow 2
  have hlim2 : Tendsto (fun k ↦ M * (‖A (β k)‖ ^ 2 + Q (β k))) atTop
      (𝓝 (M * (‖A α‖ ^ 2 + 0))) :=
    ((h2.norm.pow 2).add h3).const_mul M
  have hle := le_of_tendsto_of_tendsto' hlim hlim2 fun k ↦ hest (β k)
  rw [add_zero] at hle
  calc ‖⟪a α, f⟫_ℂ‖ = Real.sqrt (‖⟪a α, f⟫_ℂ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (M * ‖A α‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt M * ‖A α‖ := by
      rw [Real.sqrt_mul hM, Real.sqrt_sq (norm_nonneg _)]

/-- Elements orthogonal to the weak kernel `{h | ∀ α, ⟪A α, h⟫ = 0}` lie in the closure of
`range A`. -/
theorem mem_closure_range_of_orthogonal [CompleteSpace H₁] (A : V →ₗ[ℂ] H₁) {u : H₁}
    (hu : ∀ h : H₁, (∀ α, ⟪A α, h⟫_ℂ = 0) → ⟪h, u⟫_ℂ = 0) :
    u ∈ (LinearMap.range A).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  intro h hh
  refine hu h fun α ↦ ?_
  exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self A α) hh

end

end Hironaka.Hormander
