import Hironaka.Resolution.HironakaG10FlatPolydiscKoszul

/-! # Douady's Prop. 5 Cor. with hypotheses on the base presentation itself

`HironakaG10FlatPolydiscKoszul.koszul_directExact` assumes exactness and complements for the
`b`-fold copies `M₀ ⊗ I_b` of the base matrices. Here they are derived from the same properties of
`M₀` (`M₀ ⊗ I_b` acts on each slice `x(·, k)` as `M₀`, `kron_apply_slice`):

* `kron_eq_zero_iff`, `exists_kron_eq` (exactness of `b` copies), `mem_range_kron_iff`;
* `closedComplemented_ker_kron`, `closedComplemented_range_kron` (slicewise projections);
* `koszul_directExact_of_base`: if `(g₀, f₀)` over `B(K')` is exact in the middle with complemented
  `ker f₀`, `ker g₀`, `im f₀` and `f₀ g₀ = 0`, the Koszul total complex of `W` on the pulled-back
  complex over `B(K' × D̄(0,ρ))` is exact in the middle with complemented kernels and image —
  privilege (start of a resolution) passes from `K'` to the hypersurface `W = 0`
  (Douady 1966, §7 n° 2, Corollaire de la Proposition 5).

BP: hironaka-g10-flat-polydisc-koszul-base.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscKoszulBase
noncomputable section
open Classical HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision
  HironakaG10FlatPolydiscQuotient HironakaG10FlatPolydiscPrivilege HironakaG10FlatPolydiscRemainderMap
  HironakaG10FlatPolydiscPushforward HironakaG10FlatKoszulDivision HironakaG10FlatPolydiscKoszul

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {K' : Set P} [CompactSpace K']
  {b : ℕ} {p q : Type*} [Fintype p] [Fintype q]

/-- The `k`-th slice `x(·, k)`, as a continuous linear map. -/
def sliceCLM (p : Type*) [Fintype p] (k : Fin b) :
    (p × Fin b → holSubalgebra K') →L[ℂ] (p → holSubalgebra K') :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (i, k)

omit [CompactSpace K'] in
theorem sliceCLM_apply (k : Fin b) (x : p × Fin b → holSubalgebra K') (i : p) :
    sliceCLM p k x i = x (i, k) := rfl

omit [Fintype q] in
/-- `M₀ ⊗ I_b` acts on each slice as `M₀`. -/
theorem kron_apply_slice (M₀ : q → p → holSubalgebra K') (x : p × Fin b → holSubalgebra K')
    (j : q) (k : Fin b) :
    matrixOperator (kronMatrix b M₀) x (j, k) = matrixOperator M₀ (sliceCLM p k x) j := by
  rw [kron_apply, matrixOperator_apply]
  rfl

omit [Fintype q] in
theorem kron_eq_zero_iff (M₀ : q → p → holSubalgebra K') (x : p × Fin b → holSubalgebra K') :
    matrixOperator (kronMatrix b M₀) x = 0 ↔ ∀ k, matrixOperator M₀ (sliceCLM p k x) = 0 := by
  constructor
  · intro h k
    funext j
    rw [← kron_apply_slice, h]
    rfl
  · intro h
    funext jk
    rw [kron_apply_slice, h jk.2]
    rfl

/-- `y ∈ im (M₀ ⊗ I_b)` iff every slice of `y` lies in `im M₀`. -/
theorem mem_range_kron_iff (M₀ : q → p → holSubalgebra K') (y : q × Fin b → holSubalgebra K') :
    y ∈ LinearMap.range (matrixOperator (kronMatrix b M₀) :
      (p × Fin b → holSubalgebra K') →ₗ[ℂ] (q × Fin b → holSubalgebra K')) ↔
      ∀ k, sliceCLM q k y ∈ LinearMap.range (matrixOperator M₀ :
        (p → holSubalgebra K') →ₗ[ℂ] (q → holSubalgebra K')) := by
  constructor
  · rintro ⟨x, rfl⟩ k
    refine ⟨sliceCLM p k x, ?_⟩
    funext j
    show matrixOperator M₀ (sliceCLM p k x) j = matrixOperator (kronMatrix b M₀) x (j, k)
    rw [kron_apply_slice]
  · intro h
    choose t ht using h
    refine ⟨fun ik => t ik.2 ik.1, ?_⟩
    funext jk
    show matrixOperator (kronMatrix b M₀) (fun ik => t ik.2 ik.1) jk = y jk
    rw [kron_apply_slice]
    have := congrFun (ht jk.2) jk.1
    exact this

omit [Fintype q] in
/-- Exactness of `b` copies. -/
theorem exists_kron_eq {r : Type*} [Fintype r] (g₀ : p → r → holSubalgebra K')
    (f₀ : q → p → holSubalgebra K')
    (hex : ∀ x, matrixOperator f₀ x = 0 → ∃ t, matrixOperator g₀ t = x)
    (x : p × Fin b → holSubalgebra K') (hx : matrixOperator (kronMatrix b f₀) x = 0) :
    ∃ t, matrixOperator (kronMatrix b g₀) t = x := by
  have h : ∀ k, sliceCLM p k x ∈ LinearMap.range (matrixOperator g₀ :
      (r → holSubalgebra K') →ₗ[ℂ] (p → holSubalgebra K')) :=
    fun k => hex _ ((kron_eq_zero_iff f₀ x).mp hx k)
  exact (mem_range_kron_iff g₀ x).mpr h

/-- The slicewise operator `x ↦ ((T (x(·,k))) i)_{(i,k)}`. -/
def sliceOp (T : (p → holSubalgebra K') →L[ℂ] (p → holSubalgebra K')) :
    (p × Fin b → holSubalgebra K') →L[ℂ] (p × Fin b → holSubalgebra K') :=
  ContinuousLinearMap.pi fun ik => (ContinuousLinearMap.proj ik.1).comp (T.comp (sliceCLM p ik.2))

omit [CompactSpace K'] in
theorem sliceCLM_sliceOp (T : (p → holSubalgebra K') →L[ℂ] (p → holSubalgebra K'))
    (x : p × Fin b → holSubalgebra K') (k : Fin b) :
    sliceCLM p k (sliceOp T x) = T (sliceCLM p k x) := rfl

omit [Fintype q] in
/-- **`ker (M₀ ⊗ I_b)` is complemented if `ker M₀` is.** -/
theorem closedComplemented_ker_kron (M₀ : q → p → holSubalgebra K')
    (h : (LinearMap.ker (matrixOperator M₀ :
      (p → holSubalgebra K') →ₗ[ℂ] (q → holSubalgebra K'))).ClosedComplemented) :
    (LinearMap.ker (matrixOperator (kronMatrix b M₀) :
      (p × Fin b → holSubalgebra K') →ₗ[ℂ] (q × Fin b → holSubalgebra K'))).ClosedComplemented := by
  obtain ⟨T, hT, hTS⟩ := exists_proj_of_closedComplemented h
  refine closedComplemented_of_proj _ (sliceOp T) (fun x => ?_) (fun x hx => ?_)
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, kron_eq_zero_iff]
    intro k
    rw [sliceCLM_sliceOp]
    exact hT _
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, kron_eq_zero_iff] at hx
    funext ik
    show T (sliceCLM p ik.2 x) ik.1 = x ik
    rw [hTS _ (hx ik.2)]
    rfl

/-- **`im (M₀ ⊗ I_b)` is complemented if `im M₀` is.** -/
theorem closedComplemented_range_kron (M₀ : q → p → holSubalgebra K')
    (h : (LinearMap.range (matrixOperator M₀ :
      (p → holSubalgebra K') →ₗ[ℂ] (q → holSubalgebra K'))).ClosedComplemented) :
    (LinearMap.range (matrixOperator (kronMatrix b M₀) :
      (p × Fin b → holSubalgebra K') →ₗ[ℂ] (q × Fin b → holSubalgebra K'))).ClosedComplemented := by
  obtain ⟨T, hT, hTS⟩ := exists_proj_of_closedComplemented h
  refine closedComplemented_of_proj _ (sliceOp T) (fun y => ?_) (fun y hy => ?_)
  · rw [mem_range_kron_iff]
    intro k
    rw [sliceCLM_sliceOp]
    exact hT _
  · rw [mem_range_kron_iff] at hy
    funext jk
    show T (sliceCLM q jk.2 y) jk.1 = y jk
    rw [hTS _ (hy jk.2)]
    rfl

variable [FiniteDimensional ℂ P] {ρ : ℝ} {A : ℕ → P → ℂ} {U : Set P}
  [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]

/-- **Privilege passes from `K'` to the hypersurface `W = 0`** (Douady 1966, §7 Prop. 5 Cor., for a
start of a resolution), with hypotheses on the base presentation `(g₀, f₀)` itself. -/
theorem koszul_directExact_of_base (H : WeierstrassHyp K' ρ b A U) {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂]
    [Fintype ι₁] [Fintype ι₀] (g₀ : ι₁ → ι₂ → holSubalgebra K') (f₀ : ι₀ → ι₁ → holSubalgebra K')
    (hfg₀ : ∀ i k, ∑ j, f₀ i j * g₀ j k = 0)
    (hex : ∀ x, matrixOperator f₀ x = 0 → ∃ t, matrixOperator g₀ t = x)
    (hkerf : (LinearMap.ker (matrixOperator f₀ :
      (ι₁ → holSubalgebra K') →ₗ[ℂ] (ι₀ → holSubalgebra K'))).ClosedComplemented)
    (himf : (LinearMap.range (matrixOperator f₀ :
      (ι₁ → holSubalgebra K') →ₗ[ℂ] (ι₀ → holSubalgebra K'))).ClosedComplemented)
    (hkerg : (LinearMap.ker (matrixOperator g₀ :
      (ι₂ → holSubalgebra K') →ₗ[ℂ] (ι₁ → holSubalgebra K'))).ClosedComplemented) :
    (∀ z, koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) z = 0 →
      ∃ w, koszulD₂ (divData H ι₁) (matrixOperator (pullMatrix ρ g₀))
        (matrixOperator (pullMatrix ρ f₀)) w = z) ∧
    (LinearMap.ker (koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)) →ₗ[ℂ] (ι₀ → BK K' ρ))).ClosedComplemented ∧
    (LinearMap.range (koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)) →ₗ[ℂ] (ι₀ → BK K' ρ))).ClosedComplemented ∧
    (LinearMap.ker (koszulD₂ (divData H ι₁) (matrixOperator (pullMatrix ρ g₀))
      (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₂ → BK K' ρ) × (ι₁ → BK K' ρ)) →ₗ[ℂ] ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)))).ClosedComplemented :=
  koszul_directExact H g₀ f₀ hfg₀ (exists_kron_eq g₀ f₀ hex) (closedComplemented_ker_kron f₀ hkerf)
    (closedComplemented_range_kron f₀ himf) (closedComplemented_ker_kron g₀ hkerg)

end
end Hironaka.HironakaG10FlatPolydiscKoszulBase
