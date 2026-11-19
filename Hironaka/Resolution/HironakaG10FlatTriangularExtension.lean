import Hironaka.Resolution.HironakaG10FlatResolutionStart

/-! # Douady's Proposition 3 (extensions), Banach core: triangular complexes

Douady 1966, §7 n° 2, Prop. 3 (a): if `K` is privileged for `F'` and `F''` and `0 → F' → F → F'' → 0`
is exact, `K` is privileged for `F`. The proof takes a horseshoe resolution `L = L' ⊕ L''` of `F`, whose
differential is upper triangular, `d = [d' h; 0 d'']`, and shows that `B(K; L)` is exact and direct
when `B(K; L')`, `B(K; L'')` are. This module is that Banach-space step, degree by degree, with
directness carried by bounded generalized inverses (`HironakaG10FlatGeneralizedInverse`).

For Banach spaces and bounded maps `a : A₁ → A₀`, `h : C₁ → A₀`, `c : C₁ → C₀`, the triangular
operator is `triOp a h c (x, y) = (a x + h y, c y)`.

* `triOp_comp`: `triOp a₁ h₁ c₁ ∘ triOp a₂ h₂ c₂ = 0` from `a₁a₂ = 0`, `a₁h₂ + h₁c₂ = 0`, `c₁c₂ = 0`.
* `triOp_exact`: exactness in the middle from exactness of the two diagonal complexes.
* `triInv`, `triOp_triInv`: if `a`, `c` have generalized inverses `R_A`, `R_C` and `h` maps `ker c` into
  `im a` (`exists_of_exact`: automatic when the `C`-complex is exact at `C₁`), then
  `(z, w) ↦ (R_A (z − h R_C w), R_C w)` is a generalized inverse of `triOp a h c`;
  `triOp_direct`: `triOp a h c` is direct.
* Matrix form over a Banach algebra: `triMatrix a h c = [a h; 0 c]`, `sumCLE`,
  `matrixOperator_triMatrix`, and **`directExact_triMatrix`**: if `(a₂, a₁)` and `(c₂, c₁)` are direct
  exact starts, `a₁h₂ + h₁c₂ = 0` and `h₂ (ker c₂) ⊆ im a₂`, then `([a₂ h₂; 0 c₂], [a₁ h₁; 0 c₁])` is a
  direct exact start.

The construction of the horseshoe resolution itself (sheaf level) is NOT done here.
BP: hironaka-g10-flat-triangular-extension.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaG10FlatTriangularExtension
noncomputable section
open HironakaG10FlatGeneralizedInverse HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart

section Abstract
variable {A₂ A₁ A₀ C₂ C₁ C₀ : Type*} [NormedAddCommGroup A₂] [NormedSpace ℂ A₂]
  [NormedAddCommGroup A₁] [NormedSpace ℂ A₁] [NormedAddCommGroup A₀] [NormedSpace ℂ A₀]
  [NormedAddCommGroup C₂] [NormedSpace ℂ C₂] [NormedAddCommGroup C₁] [NormedSpace ℂ C₁]
  [NormedAddCommGroup C₀] [NormedSpace ℂ C₀]

/-- The triangular operator `(x, y) ↦ (a x + h y, c y)`. -/
def triOp (a : A₁ →L[ℂ] A₀) (h : C₁ →L[ℂ] A₀) (c : C₁ →L[ℂ] C₀) : A₁ × C₁ →L[ℂ] A₀ × C₀ :=
  (a.comp (ContinuousLinearMap.fst ℂ A₁ C₁) + h.comp (ContinuousLinearMap.snd ℂ A₁ C₁)).prod
    (c.comp (ContinuousLinearMap.snd ℂ A₁ C₁))

theorem triOp_apply (a : A₁ →L[ℂ] A₀) (h : C₁ →L[ℂ] A₀) (c : C₁ →L[ℂ] C₀) (z : A₁ × C₁) :
    triOp a h c z = (a z.1 + h z.2, c z.2) := rfl

variable {a₂ : A₂ →L[ℂ] A₁} {a₁ : A₁ →L[ℂ] A₀} {h₂ : C₂ →L[ℂ] A₁} {h₁ : C₁ →L[ℂ] A₀}
  {c₂ : C₂ →L[ℂ] C₁} {c₁ : C₁ →L[ℂ] C₀}

/-- The triangular complex is a complex. -/
theorem triOp_comp (ha : ∀ u, a₁ (a₂ u) = 0) (hh : ∀ v, a₁ (h₂ v) + h₁ (c₂ v) = 0)
    (hc : ∀ v, c₁ (c₂ v) = 0) (z : A₂ × C₂) : triOp a₁ h₁ c₁ (triOp a₂ h₂ c₂ z) = 0 := by
  rw [triOp_apply, triOp_apply, map_add, ha, zero_add, hh, hc]
  rfl

/-- **Exactness in the middle** of the triangular complex. -/
theorem triOp_exact (hh : ∀ v, a₁ (h₂ v) + h₁ (c₂ v) = 0) (hA : ∀ x, a₁ x = 0 → ∃ u, a₂ u = x)
    (hC : ∀ y, c₁ y = 0 → ∃ v, c₂ v = y) (z : A₁ × C₁) (hz : triOp a₁ h₁ c₁ z = 0) :
    ∃ w, triOp a₂ h₂ c₂ w = z := by
  rw [triOp_apply, Prod.mk_eq_zero] at hz
  obtain ⟨v, hv⟩ := hC z.2 hz.2
  have hx : a₁ (z.1 - h₂ v) = 0 := by
    have h1 := hh v
    rw [hv] at h1
    rw [map_sub, show a₁ z.1 - a₁ (h₂ v) = (a₁ z.1 + h₁ z.2) - (a₁ (h₂ v) + h₁ z.2) by abel, hz.1,
      h1, sub_zero]
  obtain ⟨u, hu⟩ := hA _ hx
  refine ⟨(u, v), ?_⟩
  rw [triOp_apply]
  exact Prod.ext (by simp [hu]) hv

/-- `h` maps `ker c₁` into `im a₁` when the `C`-complex is exact at `C₁`. -/
theorem exists_of_exact (hh : ∀ v, a₁ (h₂ v) + h₁ (c₂ v) = 0)
    (hC : ∀ y, c₁ y = 0 → ∃ v, c₂ v = y) (y : C₁) (hy : c₁ y = 0) : ∃ x, a₁ x = h₁ y := by
  obtain ⟨v, rfl⟩ := hC y hy
  exact ⟨-h₂ v, by rw [map_neg, neg_eq_iff_add_eq_zero]; exact hh v⟩

/-- The generalized inverse `(z, w) ↦ (R_A (z − h (R_C w)), R_C w)` of a triangular operator. -/
def triInv (RA : A₀ →L[ℂ] A₁) (h : C₁ →L[ℂ] A₀) (RC : C₀ →L[ℂ] C₁) : A₀ × C₀ →L[ℂ] A₁ × C₁ :=
  (RA.comp (ContinuousLinearMap.fst ℂ A₀ C₀ - h.comp (RC.comp (ContinuousLinearMap.snd ℂ A₀ C₀)))).prod
    (RC.comp (ContinuousLinearMap.snd ℂ A₀ C₀))

theorem triInv_apply (RA : A₀ →L[ℂ] A₁) (h : C₁ →L[ℂ] A₀) (RC : C₀ →L[ℂ] C₁) (z : A₀ × C₀) :
    triInv RA h RC z = (RA (z.1 - h (RC z.2)), RC z.2) := rfl

/-- **Generalized inverse of a triangular operator.** -/
theorem triOp_triInv {a : A₁ →L[ℂ] A₀} {h : C₁ →L[ℂ] A₀} {c : C₁ →L[ℂ] C₀} {RA : A₀ →L[ℂ] A₁}
    {RC : C₀ →L[ℂ] C₁} (hRA : ∀ x, a (RA (a x)) = a x) (hRC : ∀ y, c (RC (c y)) = c y)
    (hhc : ∀ y, c y = 0 → ∃ x, a x = h y) (z : A₁ × C₁) :
    triOp a h c (triInv RA h RC (triOp a h c z)) = triOp a h c z := by
  obtain ⟨x, y⟩ := z
  have hker : c (y - RC (c y)) = 0 := by rw [map_sub, hRC, sub_self]
  obtain ⟨x', hx'⟩ := hhc _ hker
  have key : a x + h y - h (RC (c y)) = a (x + x') := by
    rw [map_add, hx', map_sub]
    abel
  simp only [triOp_apply, triInv_apply]
  refine Prod.ext ?_ (hRC y)
  show a (RA (a x + h y - h (RC (c y)))) + h (RC (c y)) = a x + h y
  rw [key, hRA, ← key]
  abel

/-- **A triangular operator with direct diagonal blocks is direct** (Banach spaces), provided `h`
maps `ker c` into `im a`. -/
theorem triOp_direct [CompleteSpace A₁] [CompleteSpace A₀] [CompleteSpace C₁] [CompleteSpace C₀]
    {a : A₁ →L[ℂ] A₀} {h : C₁ →L[ℂ] A₀} {c : C₁ →L[ℂ] C₀}
    (hkerA : (LinearMap.ker (a : A₁ →ₗ[ℂ] A₀)).ClosedComplemented)
    (hranA : (LinearMap.range (a : A₁ →ₗ[ℂ] A₀)).ClosedComplemented)
    (hkerC : (LinearMap.ker (c : C₁ →ₗ[ℂ] C₀)).ClosedComplemented)
    (hranC : (LinearMap.range (c : C₁ →ₗ[ℂ] C₀)).ClosedComplemented)
    (hhc : ∀ y, c y = 0 → ∃ x, a x = h y) :
    (LinearMap.ker (triOp a h c : A₁ × C₁ →ₗ[ℂ] A₀ × C₀)).ClosedComplemented ∧
      (LinearMap.range (triOp a h c : A₁ × C₁ →ₗ[ℂ] A₀ × C₀)).ClosedComplemented := by
  obtain ⟨RA, hRA⟩ := exists_generalizedInverse a hkerA hranA
  obtain ⟨RC, hRC⟩ := exists_generalizedInverse c hkerC hranC
  have hR := triOp_triInv hRA hRC hhc
  exact ⟨closedComplemented_ker_of_generalizedInverse _ _ hR,
    closedComplemented_range_of_generalizedInverse _ _ hR⟩

end Abstract

/-! ## Matrix form over a Banach algebra -/

section Matrix
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- `(ι ⊕ κ → R) ≃ (ι → R) × (κ → R)`, as a continuous linear equivalence. -/
def sumCLE (ι κ : Type*) : (ι ⊕ κ → R) ≃L[ℂ] (ι → R) × (κ → R) :=
  { LinearEquiv.sumArrowLequivProdArrow ι κ ℂ R with
    continuous_toFun := (continuous_pi fun _ => continuous_apply _).prodMk
      (continuous_pi fun _ => continuous_apply _)
    continuous_invFun := continuous_pi fun s => by
      rcases s with i | k
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply k).comp continuous_snd }

theorem sumCLE_apply {ι κ : Type*} (v : ι ⊕ κ → R) :
    sumCLE ι κ v = (fun i => v (Sum.inl i), fun k => v (Sum.inr k)) := rfl

variable {ι₂ ι₁ ι₀ κ₂ κ₁ κ₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀] [Fintype κ₂]
  [Fintype κ₁] [Fintype κ₀]

/-- The block upper triangular matrix `[a h; 0 c]`. -/
def triMatrix {ι κ ι' κ' : Type*} (a : ι → ι' → R) (h : ι → κ' → R) (c : κ → κ' → R) :
    ι ⊕ κ → ι' ⊕ κ' → R
  | Sum.inl i => Sum.elim (a i) (h i)
  | Sum.inr k => Sum.elim (fun _ => 0) (c k)

theorem matrixOperator_triMatrix (a : ι₀ → ι₁ → R) (h : ι₀ → κ₁ → R) (c : κ₀ → κ₁ → R)
    (v : ι₁ ⊕ κ₁ → R) :
    sumCLE ι₀ κ₀ (matrixOperator (triMatrix a h c) v) =
      triOp (matrixOperator a) (matrixOperator h) (matrixOperator c) (sumCLE ι₁ κ₁ v) := by
  rw [triOp_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · simp [sumCLE_apply, matrixOperator_apply, Fintype.sum_sum_type, triMatrix]
  · simp [sumCLE_apply, matrixOperator_apply, Fintype.sum_sum_type, triMatrix]

theorem matrixOperator_triMatrix_eq (a : ι₀ → ι₁ → R) (h : ι₀ → κ₁ → R) (c : κ₀ → κ₁ → R)
    (v : ι₁ ⊕ κ₁ → R) :
    matrixOperator (triMatrix a h c) v = (sumCLE ι₀ κ₀).symm
      (triOp (matrixOperator a) (matrixOperator h) (matrixOperator c) (sumCLE ι₁ κ₁ v)) := by
  rw [← matrixOperator_triMatrix, ContinuousLinearEquiv.symm_apply_apply]

/-- Generalized inverses transfer along the identification `sumCLE`. -/
theorem exists_generalizedInverse_triMatrix [CompleteSpace R] {a : ι₀ → ι₁ → R} {h : ι₀ → κ₁ → R}
    {c : κ₀ → κ₁ → R}
    (hkerA : (LinearMap.ker (matrixOperator a : (ι₁ → R) →ₗ[ℂ] (ι₀ → R))).ClosedComplemented)
    (hranA : (LinearMap.range (matrixOperator a : (ι₁ → R) →ₗ[ℂ] (ι₀ → R))).ClosedComplemented)
    (hkerC : (LinearMap.ker (matrixOperator c : (κ₁ → R) →ₗ[ℂ] (κ₀ → R))).ClosedComplemented)
    (hranC : (LinearMap.range (matrixOperator c : (κ₁ → R) →ₗ[ℂ] (κ₀ → R))).ClosedComplemented)
    (hhc : ∀ y, matrixOperator c y = 0 → ∃ x, matrixOperator a x = matrixOperator h y) :
    ∃ S : (ι₀ ⊕ κ₀ → R) →L[ℂ] (ι₁ ⊕ κ₁ → R), ∀ v,
      matrixOperator (triMatrix a h c) (S (matrixOperator (triMatrix a h c) v)) =
        matrixOperator (triMatrix a h c) v := by
  obtain ⟨RA, hRA⟩ := exists_generalizedInverse _ hkerA hranA
  obtain ⟨RC, hRC⟩ := exists_generalizedInverse _ hkerC hranC
  have hR := triOp_triInv hRA hRC hhc
  refine ⟨(((sumCLE (R := R) ι₁ κ₁).symm : ((ι₁ → R) × (κ₁ → R)) ≃L[ℂ] (ι₁ ⊕ κ₁ → R)) :
      ((ι₁ → R) × (κ₁ → R)) →L[ℂ] (ι₁ ⊕ κ₁ → R)).comp
    ((triInv RA (matrixOperator h) RC).comp ((sumCLE (R := R) ι₀ κ₀ :
      (ι₀ ⊕ κ₀ → R) ≃L[ℂ] (ι₀ → R) × (κ₀ → R)) : (ι₀ ⊕ κ₀ → R) →L[ℂ] (ι₀ → R) × (κ₀ → R))),
    fun v => ?_⟩
  rw [matrixOperator_triMatrix_eq a h c v]
  show matrixOperator (triMatrix a h c) ((sumCLE ι₁ κ₁).symm (triInv RA (matrixOperator h) RC
    (sumCLE ι₀ κ₀ ((sumCLE ι₀ κ₀).symm _)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, matrixOperator_triMatrix_eq,
    ContinuousLinearEquiv.apply_symm_apply, hR]

/-- **Douady's Prop. 3 (a), Banach core, for starts of resolutions**: if `(a₂, a₁)` and `(c₂, c₁)`
are direct exact starts over a Banach algebra, `a₁h₂ + h₁c₂ = 0` and `h₂` maps `ker c₂` into
`im a₂`, the triangular start `([a₂ h₂; 0 c₂], [a₁ h₁; 0 c₁])` is direct exact. -/
theorem directExact_triMatrix [CompleteSpace R] {a₂ : ι₁ → ι₂ → R} {a₁ : ι₀ → ι₁ → R}
    {h₂ : ι₁ → κ₂ → R} {h₁ : ι₀ → κ₁ → R} {c₂ : κ₁ → κ₂ → R} {c₁ : κ₀ → κ₁ → R}
    (hA : DirectExact a₂ a₁) (hC : DirectExact c₂ c₁)
    (hh : ∀ i k, ∑ j, a₁ i j * h₂ j k + ∑ j, h₁ i j * c₂ j k = 0)
    (hker₂ : ∀ v, matrixOperator c₂ v = 0 → ∃ u, matrixOperator a₂ u = matrixOperator h₂ v) :
    DirectExact (triMatrix a₂ h₂ c₂) (triMatrix a₁ h₁ c₁) := by
  -- the operator identities
  have hh' : ∀ v, matrixOperator a₁ (matrixOperator h₂ v) + matrixOperator h₁ (matrixOperator c₂ v)
      = 0 := by
    intro v
    funext i
    simp only [matrixOperator_apply, Pi.add_apply, Pi.zero_apply, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun j k => h₁ i j * (c₂ j k * v k)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, hh i k, zero_mul]
  have hA₁ : ∀ x, matrixOperator a₁ x = 0 → ∃ u, matrixOperator a₂ u = x := hA.exact
  have hC₁ : ∀ y, matrixOperator c₁ y = 0 → ∃ v, matrixOperator c₂ v = y := hC.exact
  have hran_a₂ : (LinearMap.range (matrixOperator a₂ : (ι₂ → R) →ₗ[ℂ] (ι₁ → R))).ClosedComplemented :=
    hA.range_eq_ker ▸ hA.kerf
  have hran_c₂ : (LinearMap.range (matrixOperator c₂ : (κ₂ → R) →ₗ[ℂ] (κ₁ → R))).ClosedComplemented :=
    hC.range_eq_ker ▸ hC.kerf
  obtain ⟨S₁, hS₁⟩ := exists_generalizedInverse_triMatrix (h := h₁) hA.kerf hA.imf hC.kerf hC.imf
    (exists_of_exact hh' hC₁)
  obtain ⟨S₂, hS₂⟩ := exists_generalizedInverse_triMatrix (h := h₂) hA.kerg hran_a₂ hC.kerg hran_c₂
    hker₂
  refine ⟨fun s t => ?_, fun v hv => ?_, closedComplemented_ker_of_generalizedInverse _ _ hS₁,
    closedComplemented_range_of_generalizedInverse _ _ hS₁,
    closedComplemented_ker_of_generalizedInverse _ _ hS₂⟩
  · -- `d₁ d₂ = 0` entrywise
    rcases s with i | k <;> rcases t with i' | k'
    · simp only [triMatrix, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
        Finset.sum_const_zero, add_zero]
      exact hA.comp i i'
    · simp only [triMatrix, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      exact hh i k'
    · simp [triMatrix, Fintype.sum_sum_type]
    · simp only [triMatrix, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
        Finset.sum_const_zero, zero_add]
      exact hC.comp k k'
  · -- exactness, through `sumCLE`
    have hv' : triOp (matrixOperator a₁) (matrixOperator h₁) (matrixOperator c₁)
        (sumCLE ι₁ κ₁ v) = 0 := by
      rw [← matrixOperator_triMatrix, hv, map_zero]
    obtain ⟨w, hw⟩ := triOp_exact hh' hA₁ hC₁ _ hv'
    refine ⟨(sumCLE ι₂ κ₂).symm w, ?_⟩
    rw [matrixOperator_triMatrix_eq, ContinuousLinearEquiv.apply_symm_apply, hw,
      ContinuousLinearEquiv.symm_apply_apply]

end Matrix

end
end Hironaka.HironakaG10FlatTriangularExtension
