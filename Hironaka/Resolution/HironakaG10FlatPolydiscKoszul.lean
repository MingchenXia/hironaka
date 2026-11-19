import Hironaka.Resolution.HironakaG10FlatPolydiscPushforward
import Hironaka.Resolution.HironakaG10FlatKoszulDivision

/-! # Privilege passes from `K'` to the hypersurface `W = 0` over `K' × D̄(0,ρ)`

Instantiation of `HironakaG10FlatKoszulDivision` for `B(K)`, `K = K' × D̄(0,ρ)`, under
`WeierstrassHyp K' ρ b A U` (Douady 1966, §7 n° 2, Corollaire de la Proposition 5, for
`W = w − a`; here for any Weierstrass polynomial `W` with roots in `D(0,ρ)`).

* `divData H q`: the division datum on `B(K)^q` (`μ` = multiplication by `W`, `rem = remVec`,
  `sec = polyVec`, `quot` componentwise), remainder space `B(K')^{q × b}`.
* `pullMatrix`, `kronMatrix`: a matrix `M₀` over `B(K')` pulled back to `B(K)`, and `M₀ ⊗ I_b`;
  `pushMatrix_pullMatrix`: the pushed-forward matrix of a pulled-back matrix is `M₀ ⊗ I_b`;
  `divHom_pullMatrix`: pulled-back matrices are compatible with the division data.
* `koszul_directExact`: let `g₀ : B(K')^{ι₂} → B(K')^{ι₁}`, `f₀ : B(K')^{ι₁} → B(K')^{ι₀}` be matrices
  with `f₀ g₀ = 0` such that `(g₀ ⊗ I_b, f₀ ⊗ I_b)` is exact at the middle with complemented kernels
  and complemented image of `f₀ ⊗ I_b`. Then the Koszul total complex of `W` on the pulled-back
  complex, `B(K)^{ι₂} × B(K)^{ι₁} → B(K)^{ι₁} × B(K)^{ι₀} → B(K)^{ι₀}` — a start of a resolution of
  `pr^* coker f₀ ⊗ O/(W)` — is exact and direct.

BP: hironaka-g10-flat-polydisc-koszul.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscKoszul
noncomputable section
open Classical HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision
  HironakaG10FlatPolydiscQuotient HironakaG10FlatPolydiscPrivilege HironakaG10FlatPolydiscRemainderMap
  HironakaG10FlatPolydiscPushforward HironakaG10FlatKoszulDivision

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  {K' : Set P} {ρ : ℝ} {b : ℕ} {A : ℕ → P → ℂ} {U : Set P}
  [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K']

/-- Multiplication by `W` on `B(K)^q`. -/
def mulWVec (H : WeierstrassHyp K' ρ b A U) (q : Type*) [Fintype q] :
    (q → BK K' ρ) →L[ℂ] (q → BK K' ρ) :=
  ContinuousLinearMap.pi fun j => (mulW H).comp (ContinuousLinearMap.proj j)

/-- The componentwise quotient on `B(K)^q`. -/
def quotVec (H : WeierstrassHyp K' ρ b A U) (q : Type*) [Fintype q] :
    (q → BK K' ρ) →L[ℂ] (q → BK K' ρ) :=
  ContinuousLinearMap.pi fun j => (quotMap H).comp (ContinuousLinearMap.proj j)

/-- **The division datum on `B(K)^q`.** -/
def divData (H : WeierstrassHyp K' ρ b A U) (q : Type*) [Fintype q] :
    DivData (q → BK K' ρ) (q × Fin b → holSubalgebra K') where
  μ := mulWVec H q
  rem := remVec H
  sec := polyVec K' ρ b q
  quot := quotVec H q
  rem_sec := remVec_polyVec H
  rem_μ x := (remVec_eq_zero_iff H _).mpr ⟨x, rfl⟩
  quot_μ x := funext fun j => quotMap_Welem_mul H (x j)
  decomp x := funext fun j => eq_quot_rem H (x j)

variable {p q : Type*} [Fintype p] [Fintype q]

variable (ρ) in
/-- A matrix over `B(K')` pulled back to `B(K)`. -/
def pullMatrix (M₀ : q → p → holSubalgebra K') : q → p → BK K' ρ :=
  fun j i => pull K' ρ (M₀ j i)

/-- The matrix `M₀ ⊗ I_b` over `B(K')`. -/
def kronMatrix (b : ℕ) (M₀ : q → p → holSubalgebra K') : q × Fin b → p × Fin b → holSubalgebra K' :=
  fun jk il => if jk.2 = il.2 then M₀ jk.1 il.1 else 0

omit [Fintype p] [Fintype q] in
/-- The pushed-forward matrix of a pulled-back matrix is `M₀ ⊗ I_b`. -/
theorem pushMatrix_pullMatrix (H : WeierstrassHyp K' ρ b A U) (M₀ : q → p → holSubalgebra K') :
    pushMatrix H (pullMatrix ρ M₀) = kronMatrix b M₀ := by
  funext jk il
  simp only [pushMatrix, pullMatrix, mulMatrix_pull, Matrix.diagonal_apply, kronMatrix]

omit [FiniteDimensional ℂ P] in
theorem polyMap_eq_sum (r : Fin b → holSubalgebra K') :
    polyMap K' ρ b r = ∑ k : Fin b, pull K' ρ (r k) * wPow K' ρ k := by
  rw [polyMap_apply, polySum_extFin]

omit [FiniteDimensional ℂ P] [Fintype q] in
theorem kron_apply (M₀ : q → p → holSubalgebra K') (r : p × Fin b → holSubalgebra K') (j : q)
    (k : Fin b) : matrixOperator (kronMatrix b M₀) r (j, k) = ∑ i, M₀ j i * r (i, k) := by
  rw [matrixOperator_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [kronMatrix]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro l _ hl
    rw [if_neg (fun h => hl h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **Pulled-back matrices are compatible with the division data.** -/
theorem divHom_pullMatrix (H : WeierstrassHyp K' ρ b A U) (M₀ : q → p → holSubalgebra K') :
    DivHom (divData H p) (divData H q) (matrixOperator (pullMatrix ρ M₀))
      (matrixOperator (kronMatrix b M₀)) where
  comm_μ x := by
    funext j
    have e1 : ((divData H q).μ (matrixOperator (pullMatrix ρ M₀) x)) j =
        Welem H * matrixOperator (pullMatrix ρ M₀) x j := rfl
    have e2 : (divData H p).μ x = fun i => Welem H * x i := rfl
    rw [e1, e2, matrixOperator_apply, matrixOperator_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  comm_rem x := by
    show remVec H (matrixOperator (pullMatrix ρ M₀) x) = matrixOperator (kronMatrix b M₀) (remVec H x)
    rw [remVec_matrixOperator, pushMatrix_pullMatrix]
  comm_sec r := by
    funext j
    show matrixOperator (pullMatrix ρ M₀) (polyVec K' ρ b p r) j =
      polyVec K' ρ b q (matrixOperator (kronMatrix b M₀) r) j
    rw [matrixOperator_apply, polyVec_apply, polyMap_eq_sum]
    simp only [polyVec_apply, polyMap_eq_sum, kron_apply, map_sum, map_mul, pullMatrix,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

omit [FiniteDimensional ℂ P] [CompactSpace K'] [Fintype p] in
/-- A product `f₀ g₀ = 0` of matrices over `B(K')` pulls back to a zero composite. -/
theorem pullMatrix_comp_eq_zero {r : Type*} [Fintype r] (g₀ : q → r → holSubalgebra K')
    (f₀ : p → q → holSubalgebra K') (hfg₀ : ∀ i k, ∑ j, f₀ i j * g₀ j k = 0) (u : r → BK K' ρ) :
    matrixOperator (pullMatrix ρ f₀) (matrixOperator (pullMatrix ρ g₀) u) = 0 := by
  funext i
  have h : ∀ k, ∑ j, pull K' ρ (f₀ i j) * (pull K' ρ (g₀ j k) * u k) =
      pull K' ρ (∑ j, f₀ i j * g₀ j k) * u k := by
    intro k
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc]
  simp only [matrixOperator_apply, pullMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [h, hfg₀, map_zero, zero_mul, Finset.sum_const_zero, Pi.zero_apply]

/-- **Privilege passes to the hypersurface `W = 0`** (Douady 1966, §7 Prop. 5 Cor., for a start of a
resolution): if `(g₀ ⊗ I_b, f₀ ⊗ I_b)` is exact and direct over `B(K')`, the Koszul total complex of
`W` on the pulled-back complex is exact and direct over `B(K' × D̄(0,ρ))`. -/
theorem koszul_directExact (H : WeierstrassHyp K' ρ b A U) {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂]
    [Fintype ι₁] [Fintype ι₀] (g₀ : ι₁ → ι₂ → holSubalgebra K') (f₀ : ι₀ → ι₁ → holSubalgebra K')
    (hfg₀ : ∀ i k, ∑ j, f₀ i j * g₀ j k = 0)
    (hex : ∀ r, matrixOperator (kronMatrix b f₀) r = 0 →
      ∃ t, matrixOperator (kronMatrix b g₀) t = r)
    (hkerf : (LinearMap.ker (matrixOperator (kronMatrix b f₀) :
      (ι₁ × Fin b → holSubalgebra K') →ₗ[ℂ] (ι₀ × Fin b → holSubalgebra K'))).ClosedComplemented)
    (himf : (LinearMap.range (matrixOperator (kronMatrix b f₀) :
      (ι₁ × Fin b → holSubalgebra K') →ₗ[ℂ] (ι₀ × Fin b → holSubalgebra K'))).ClosedComplemented)
    (hkerg : (LinearMap.ker (matrixOperator (kronMatrix b g₀) :
      (ι₂ × Fin b → holSubalgebra K') →ₗ[ℂ] (ι₁ × Fin b → holSubalgebra K'))).ClosedComplemented) :
    (∀ z, koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) z = 0 →
      ∃ w, koszulD₂ (divData H ι₁) (matrixOperator (pullMatrix ρ g₀))
        (matrixOperator (pullMatrix ρ f₀)) w = z) ∧
    (LinearMap.ker (koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)) →ₗ[ℂ] (ι₀ → BK K' ρ))).ClosedComplemented ∧
    (LinearMap.range (koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)) →ₗ[ℂ] (ι₀ → BK K' ρ))).ClosedComplemented ∧
    (LinearMap.ker (koszulD₂ (divData H ι₁) (matrixOperator (pullMatrix ρ g₀))
      (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₂ → BK K' ρ) × (ι₁ → BK K' ρ)) →ₗ[ℂ] ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)))).ClosedComplemented := by
  have hg := divHom_pullMatrix H g₀
  have hf := divHom_pullMatrix H f₀
  have hfg := pullMatrix_comp_eq_zero (ρ := ρ) g₀ f₀ hfg₀
  exact ⟨exists_koszulD₂_eq hg hf hfg hex,
    closedComplemented_ker_koszulD₁ hf hkerf, closedComplemented_range_koszulD₁ hf himf,
    closedComplemented_ker_koszulD₂ hg hfg hkerg⟩

end
end Hironaka.HironakaG10FlatPolydiscKoszul
