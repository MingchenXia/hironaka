import Hironaka.Resolution.HironakaG10FlatPolydiscRemainderMap
import Mathlib.Topology.Algebra.Module.Complement

/-! # Pushforward of a `B(K)`-presentation killed by a Weierstrass polynomial

Split 3 of the privileged-neighbourhood programme (REPORT-r2, lane G10F). Under
`WeierstrassHyp K' ρ b A U`, `K = K' × D̄(0,ρ)`, let `M` be a `q × p` matrix over `B(K)`
(e.g. the restriction to `K` of a holomorphic presentation matrix of a coherent sheaf), acting by
`matrixOperator M : B(K)^p → B(K)^q`, and assume that `W` kills the cokernel:
`W eⱼ ∈ M · B(K)^p` for every `j` (`KillsCoker`; e.g. if `W ∈ Ann(coker M)` on a neighbourhood of
`K`). Put `M' = pushMatrix M`, the `(q × b) × (p × b)` matrix over `B(K')` whose `(j,i)` block is
the multiplication matrix of `Mⱼᵢ` on `B(K)/W·B(K) ≅ B(K')^b`
(`HironakaG10FlatPolydiscRemainderMap.mulMatrix`). Then, with `rem : B(K)^q → B(K')^{q×b}` the
componentwise remainder (`remVec`, a split surjection with section `polyVec`):

* `remVec_matrixOperator`: `rem (M v) = M' (rem v)`;
* `mem_range_iff`: `u ∈ M · B(K)^p ↔ rem u ∈ M' · B(K')^{p×b}`;
* `isClosed_range_iff`: the image of `M` is closed iff the image of `M'` is closed;
* `closedComplemented_range_iff`: the image of `M` is topologically complemented iff the image of
  `M'` is;
* `cokernelEquiv`: `B(K)^q / M·B(K)^p ≃ B(K')^{q×b} / M'·B(K')^{p×b}`.

So the image/cokernel half of privilege of `K` for `coker M` is EQUIVALENT to the same property of
`K'` for the pushed-forward presentation `M'` in one variable less (Douady 1966 §7; Frisch 1968).
Kernels (syzygies) are not transferred here. BP: hironaka-g10-flat-polydisc-pushforward.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscPushforward
noncomputable section
open Classical HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision
  HironakaG10FlatPolydiscQuotient HironakaG10FlatPolydiscPrivilege HironakaG10FlatPolydiscRemainderMap

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  {K' : Set P} {ρ : ℝ} {b : ℕ} {A : ℕ → P → ℂ} {U : Set P}
  [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K']
  {p q : Type*} [Fintype p] [Fintype q]

/-- `B(K' × D̄(0,ρ))`. -/
abbrev BK (K' : Set P) (ρ : ℝ) := holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)

/-! ## Componentwise remainder and its section -/

/-- The componentwise remainder `B(K)^q → B(K')^{q × b}`. -/
def remVec (H : WeierstrassHyp K' ρ b A U) :
    (q → BK K' ρ) →L[ℂ] (q × Fin b → holSubalgebra K') :=
  ContinuousLinearMap.pi fun jk =>
    (ContinuousLinearMap.proj jk.2).comp ((remMap H).comp (ContinuousLinearMap.proj jk.1))

omit [Fintype q] in
theorem remVec_apply (H : WeierstrassHyp K' ρ b A U) (v : q → BK K' ρ) (jk : q × Fin b) :
    remVec H v jk = remMap H (v jk.1) jk.2 := rfl

variable (K' ρ b q) in
/-- The componentwise polynomial `B(K')^{q × b} → B(K)^q`, `r ↦ (∑_{k<b} r_{jk} wᵏ)_j`. -/
def polyVec : (q × Fin b → holSubalgebra K') →L[ℂ] (q → BK K' ρ) :=
  ContinuousLinearMap.pi fun j =>
    (polyMap K' ρ b).comp (ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (j, k))

omit [FiniteDimensional ℂ P] [Fintype q] in
theorem polyVec_apply (r : q × Fin b → holSubalgebra K') (j : q) :
    polyVec K' ρ b q r j = polyMap K' ρ b (fun k => r (j, k)) := rfl

omit [Fintype q] in
theorem remVec_polyVec (H : WeierstrassHyp K' ρ b A U) (r : q × Fin b → holSubalgebra K') :
    remVec H (polyVec K' ρ b q r) = r := by
  funext jk
  rw [remVec_apply, polyVec_apply, remMap_polyMap]

omit [Fintype q] in
theorem remVec_eq_zero_iff (H : WeierstrassHyp K' ρ b A U) (v : q → BK K' ρ) :
    remVec H v = 0 ↔ ∃ u : q → BK K' ρ, v = fun j => Welem H * u j := by
  constructor
  · intro h
    have hj : ∀ j, remMap H (v j) = 0 := fun j => funext fun k => congrFun h (j, k)
    refine ⟨fun j => quotMap H (v j), funext fun j => ?_⟩
    conv_lhs => rw [eq_quot_rem H (v j), hj j, map_zero, add_zero]
  · rintro ⟨u, rfl⟩
    funext jk
    rw [remVec_apply, remMap_Welem_mul]
    rfl

/-! ## The pushed-forward matrix -/

/-- The pushed-forward matrix over `B(K')`: the `(j,i)` block is the multiplication matrix of
`Mⱼᵢ` on `B(K)/W·B(K) ≅ B(K')^b`. -/
def pushMatrix (H : WeierstrassHyp K' ρ b A U) (M : q → p → BK K' ρ) :
    q × Fin b → p × Fin b → holSubalgebra K' :=
  fun jk il => mulMatrix H (M jk.1 il.1) jk.2 il.2

omit [Fintype q] in
/-- **The remainder intertwines `M` and `M'`.** -/
theorem remVec_matrixOperator (H : WeierstrassHyp K' ρ b A U) (M : q → p → BK K' ρ)
    (v : p → BK K' ρ) :
    remVec H (matrixOperator M v) = matrixOperator (pushMatrix H M) (remVec H v) := by
  funext jk
  rw [remVec_apply, matrixOperator_apply, matrixOperator_apply, map_sum, Finset.sum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [remMap_mul]
  simp only [Matrix.mulVec, dotProduct, pushMatrix, remVec_apply]

/-! ## Transfer of the image -/

/-- `W` kills the cokernel of `M`: `W eⱼ ∈ M · B(K)^p` for every `j`. -/
def KillsCoker (H : WeierstrassHyp K' ρ b A U) (M : q → p → BK K' ρ) : Prop :=
  ∀ j : q, ∃ c : p → BK K' ρ, matrixOperator M c = Pi.single j (Welem H)

omit [FiniteDimensional ℂ P] [CompactSpace K'] [Fintype q] in
theorem matrixOperator_mul (M : q → p → BK K' ρ) (a : BK K' ρ) (v : p → BK K' ρ) :
    matrixOperator M (fun i => a * v i) = fun j => a * matrixOperator M v j := by
  funext j
  rw [matrixOperator_apply, matrixOperator_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [FiniteDimensional ℂ P] [CompactSpace K'] in
/-- If `W` kills the cokernel, `W · B(K)^q ⊆ M · B(K)^p`. -/
theorem exists_eq_Welem_mul (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) (u : q → BK K' ρ) :
    ∃ v, matrixOperator M v = fun j => Welem H * u j := by
  choose c hc using hM
  classical
  refine ⟨∑ j, fun i => u j * c j i, ?_⟩
  rw [map_sum]
  funext j'
  rw [Finset.sum_apply]
  simp only [matrixOperator_mul, hc, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j', if_pos (Finset.mem_univ _), mul_comm]

/-- **The image of `M` is the preimage of the image of `M'`.** -/
theorem mem_range_iff (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) (u : q → BK K' ρ) :
    u ∈ (matrixOperator M).range ↔
      remVec H u ∈ (matrixOperator (pushMatrix H M)).range := by
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨remVec H v, (remVec_matrixOperator H M v).symm⟩
  · rintro ⟨r, hr⟩
    have h0 : remVec H (u - matrixOperator M (polyVec K' ρ b p r)) = 0 := by
      rw [map_sub, remVec_matrixOperator, remVec_polyVec, hr, sub_self]
    obtain ⟨w, hw⟩ := (remVec_eq_zero_iff H _).mp h0
    obtain ⟨v', hv'⟩ := exists_eq_Welem_mul H hM w
    refine ⟨polyVec K' ρ b p r + v', ?_⟩
    rw [map_add, hv', ← hw, add_sub_cancel]

theorem range_eq_preimage (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) :
    ((matrixOperator M).range : Set (q → BK K' ρ)) =
      remVec H ⁻¹' ((matrixOperator (pushMatrix H M)).range : Set (q × Fin b → holSubalgebra K')) :=
  Set.ext fun u => mem_range_iff H hM u

theorem pushRange_eq_preimage (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) :
    ((matrixOperator (pushMatrix H M)).range : Set (q × Fin b → holSubalgebra K')) =
      polyVec K' ρ b q ⁻¹' ((matrixOperator M).range : Set (q → BK K' ρ)) := by
  ext r
  simp only [Set.mem_preimage, SetLike.mem_coe]
  rw [mem_range_iff H hM, remVec_polyVec]

/-- **Closed image transfers.** -/
theorem isClosed_range_iff (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) :
    IsClosed ((matrixOperator M).range : Set (q → BK K' ρ)) ↔
      IsClosed ((matrixOperator (pushMatrix H M)).range : Set (q × Fin b → holSubalgebra K')) := by
  constructor
  · intro h
    rw [pushRange_eq_preimage H hM]
    exact h.preimage (polyVec K' ρ b q).continuous
  · intro h
    rw [range_eq_preimage H hM]
    exact h.preimage (remVec H).continuous

/-- **Topologically complemented image transfers.** -/
theorem closedComplemented_range_iff (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) :
    (matrixOperator M).range.ClosedComplemented ↔
      (matrixOperator (pushMatrix H M)).range.ClosedComplemented := by
  constructor
  · rintro ⟨pr, hpr⟩
    have hmem : ∀ r, ((remVec H).comp ((matrixOperator M).range.subtypeL.comp
          (pr.comp (polyVec K' ρ b q)))) r ∈ (matrixOperator (pushMatrix H M)).range := by
      intro r
      exact (mem_range_iff H hM _).mp (pr (polyVec K' ρ b q r)).2
    refine ⟨((remVec H).comp ((matrixOperator M).range.subtypeL.comp
        (pr.comp (polyVec K' ρ b q)))).codRestrict _ hmem, fun r => ?_⟩
    apply Subtype.ext
    have hr : polyVec K' ρ b q r ∈ (matrixOperator M).range := by
      rw [mem_range_iff H hM, remVec_polyVec]
      exact r.2
    change remVec H (pr (polyVec K' ρ b q r) : q → BK K' ρ) = r
    rw [show pr (polyVec K' ρ b q r) = ⟨polyVec K' ρ b q r, hr⟩ from hpr ⟨_, hr⟩, remVec_polyVec]
  · rintro ⟨pr', hpr'⟩
    let f : (q → BK K' ρ) →L[ℂ] (q → BK K' ρ) :=
      ContinuousLinearMap.id ℂ _ - (polyVec K' ρ b q).comp
        ((remVec H) - (matrixOperator (pushMatrix H M)).range.subtypeL.comp (pr'.comp (remVec H)))
    have hfu : ∀ u, f u = u - polyVec K' ρ b q (remVec H u - (pr' (remVec H u) :
        q × Fin b → holSubalgebra K')) := fun u => rfl
    have hrem : ∀ u, remVec H (f u) = (pr' (remVec H u) : q × Fin b → holSubalgebra K') := by
      intro u
      rw [hfu, map_sub, remVec_polyVec]
      abel
    have hmem : ∀ u, f u ∈ (matrixOperator M).range := by
      intro u
      rw [mem_range_iff H hM, hrem]
      exact (pr' (remVec H u)).2
    refine ⟨f.codRestrict _ hmem, fun u => ?_⟩
    apply Subtype.ext
    change f u = u
    have hu : remVec H (u : q → BK K' ρ) ∈ (matrixOperator (pushMatrix H M)).range :=
      (mem_range_iff H hM _).mp u.2
    have hfix : (pr' (remVec H u) : q × Fin b → holSubalgebra K') = remVec H u := by
      rw [show pr' (remVec H u) = ⟨remVec H u, hu⟩ from hpr' ⟨_, hu⟩]
    rw [hfu, hfix, sub_self, map_zero, sub_zero]

/-- **The cokernels agree**: `B(K)^q / M·B(K)^p ≃ B(K')^{q×b} / M'·B(K')^{p×b}`. -/
def cokernelEquiv (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) :
    ((q → BK K' ρ) ⧸ (matrixOperator M).range) ≃ₗ[ℂ]
      ((q × Fin b → holSubalgebra K') ⧸ (matrixOperator (pushMatrix H M)).range) :=
  let g : (q → BK K' ρ) →ₗ[ℂ] ((q × Fin b → holSubalgebra K') ⧸
      (matrixOperator (pushMatrix H M)).range) :=
    (matrixOperator (pushMatrix H M)).range.mkQ ∘ₗ (remVec (q := q) H).toLinearMap
  have hker : LinearMap.ker g = (matrixOperator M).range := by
    ext u
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ContinuousLinearMap.coe_coe, ← mem_range_iff H hM]
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨polyVec K' ρ b q r, by
      rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, remVec_polyVec]⟩
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective g hsurj)

theorem cokernelEquiv_mk (H : WeierstrassHyp K' ρ b A U) {M : q → p → BK K' ρ}
    (hM : KillsCoker H M) (u : q → BK K' ρ) :
    cokernelEquiv H hM (Submodule.Quotient.mk u) = Submodule.Quotient.mk (remVec H u) := by
  rw [cokernelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ u

end
end Hironaka.HironakaG10FlatPolydiscPushforward
