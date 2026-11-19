import Hironaka.Resolution.HironakaG10FlatPolydiscPrivilege
import Mathlib.Analysis.Normed.Operator.Banach

/-! # The remainder map of Weierstrass division in `B(K' × D̄(0,ρ))`

Splits 1–2 of the privileged-neighbourhood programme (REPORT-r2, lane G10F). Under
`WeierstrassHyp K' ρ b A U` (`K' ⊆ closure (interior K')` compact, `W = w^b + ∑_{k<b} A_k w^k`
with coefficients holomorphic on an open `U ⊇ K'`, all roots of `W(z,·)` in `D(0,ρ)`), let
`K = K' × D̄(0,ρ)`.

* `pull : B(K') →ₐ B(K)`, `r ↦ r ∘ pr₁` (norm `≤ 1`, `pullCLM`); `Welem`, `wPow i`: the
  elements `W` and `wⁱ` of `B(K)`.
* `divisionEquiv`: the map `(q, r) ↦ W q + ∑_{i<b} rᵢ wⁱ` is an isomorphism of Banach spaces
  `B(K) × B(K')^b ≃L B(K)` (existence and uniqueness of the division, open mapping theorem).
* `remMap : B(K) →L B(K')^b` (the remainder), `quotMap : B(K) →L B(K)` (the quotient);
  `ker remMap = W·B(K)` (`ker_remMap`), `remMap (polyMap r) = r`, and `W·B(K)` is closed
  (`isClosed_range_mulW`) with the closed complement `B(K')[w]_{<b}` (`isCompl_range_mulW`).
* **`B(K')`-linearity** (`remMap_pull_mul`): `rem(r ∘ pr₁ · f) = r · rem(f)`; hence
  `B(K)/W·B(K)` is a free `B(K')`-module with basis `1, w, …, w^{b-1}`.
* **Multiplication matrices** (`mulMatrix`, `remMap_mul`): for every `g ∈ B(K)`,
  `rem(g f) = M(g) · rem(f)` with the `b × b` matrix `M(g)ₖₗ = remₖ(g wˡ)` over `B(K')`; in
  particular the companion matrix of `W` (`remMap_wPow_lt`, `remMap_wPow_self`:
  `rem(w^b) = -(A₀, …, A_{b-1})`).

This is the algebraic structure of the pushforward of `O/(W)` along `K → K'` at the level of
`B(K)` (Frisch 1968, Lemme 3 for `O/(W)`: the quotient is free over the base algebra), used by
`HironakaG10FlatPolydiscPushforward`. BP: hironaka-g10-flat-polydisc-remainder-map.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscRemainderMap
noncomputable section
open Classical HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision
  HironakaG10FlatPolydiscFibre HironakaG10FlatPolydiscQuotient HironakaG10FlatPolydiscPrivilege

/-! ## Evaluation and construction of elements of `B(K)` -/

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Evaluation at a point of `K`, as an algebra map `B(K) → ℂ`. -/
def evalHom (K : Set E) (x : K) : holSubalgebra K →ₐ[ℂ] ℂ where
  toFun f := (f : C(K, ℂ)) x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem evalHom_apply (K : Set E) (x : K) (f : holSubalgebra K) :
    evalHom K x f = (f : C(K, ℂ)) x := rfl

theorem ext_evalHom {K : Set E} {f g : holSubalgebra K} (h : ∀ x : K, evalHom K x f = evalHom K x g) :
    f = g := by
  apply Subtype.ext
  ext x
  exact h x

omit [NormedSpace ℂ E] in
/-- The extension by zero of a continuous function on `K` is continuous on `K`. -/
theorem continuousOn_extendZero (K : Set E) (f : C(K, ℂ)) : ContinuousOn (extendZero K f) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : K.domRestrict (extendZero K f) = f := by
    funext z
    exact extendZero_of_mem K f z.2
  rw [h]
  exact f.continuous

/-- An element of `B(K)` from a function continuous on `K` and holomorphic on `interior K`. -/
def ofContinuousOn (K : Set E) (g : E → ℂ) (hc : ContinuousOn g K)
    (hd : DifferentiableOn ℂ g (interior K)) : holSubalgebra K :=
  ⟨⟨K.domRestrict g, hc.domRestrict⟩, hd.congr fun z hz => by
      rw [extendZero_of_mem K _ (interior_subset hz)]
      rfl⟩

theorem evalHom_ofContinuousOn (K : Set E) (g : E → ℂ) (hc : ContinuousOn g K)
    (hd : DifferentiableOn ℂ g (interior K)) (x : K) :
    evalHom K x (ofContinuousOn K g hc hd) = g x := rfl

theorem evalHom_restrict (K : Set E) {U : Set E} (hKU : K ⊆ U) (F : E → ℂ)
    (hF : DifferentiableOn ℂ F U) (x : K) : evalHom K x (restrict K hKU F hF) = F x := rfl

end General

/-! ## The pullback `B(K') → B(K' × D̄(0,ρ))` -/

section Pull
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] (K' : Set P) (ρ : ℝ)

omit [NormedSpace ℂ P] in
theorem continuousOn_comp_fst (r : C(K', ℂ)) :
    ContinuousOn (fun x : P × ℂ => extendZero K' r x.1) (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  (continuousOn_extendZero K' r).comp continuous_fst.continuousOn fun _ hx => hx.1

theorem differentiableOn_comp_fst (r : holSubalgebra K') :
    DifferentiableOn ℂ (fun x : P × ℂ => extendZero K' (r : C(K', ℂ)) x.1)
      (interior (K' ×ˢ closedBall (0 : ℂ) ρ)) := by
  rw [interior_prod_eq, interior_closedBall']
  exact (mem_holSubalgebra.mp r.2).comp differentiableOn_fst fun _ hx => hx.1

/-- The pullback `B(K') → B(K' × D̄(0,ρ))`, `r ↦ r ∘ pr₁`. -/
def pull : holSubalgebra K' →ₐ[ℂ] holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) where
  toFun r := ofContinuousOn _ (fun x : P × ℂ => extendZero K' (r : C(K', ℂ)) x.1)
    (continuousOn_comp_fst K' ρ r) (differentiableOn_comp_fst K' ρ r)
  map_one' := by
    refine ext_evalHom fun x => ?_
    rw [evalHom_ofContinuousOn, map_one]
    show extendZero K' ((1 : holSubalgebra K') : C(K', ℂ)) x.1.1 = 1
    rw [extendZero_of_mem K' _ x.2.1]
    rfl
  map_mul' r s := by
    refine ext_evalHom fun x => ?_
    rw [map_mul, evalHom_ofContinuousOn, evalHom_ofContinuousOn, evalHom_ofContinuousOn]
    show extendZero K' ((r * s : holSubalgebra K') : C(K', ℂ)) x.1.1 =
      extendZero K' (r : C(K', ℂ)) x.1.1 * extendZero K' (s : C(K', ℂ)) x.1.1
    rw [extendZero_of_mem K' _ x.2.1, extendZero_of_mem K' _ x.2.1, extendZero_of_mem K' _ x.2.1]
    rfl
  map_zero' := by
    refine ext_evalHom fun x => ?_
    rw [evalHom_ofContinuousOn, map_zero]
    show extendZero K' ((0 : holSubalgebra K') : C(K', ℂ)) x.1.1 = 0
    rw [extendZero_of_mem K' _ x.2.1]
    rfl
  map_add' r s := by
    refine ext_evalHom fun x => ?_
    rw [map_add, evalHom_ofContinuousOn, evalHom_ofContinuousOn, evalHom_ofContinuousOn]
    show extendZero K' ((r + s : holSubalgebra K') : C(K', ℂ)) x.1.1 =
      extendZero K' (r : C(K', ℂ)) x.1.1 + extendZero K' (s : C(K', ℂ)) x.1.1
    rw [extendZero_of_mem K' _ x.2.1, extendZero_of_mem K' _ x.2.1, extendZero_of_mem K' _ x.2.1]
    rfl
  commutes' c := by
    refine ext_evalHom fun x => ?_
    rw [evalHom_ofContinuousOn, AlgHom.commutes]
    show extendZero K' ((algebraMap ℂ (holSubalgebra K') c : holSubalgebra K') : C(K', ℂ)) x.1.1 = c
    rw [extendZero_of_mem K' _ x.2.1]
    rfl

theorem evalHom_pull (r : holSubalgebra K') (x : K' ×ˢ closedBall (0 : ℂ) ρ) :
    evalHom _ x (pull K' ρ r) = evalHom K' ⟨x.1.1, x.2.1⟩ r := by
  show extendZero K' (r : C(K', ℂ)) x.1.1 = (r : C(K', ℂ)) ⟨x.1.1, x.2.1⟩
  exact extendZero_of_mem K' _ x.2.1

variable [CompactSpace K'] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]

theorem norm_pull_le (r : holSubalgebra K') : ‖pull K' ρ r‖ ≤ ‖r‖ := by
  rw [norm_holSubalgebra, ContinuousMap.norm_le _ (norm_nonneg _)]
  intro x
  rw [← evalHom_apply, evalHom_pull, evalHom_apply, norm_holSubalgebra]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- The pullback as a continuous linear map. -/
def pullCLM : holSubalgebra K' →L[ℂ] holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  (pull K' ρ).toLinearMap.mkContinuous 1 fun r => by
    rw [one_mul]
    exact norm_pull_le K' ρ r

theorem pullCLM_apply (r : holSubalgebra K') : pullCLM K' ρ r = pull K' ρ r := rfl

end Pull

/-! ## The division isomorphism -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  {K' : Set P} {ρ : ℝ} {b : ℕ} {A : ℕ → P → ℂ} {U : Set P}
  [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K']

/-- The element `W` of `B(K)`. -/
def Welem (H : WeierstrassHyp K' ρ b A U) : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  restrict _ (U := U ×ˢ univ) (fun _ hx => ⟨H.sub hx.1, mem_univ _⟩)
    (fun x : P × ℂ => polyEval b A x.1 x.2) (differentiableOn_polyEval b H.holo)

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem evalHom_Welem (H : WeierstrassHyp K' ρ b A U) (x : K' ×ˢ closedBall (0 : ℂ) ρ) :
    evalHom _ x (Welem H) = polyEval b A x.1.1 x.1.2 := rfl

variable (K' ρ) in
/-- The element `wⁱ` of `B(K)`. -/
def wPow (i : ℕ) : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  restrict _ (U := univ) (subset_univ _) (fun x : P × ℂ => x.2 ^ i)
    (differentiableOn_snd.pow i)

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem evalHom_wPow (i : ℕ) (x : K' ×ˢ closedBall (0 : ℂ) ρ) :
    evalHom _ x (wPow K' ρ i) = x.1.2 ^ i := rfl

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem wPow_add (i j : ℕ) : wPow K' ρ (i + j) = wPow K' ρ i * wPow K' ρ j :=
  ext_evalHom fun x => by rw [map_mul, evalHom_wPow, evalHom_wPow, evalHom_wPow, pow_add]

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem wPow_zero : wPow K' ρ 0 = 1 :=
  ext_evalHom fun x => by rw [map_one, evalHom_wPow, pow_zero]

/-- The polynomial `∑_{i<b} rᵢ wⁱ` with coefficients in `B(K')`. -/
def polySum (b : ℕ) (r : ℕ → holSubalgebra K') : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  ∑ i ∈ Finset.range b, pull K' ρ (r i) * wPow K' ρ i

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem evalHom_polySum (r : ℕ → holSubalgebra K') (x : K' ×ˢ closedBall (0 : ℂ) ρ) :
    evalHom _ x (polySum (ρ := ρ) b r) =
      ∑ i ∈ Finset.range b, ((r i : holSubalgebra K') : C(K', ℂ)) ⟨x.1.1, x.2.1⟩ * x.1.2 ^ i := by
  rw [polySum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, evalHom_pull, evalHom_wPow]; rfl

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem polySum_add (r s : ℕ → holSubalgebra K') :
    polySum (ρ := ρ) b (r + s) = polySum (ρ := ρ) b r + polySum (ρ := ρ) b s := by
  simp only [polySum, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem pull_mul_polySum (s : holSubalgebra K') (r : ℕ → holSubalgebra K') :
    pull K' ρ s * polySum (ρ := ρ) b r = polySum (ρ := ρ) b (fun i => s * r i) := by
  simp only [polySum, Finset.mul_sum, map_mul, mul_assoc]

omit [CompactSpace K'] in
/-- **The division identity in `B(K)`.** -/
theorem eq_division (H : WeierstrassHyp K' ρ b A U) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    f = Welem H * quotientElem H f + polySum b (remElem H f) := by
  refine ext_evalHom fun x => ?_
  rw [map_add, map_mul, evalHom_Welem, evalHom_polySum, evalHom_apply, evalHom_apply]
  exact exists_division H f x

omit [CompactSpace K'] in
/-- **Uniqueness of the division in `B(K)`.** -/
theorem division_unique (H : WeierstrassHyp K' ρ b A U)
    (f q : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (r : ℕ → holSubalgebra K')
    (h : f = Welem H * q + polySum b r) :
    q = quotientElem H f ∧ ∀ i < b, r i = remElem H f i := by
  refine division_unique_B H f q r fun x => ?_
  have := congrArg (evalHom _ x) h
  rw [map_add, map_mul, evalHom_Welem, evalHom_polySum, evalHom_apply, evalHom_apply] at this
  exact this

omit [CompactSpace K'] in
/-- Two divisions with the same value agree. -/
theorem division_inj (H : WeierstrassHyp K' ρ b A U)
    (q₁ q₂ : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (r₁ r₂ : ℕ → holSubalgebra K')
    (h : Welem H * q₁ + polySum b r₁ = Welem H * q₂ + polySum b r₂) :
    q₁ = q₂ ∧ ∀ i < b, r₁ i = r₂ i := by
  obtain ⟨h1, h2⟩ := division_unique H _ q₁ r₁ rfl
  obtain ⟨h3, h4⟩ := division_unique H _ q₂ r₂ h
  exact ⟨h1.trans h3.symm, fun i hi => (h2 i hi).trans (h4 i hi).symm⟩

/-- Extension of a `Fin b`-indexed family by zero. -/
def extFin (r : Fin b → holSubalgebra K') : ℕ → holSubalgebra K' :=
  fun i => if hi : i < b then r ⟨i, hi⟩ else 0

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]
  [CompactSpace K'] in
theorem extFin_val (r : Fin b → holSubalgebra K') (i : Fin b) : extFin r i = r i := by
  rw [extFin, dif_pos i.2]

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem polySum_extFin (r : Fin b → holSubalgebra K') :
    polySum (ρ := ρ) b (extFin r) = ∑ i : Fin b, pull K' ρ (r i) * wPow K' ρ i := by
  rw [polySum, ← Fin.sum_univ_eq_sum_range (fun i => pull K' ρ (extFin r i) * wPow K' ρ i) b]
  exact Finset.sum_congr rfl fun i _ => by rw [extFin_val]

variable (K' ρ b) in
/-- `r ↦ ∑_{i<b} rᵢ wⁱ` as a continuous linear map `B(K')^b → B(K)`. -/
def polyMap : (Fin b → holSubalgebra K') →L[ℂ] holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  ∑ i : Fin b, ((ContinuousLinearMap.mul ℂ (holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))).flip
    (wPow K' ρ i)).comp ((pullCLM K' ρ).comp (ContinuousLinearMap.proj i))

omit [FiniteDimensional ℂ P] in
theorem polyMap_apply (r : Fin b → holSubalgebra K') :
    polyMap K' ρ b r = polySum b (extFin r) := by
  rw [polySum_extFin, polyMap, _root_.sum_apply]
  rfl

/-- The division map `(q, r) ↦ W q + ∑_{i<b} rᵢ wⁱ`. -/
def divisionMap (H : WeierstrassHyp K' ρ b A U) :
    (holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) × (Fin b → holSubalgebra K')) →L[ℂ]
      holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  (ContinuousLinearMap.mul ℂ _ (Welem H)).comp (ContinuousLinearMap.fst ℂ _ _) +
    (polyMap K' ρ b).comp (ContinuousLinearMap.snd ℂ _ _)

omit [FiniteDimensional ℂ P] in
theorem divisionMap_apply (H : WeierstrassHyp K' ρ b A U)
    (x : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) × (Fin b → holSubalgebra K')) :
    divisionMap H x = Welem H * x.1 + polySum b (extFin x.2) := by
  rw [← polyMap_apply]
  rfl

theorem divisionMap_injective (H : WeierstrassHyp K' ρ b A U) :
    Function.Injective (divisionMap H) := by
  intro x y hxy
  rw [divisionMap_apply, divisionMap_apply] at hxy
  obtain ⟨h1, h2⟩ := division_inj H _ _ _ _ hxy
  refine Prod.ext h1 (funext fun i => ?_)
  have := h2 i i.2
  rwa [extFin_val, extFin_val] at this

theorem divisionMap_surjective (H : WeierstrassHyp K' ρ b A U) :
    Function.Surjective (divisionMap H) := by
  intro f
  refine ⟨(quotientElem H f, fun i => remElem H f i), ?_⟩
  rw [divisionMap_apply]
  refine Eq.trans ?_ (eq_division H f).symm
  dsimp only
  congr 1
  rw [polySum, polySum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [extFin, dif_pos (Finset.mem_range.mp hi)]

/-- **The division isomorphism** `B(K) × B(K')^b ≃L B(K)`, `(q, r) ↦ W q + ∑_{i<b} rᵢ wⁱ`
(Banach isomorphism by the open mapping theorem). -/
def divisionEquiv (H : WeierstrassHyp K' ρ b A U) :
    (holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) × (Fin b → holSubalgebra K')) ≃L[ℂ]
      holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  ContinuousLinearEquiv.ofBijective (divisionMap H)
    (LinearMap.ker_eq_bot.mpr (divisionMap_injective H))
    (LinearMap.range_eq_top.mpr (divisionMap_surjective H))

theorem divisionEquiv_apply (H : WeierstrassHyp K' ρ b A U)
    (x : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) × (Fin b → holSubalgebra K')) :
    divisionEquiv H x = divisionMap H x := rfl

/-! ## The remainder and quotient maps -/

/-- The remainder map `B(K) →L B(K')^b`. -/
def remMap (H : WeierstrassHyp K' ρ b A U) :
    holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) →L[ℂ] (Fin b → holSubalgebra K') :=
  (ContinuousLinearMap.snd ℂ _ _).comp (divisionEquiv H).symm.toContinuousLinearMap

/-- The quotient map `B(K) →L B(K)`. -/
def quotMap (H : WeierstrassHyp K' ρ b A U) :
    holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) →L[ℂ] holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  (ContinuousLinearMap.fst ℂ _ _).comp (divisionEquiv H).symm.toContinuousLinearMap

theorem remMap_divisionMap (H : WeierstrassHyp K' ρ b A U)
    (x : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) × (Fin b → holSubalgebra K')) :
    remMap H (divisionMap H x) = x.2 := by
  change ((divisionEquiv H).symm (divisionEquiv H x)).2 = x.2
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem quotMap_divisionMap (H : WeierstrassHyp K' ρ b A U)
    (x : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) × (Fin b → holSubalgebra K')) :
    quotMap H (divisionMap H x) = x.1 := by
  change ((divisionEquiv H).symm (divisionEquiv H x)).1 = x.1
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem divisionMap_quot_rem (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    divisionMap H (quotMap H f, remMap H f) = f := by
  change divisionEquiv H ((divisionEquiv H).symm f) = f
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- `f = W · quot f + ∑_{i<b} remᵢ f · wⁱ`. -/
theorem eq_quot_rem (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    f = Welem H * quotMap H f + polyMap K' ρ b (remMap H f) := by
  conv_lhs => rw [← divisionMap_quot_rem H f]
  rfl

/-- The remainder map is the Cauchy remainder. -/
theorem remMap_apply (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (i : Fin b) :
    remMap H f i = remElem H f i := by
  have h := eq_quot_rem H f
  rw [polyMap_apply] at h
  have := (division_unique H f _ _ h).2 i i.2
  rwa [extFin_val] at this

theorem quotMap_apply (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) : quotMap H f = quotientElem H f := by
  have h := eq_quot_rem H f
  rw [polyMap_apply] at h
  exact (division_unique H f _ _ h).1

theorem remMap_polyMap (H : WeierstrassHyp K' ρ b A U) (r : Fin b → holSubalgebra K') :
    remMap H (polyMap K' ρ b r) = r := by
  have : polyMap K' ρ b r = divisionMap H (0, r) := by
    rw [divisionMap_apply, mul_zero, zero_add, polyMap_apply]
  rw [this, remMap_divisionMap]

theorem remMap_Welem_mul (H : WeierstrassHyp K' ρ b A U)
    (q : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) : remMap H (Welem H * q) = 0 := by
  have : Welem H * q = divisionMap H (q, 0) := by
    rw [divisionMap_apply]
    have h0 : extFin (b := b) (0 : Fin b → holSubalgebra K') = 0 := by
      funext i
      simp only [extFin, Pi.zero_apply, dite_eq_ite, ite_self]
    rw [h0, polySum]
    simp
  rw [this, remMap_divisionMap]

theorem quotMap_Welem_mul (H : WeierstrassHyp K' ρ b A U)
    (q : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) : quotMap H (Welem H * q) = q := by
  have : Welem H * q = divisionMap H (q, 0) := by
    rw [divisionMap_apply]
    have h0 : extFin (b := b) (0 : Fin b → holSubalgebra K') = 0 := by
      funext i
      simp only [extFin, Pi.zero_apply, dite_eq_ite, ite_self]
    rw [h0, polySum]
    simp
  rw [this, quotMap_divisionMap]

/-- The kernel of the remainder map is `W · B(K)`. -/
theorem remMap_eq_zero_iff (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    remMap H f = 0 ↔ ∃ q, f = Welem H * q := by
  constructor
  · intro h
    refine ⟨quotMap H f, ?_⟩
    conv_lhs => rw [eq_quot_rem H f, h, map_zero, add_zero]
  · rintro ⟨q, rfl⟩
    exact remMap_Welem_mul H q

/-- Multiplication by `W` on `B(K)`. -/
def mulW (H : WeierstrassHyp K' ρ b A U) :
    holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) →L[ℂ] holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  ContinuousLinearMap.mul ℂ _ (Welem H)

theorem ker_remMap (H : WeierstrassHyp K' ρ b A U) :
    (remMap H).ker = (mulW H).range := by
  ext f
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  rw [remMap_eq_zero_iff]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩

theorem mulW_injective (H : WeierstrassHyp K' ρ b A U) : Function.Injective (mulW H) := by
  intro q₁ q₂ h
  have h' : Welem H * q₁ = Welem H * q₂ := h
  rw [← quotMap_Welem_mul H q₁, h', quotMap_Welem_mul]

/-- **Privilege of `K` for `O/(W)`, topological form**: `W · B(K)` is closed. -/
theorem isClosed_range_mulW (H : WeierstrassHyp K' ρ b A U) :
    IsClosed ((mulW H).range : Set (holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))) := by
  rw [← ker_remMap]
  exact (remMap H).isClosed_ker

/-- **`W · B(K)` and `B(K')[w]_{<b}` are complementary.** -/
theorem isCompl_range_mulW (H : WeierstrassHyp K' ρ b A U) :
    IsCompl (mulW H).range (polyMap K' ρ b).range := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro f ⟨q, rfl⟩ ⟨r, hr⟩
    simp only [ContinuousLinearMap.coe_coe] at hr ⊢
    have h1 : remMap H (mulW H q) = 0 := remMap_Welem_mul H q
    rw [← hr, remMap_polyMap] at h1
    rw [← hr, h1, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    rw [eq_quot_rem H f]
    exact Submodule.add_mem_sup ⟨quotMap H f, rfl⟩ ⟨remMap H f, rfl⟩

/-! ## `B(K')`-linearity and multiplication matrices -/

/-- **`B(K')`-linearity of the remainder**: `rem(r ∘ pr₁ · f) = r · rem(f)`. -/
theorem remMap_pull_mul (H : WeierstrassHyp K' ρ b A U) (s : holSubalgebra K')
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    remMap H (pull K' ρ s * f) = fun i => s * remMap H f i := by
  have h : pull K' ρ s * f = divisionMap H (pull K' ρ s * quotMap H f, fun i => s * remMap H f i) := by
    conv_lhs => rw [eq_quot_rem H f]
    rw [divisionMap_apply, mul_add, polyMap_apply, pull_mul_polySum, ← mul_assoc,
      mul_comm (pull K' ρ s) (Welem H), mul_assoc]
    congr 2
    funext i
    simp only [extFin]
    split_ifs <;> simp
  rw [h, remMap_divisionMap]

/-- The multiplication matrix of `g ∈ B(K)` on `B(K)/W·B(K) ≅ B(K')^b`:
`M(g)ₖₗ = remₖ(g wˡ)`. -/
def mulMatrix (H : WeierstrassHyp K' ρ b A U) (g : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    Matrix (Fin b) (Fin b) (holSubalgebra K') :=
  fun k l => remMap H (g * wPow K' ρ l) k

/-- **The remainder of a product**: `rem(g f) = M(g) · rem(f)`. -/
theorem remMap_mul (H : WeierstrassHyp K' ρ b A U) (g f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    remMap H (g * f) = (mulMatrix H g).mulVec (remMap H f) := by
  have hf := eq_quot_rem H f
  have hpoly : polyMap K' ρ b (remMap H f) = ∑ l : Fin b, pull K' ρ (remMap H f l) * wPow K' ρ l := by
    rw [polyMap_apply, polySum_extFin]
  conv_lhs => rw [hf, mul_add, hpoly, Finset.mul_sum, map_add, map_sum,
    show g * (Welem H * quotMap H f) = Welem H * (g * quotMap H f) by ring, remMap_Welem_mul,
    zero_add]
  funext k
  simp only [Matrix.mulVec, dotProduct, mulMatrix, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show g * (pull K' ρ (remMap H f l) * wPow K' ρ l) =
    pull K' ρ (remMap H f l) * (g * wPow K' ρ l) by ring, remMap_pull_mul]
  exact mul_comm _ _

/-- The multiplication matrix of a pulled-back element is scalar. -/
theorem mulMatrix_pull (H : WeierstrassHyp K' ρ b A U) (s : holSubalgebra K') :
    mulMatrix H (pull K' ρ s) = Matrix.diagonal fun _ => s := by
  funext k l
  rw [mulMatrix, remMap_pull_mul]
  have hl : wPow K' ρ l = polyMap K' ρ b (Pi.single l 1) := by
    rw [polyMap_apply, polySum_extFin, Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, map_one, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ l) h
  rw [hl, remMap_polyMap, Matrix.diagonal_apply]
  dsimp only
  by_cases hkl : k = l
  · subst hkl
    rw [Pi.single_eq_same, if_pos rfl, mul_one]
  · rw [Pi.single_eq_of_ne hkl, if_neg hkl, mul_zero]

/-- `rem(wⁱ) = eᵢ` for `i < b`. -/
theorem remMap_wPow_lt (H : WeierstrassHyp K' ρ b A U) (i : Fin b) :
    remMap H (wPow K' ρ i) = Pi.single i 1 := by
  have hl : wPow K' ρ i = polyMap K' ρ b (Pi.single i 1) := by
    rw [polyMap_apply, polySum_extFin, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, map_one, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hl, remMap_polyMap]

/-- The coefficient `A_k` of `W` as an element of `B(K')`. -/
def Aelem (H : WeierstrassHyp K' ρ b A U) (k : ℕ) : holSubalgebra K' :=
  restrict K' H.sub (A k) (H.holo k)

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem Welem_eq (H : WeierstrassHyp K' ρ b A U) :
    Welem H = wPow K' ρ b + polySum b (Aelem H) := by
  refine ext_evalHom fun x => ?_
  rw [map_add, evalHom_Welem, evalHom_wPow, evalHom_polySum, polyEval, Finset.sum_range_succ,
    H.monic x.1.1 (H.sub x.2.1), one_mul, add_comm]
  rfl

/-- **The companion relation**: `rem(w^b) = -(A₀, …, A_{b-1})`. -/
theorem remMap_wPow_self (H : WeierstrassHyp K' ρ b A U) :
    remMap H (wPow K' ρ b) = fun i : Fin b => -Aelem H i := by
  have h : wPow K' ρ b = divisionMap H (1, fun i : Fin b => -Aelem H i) := by
    rw [divisionMap_apply, mul_one, Welem_eq H]
    have : extFin (fun i : Fin b => -Aelem H i) = fun i => if i < b then -Aelem H i else 0 := by
      funext i
      simp only [extFin]
      split_ifs <;> rfl
    rw [this, add_assoc, ← polySum_add]
    have h0 : (Aelem H + fun i => if i < b then -Aelem H i else 0) =
        fun i => if i < b then 0 else Aelem H i := by
      funext i
      simp only [Pi.add_apply]
      split_ifs <;> simp
    rw [h0, polySum, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi), map_zero, zero_mul]
  rw [h, remMap_divisionMap]

end
end Hironaka.HironakaG10FlatPolydiscRemainderMap
