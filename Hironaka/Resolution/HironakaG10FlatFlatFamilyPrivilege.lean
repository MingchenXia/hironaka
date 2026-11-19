import Hironaka.Resolution.HironakaG10FlatPolydiscSlice
import Hironaka.Resolution.HironakaG10FlatComplexPersistence
import Hironaka.Resolution.HironakaG10FlatResolutionStart
import Hironaka.Resolution.HironakaG10FlatPolydiscParametric

/-! # Douady's Proposition 6 (a), Banach core: privilege of `K' × D̄(0,ρ)` from the fibre at `0`

Douady 1966, §7 n° 3, Prop. 6 (a): for a sheaf flat over a line, if `K'` is privileged for the fibre at
`w = 0`, then `K' × D̄(0,ρ)` is privileged for small `ρ`. Proof: the `B(K')`-complexes of the fibres
form a holomorphic family which is direct exact at `0`, hence has holomorphic generalized inverses
near `0` (`HironakaG10FlatComplexPersistence`); slicewise application and gluing
(`HironakaG10FlatPolydiscSlice`) give generalized inverses and exactness over `B(K' × D̄(0,ρ))`.

* `sliceVec`, `sliceMat`, `sliceVec_matrixOperator` (a `B(K)`-matrix acts slicewise),
  `eq_of_sliceVec`, `glueVec`, `sliceVec_glueVec`.
* `glueOp hK' hρ hρρ' R hR`: a family `R(w)` of operators on `B(K')`-vectors holomorphic on
  `D(0,ρ')`, `ρ < ρ'`, acting slicewise, as a bounded operator on `B(K)`-vectors (`sliceVec_glueOp`).
* `generalizedInverse_of_slices`, `exact_of_slices`, **`directExact_of_slices`**: fibrewise
  holomorphic generalized inverses and fibrewise exactness on `D̄(0,ρ)` give a `DirectExact` start
  over `B(K' × D̄(0,ρ))`.
* **`eventually_directExact_polydisc`** (Prop. 6 (a) for a start): holomorphic matrices
  `L₂ →d₂ L₁ →d₁ L₀` near `{0} × K'` with `d₁ d₂ = 0`; if the `B(K')`-operators `D₂(w)` have
  holomorphic generalized inverses near `w = 0` (what the descending induction provides from the
  higher degrees of a finite resolution) and at `w = 0` the `B(K')`-complex is exact at `L₁` with
  `D₁(0)` direct, then for all small `ρ > 0` the restricted start over `B(K' × D̄(0,ρ))` is
  `DirectExact`.
NOT formalized: the sheaf-level input (flatness ⇒ the restrictions of a resolution resolve the fibres).
BP: hironaka-g10-flat-flat-family-privilege.tex. -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatFlatFamilyPrivilege
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscSlice HironakaG10FlatResolutionStart
  HironakaG10FlatGeneralizedInverse

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {K' : Set P} [CompactSpace K']
  {ρ : ℝ} [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] {ι ι₀ ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₀]
  [Fintype ι₁] [Fintype ι₂]

/-! ## Slices and gluing of vectors -/

/-- The slice of a vector. -/
def sliceVec (hρ : 0 < ρ) (v : ι → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (w : ℂ) :
    ι → holSubalgebra K' := fun i => sliceB hρ (v i) w

/-- The slice of a matrix. -/
def sliceMat (hρ : 0 < ρ) (M : ι₀ → ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (w : ℂ) :
    ι₀ → ι₁ → holSubalgebra K' := fun i j => sliceB hρ (M i j) w

omit [Fintype ι] [CompactSpace K'] in
theorem sliceVec_add (hρ : 0 < ρ) (v v' : ι → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (w : ℂ) :
    sliceVec hρ (v + v') w = sliceVec hρ v w + sliceVec hρ v' w :=
  funext fun i => sliceB_add hρ (v i) (v' i) w

omit [Fintype ι] [CompactSpace K'] in
theorem sliceVec_smul (hρ : 0 < ρ) (c : ℂ) (v : ι → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (w : ℂ) : sliceVec hρ (c • v) w = c • sliceVec hρ v w :=
  funext fun i => sliceB_smul hρ c (v i) w

omit [Fintype ι₀] in
/-- **A `B(K)`-matrix acts slicewise.** -/
theorem sliceVec_matrixOperator (hρ : 0 < ρ) (M : ι₀ → ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (v : ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ) :
    sliceVec hρ (matrixOperator M v) w = matrixOperator (sliceMat hρ M w) (sliceVec hρ v w) := by
  funext i
  simp only [sliceVec, matrixOperator_apply, sliceMat]
  rw [← sliceL_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sliceL_apply, sliceB_mul hρ _ _ hw]

omit [Fintype ι] [CompactSpace K'] in
/-- Elements of `B(K)` are determined by their slices over the closed disc. -/
theorem eq_of_sliceB (hρ : 0 < ρ) {f g : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)}
    (h : ∀ w ∈ closedBall (0 : ℂ) ρ, sliceB hρ f w = sliceB hρ g w) : f = g := by
  apply Subtype.ext; apply ContinuousMap.ext; intro q
  have := congrArg (fun F : holSubalgebra K' => (F : C(K', ℂ)) ⟨q.1.1, q.2.1⟩) (h q.1.2 q.2.2)
  simp only [sliceB_apply hρ _ q.2.2] at this
  exact this

omit [Fintype ι] [CompactSpace K'] in
theorem eq_of_sliceVec (hρ : 0 < ρ) {v v' : ι → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)}
    (h : ∀ w ∈ closedBall (0 : ℂ) ρ, sliceVec hρ v w = sliceVec hρ v' w) : v = v' :=
  funext fun i => eq_of_sliceB hρ fun w hw => congrFun (h w hw) i

/-- Gluing a vector-valued map. -/
def glueVec (hρ : 0 < ρ) {G : ℂ → ι → holSubalgebra K'} (hG : ContinuousOn G (closedBall (0 : ℂ) ρ))
    (hG' : DifferentiableOn ℂ G (ball 0 ρ)) : ι → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  fun i => glueB hρ (continuousOn_pi.1 hG i) (differentiableOn_pi.1 hG' i)

omit [Fintype ι] in
theorem sliceVec_glueVec (hρ : 0 < ρ) {G : ℂ → ι → holSubalgebra K'}
    (hG : ContinuousOn G (closedBall (0 : ℂ) ρ)) (hG' : DifferentiableOn ℂ G (ball 0 ρ)) {w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) ρ) : sliceVec hρ (glueVec hρ hG hG') w = G w :=
  funext fun _ => sliceB_glueB hρ _ _ hw

/-! ## Gluing an operator family -/

section Glue

section Abstract
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

theorem continuousOn_clm_apply {ρ ρ' : ℝ} (hρρ' : ρ < ρ') {R : ℂ → E →L[ℂ] F}
    (hR : DifferentiableOn ℂ R (ball 0 ρ')) {g : ℂ → E} (hg : ContinuousOn g (closedBall 0 ρ)) :
    ContinuousOn (fun w => R w (g w)) (closedBall (0 : ℂ) ρ) :=
  (hR.continuousOn.mono (closedBall_subset_ball hρρ')).clm_apply hg

theorem differentiableOn_clm_apply {ρ ρ' : ℝ} (hρρ' : ρ < ρ') {R : ℂ → E →L[ℂ] F}
    (hR : DifferentiableOn ℂ R (ball 0 ρ')) {g : ℂ → E} (hg : DifferentiableOn ℂ g (ball 0 ρ)) :
    DifferentiableOn ℂ (fun w => R w (g w)) (ball (0 : ℂ) ρ) :=
  (hR.mono (ball_subset_ball hρρ'.le)).clm_apply hg

theorem exists_bound_clm {ρ ρ' : ℝ} (hρρ' : ρ < ρ') {R : ℂ → E →L[ℂ] F}
    (hR : DifferentiableOn ℂ R (ball 0 ρ')) :
    ∃ C, 0 ≤ C ∧ ∀ w ∈ closedBall (0 : ℂ) ρ, ‖R w‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    (hR.continuousOn.mono (closedBall_subset_ball hρρ'))
  exact ⟨max C 0, le_max_right _ _, fun w hw => (hC w hw).trans (le_max_left _ _)⟩

end Abstract

/-- The glued vector `w ↦ R(w) x(·,w)`. -/
def glueFn (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) {ρ' : ℝ} (hρρ' : ρ < ρ')
    (R : ℂ → (ι₀ → holSubalgebra K') →L[ℂ] (ι₁ → holSubalgebra K'))
    (hR : DifferentiableOn ℂ R (ball 0 ρ')) (x : ι₀ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  glueVec hρ (continuousOn_clm_apply hρρ' hR (continuousOn_pi.2 fun i => continuousOn_sliceB hρ (x i)))
    (differentiableOn_clm_apply hρρ' hR
      (differentiableOn_pi.2 fun i => differentiableOn_sliceB hK' hρ (x i)))

theorem sliceVec_glueFn (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) {ρ' : ℝ} (hρρ' : ρ < ρ')
    (R : ℂ → (ι₀ → holSubalgebra K') →L[ℂ] (ι₁ → holSubalgebra K'))
    (hR : DifferentiableOn ℂ R (ball 0 ρ')) (x : ι₀ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ) :
    sliceVec hρ (glueFn hK' hρ hρρ' R hR x) w = R w (sliceVec hρ x w) :=
  sliceVec_glueVec hρ
    (continuousOn_clm_apply hρρ' hR (continuousOn_pi.2 fun i => continuousOn_sliceB hρ (x i)))
    (differentiableOn_clm_apply hρρ' hR
      (differentiableOn_pi.2 fun i => differentiableOn_sliceB hK' hρ (x i))) hw

/-- **The slicewise operator `x ↦ (w ↦ R(w) x(·,w))`, glued**, as a bounded operator on
`B(K)`-vectors. -/
def glueOp (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) {ρ' : ℝ} (hρρ' : ρ < ρ')
    (R : ℂ → (ι₀ → holSubalgebra K') →L[ℂ] (ι₁ → holSubalgebra K'))
    (hR : DifferentiableOn ℂ R (ball 0 ρ')) : (ι₀ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) →L[ℂ]
    (ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :=
  LinearMap.mkContinuous
    { toFun := glueFn hK' hρ hρρ' R hR
      map_add' := fun x y => eq_of_sliceVec hρ fun w hw => by
        rw [sliceVec_add, sliceVec_glueFn hK' hρ hρρ' R hR _ hw,
          sliceVec_glueFn hK' hρ hρρ' R hR _ hw, sliceVec_glueFn hK' hρ hρρ' R hR _ hw,
          sliceVec_add, map_add]
      map_smul' := fun c x => eq_of_sliceVec hρ fun w hw => by
        rw [RingHom.id_apply, sliceVec_smul, sliceVec_glueFn hK' hρ hρρ' R hR _ hw,
          sliceVec_glueFn hK' hρ hρρ' R hR _ hw, sliceVec_smul, map_smul] }
    (exists_bound_clm (ρ := ρ) hρρ' hR).choose fun x => by
      obtain ⟨hC0, hC⟩ := (exists_bound_clm (ρ := ρ) hρρ' hR).choose_spec
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      refine norm_glueB_le hρ (G := fun w => R w (sliceVec hρ x w) i)
        (continuousOn_pi.1 (continuousOn_clm_apply hρρ' hR
          (continuousOn_pi.2 fun i => continuousOn_sliceB hρ (x i))) i)
        (differentiableOn_pi.1 (differentiableOn_clm_apply hρρ' hR
          (differentiableOn_pi.2 fun i => differentiableOn_sliceB hK' hρ (x i))) i)
        (by positivity) fun w hw => ?_
      have h1 : ‖R w (sliceVec hρ x w) i‖ ≤ ‖R w (sliceVec hρ x w)‖ := norm_le_pi_norm _ i
      have h2 : ‖sliceVec hρ x w‖ ≤ ‖x‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j =>
          (norm_sliceB_le hρ (x j) w).trans (norm_le_pi_norm x j)
      calc ‖R w (sliceVec hρ x w) i‖ ≤ ‖R w‖ * ‖sliceVec hρ x w‖ := h1.trans ((R w).le_opNorm _)
        _ ≤ _ * ‖x‖ := mul_le_mul (hC w hw) h2 (norm_nonneg _) hC0

theorem sliceVec_glueOp (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) {ρ' : ℝ} (hρρ' : ρ < ρ')
    (R : ℂ → (ι₀ → holSubalgebra K') →L[ℂ] (ι₁ → holSubalgebra K'))
    (hR : DifferentiableOn ℂ R (ball 0 ρ')) (x : ι₀ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ) :
    sliceVec hρ (glueOp hK' hρ hρρ' R hR x) w = R w (sliceVec hρ x w) :=
  sliceVec_glueFn hK' hρ hρρ' R hR x hw

end Glue

/-! ## Transfer of generalized inverses and exactness -/

/-- **Fibrewise holomorphic generalized inverses glue to a generalized inverse over `B(K)`.** -/
theorem generalizedInverse_of_slices (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) {ρ' : ℝ}
    (hρρ' : ρ < ρ') (M : ι₀ → ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (R : ℂ → (ι₀ → holSubalgebra K') →L[ℂ] (ι₁ → holSubalgebra K'))
    (hR : DifferentiableOn ℂ R (ball 0 ρ'))
    (hRM : ∀ w ∈ closedBall (0 : ℂ) ρ, ∀ x, matrixOperator (sliceMat hρ M w)
      (R w (matrixOperator (sliceMat hρ M w) x)) = matrixOperator (sliceMat hρ M w) x)
    (v : ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    matrixOperator M (glueOp hK' hρ hρρ' R hR (matrixOperator M v)) = matrixOperator M v := by
  refine eq_of_sliceVec hρ fun w hw => ?_
  rw [sliceVec_matrixOperator hρ _ _ hw, sliceVec_glueOp _ _ _ _ _ _ hw,
    sliceVec_matrixOperator hρ _ _ hw, hRM w hw]

omit [Fintype ι₀] in
/-- **Fibrewise exactness with holomorphic preimages gives exactness over `B(K)`.** -/
theorem exact_of_slices (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) {ρ' : ℝ} (hρρ' : ρ < ρ')
    (g : ι₁ → ι₂ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (f : ι₀ → ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (R : ℂ → (ι₁ → holSubalgebra K') →L[ℂ] (ι₂ → holSubalgebra K'))
    (hR : DifferentiableOn ℂ R (ball 0 ρ'))
    (hex : ∀ w ∈ closedBall (0 : ℂ) ρ, ∀ x, matrixOperator (sliceMat hρ f w) x = 0 →
      matrixOperator (sliceMat hρ g w) (R w x) = x)
    (v : ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (hv : matrixOperator f v = 0) :
    ∃ t, matrixOperator g t = v := by
  refine ⟨glueOp hK' hρ hρρ' R hR v, eq_of_sliceVec hρ fun w hw => ?_⟩
  rw [sliceVec_matrixOperator hρ _ _ hw, sliceVec_glueOp _ _ _ _ _ _ hw]
  refine hex w hw _ ?_
  rw [← sliceVec_matrixOperator hρ _ _ hw, hv]
  funext i
  exact (sliceL hρ w).map_zero

/-- **Douady §7 Prop. 6 (a), transfer step**: if `g`, `f` over `B(K' × D̄(0,ρ))` satisfy `f g = 0`
and their slices have holomorphic generalized inverses on `D(0,ρ')` (`ρ < ρ'`) and are exact on
`D̄(0,ρ)`, then `(g, f)` is a `DirectExact` start. -/
theorem directExact_of_slices (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) {ρ' : ℝ}
    (hρρ' : ρ < ρ') {g : ι₁ → ι₂ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)}
    {f : ι₀ → ι₁ → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)}
    (hfg : ∀ i k, ∑ j, f i j * g j k = 0)
    {R₂ : ℂ → (ι₁ → holSubalgebra K') →L[ℂ] (ι₂ → holSubalgebra K')}
    {R₁ : ℂ → (ι₀ → holSubalgebra K') →L[ℂ] (ι₁ → holSubalgebra K')}
    (hR₂ : DifferentiableOn ℂ R₂ (ball 0 ρ')) (hR₁ : DifferentiableOn ℂ R₁ (ball 0 ρ'))
    (hgi₂ : ∀ w ∈ closedBall (0 : ℂ) ρ, ∀ x, matrixOperator (sliceMat hρ g w)
      (R₂ w (matrixOperator (sliceMat hρ g w) x)) = matrixOperator (sliceMat hρ g w) x)
    (hgi₁ : ∀ w ∈ closedBall (0 : ℂ) ρ, ∀ x, matrixOperator (sliceMat hρ f w)
      (R₁ w (matrixOperator (sliceMat hρ f w) x)) = matrixOperator (sliceMat hρ f w) x)
    (hex : ∀ w ∈ closedBall (0 : ℂ) ρ, ∀ x, matrixOperator (sliceMat hρ f w) x = 0 →
      ∃ u, matrixOperator (sliceMat hρ g w) u = x) :
    DirectExact g f := by
  have hS₁ := generalizedInverse_of_slices hK' hρ hρρ' f R₁ hR₁ hgi₁
  have hS₂ := generalizedInverse_of_slices hK' hρ hρρ' g R₂ hR₂ hgi₂
  refine ⟨hfg, exact_of_slices hK' hρ hρρ' g f R₂ hR₂ (fun w hw x hx => ?_),
    closedComplemented_ker_of_generalizedInverse _ _ hS₁,
    closedComplemented_range_of_generalizedInverse _ _ hS₁,
    closedComplemented_ker_of_generalizedInverse _ _ hS₂⟩
  obtain ⟨u, rfl⟩ := hex w hw x hx
  exact hgi₂ w hw u

/-! ## Douady's Prop. 6 (a) for a start of a resolution -/

section Assembly
open HironakaG10FlatPolydiscParametric HironakaG10FlatComplexPersistence
variable [FiniteDimensional ℂ P]

/-- A matrix of functions of `(w, z)`, as functions of `(z, w)`. -/
def swapMat {κ ι : Type*} (d : κ → ι → ℂ × P → ℂ) : κ → ι → P × ℂ → ℂ :=
  fun i j q => d i j (q.2, q.1)

omit [CompactSpace K'] [FiniteDimensional ℂ P] in
theorem differentiableOn_swapMat {κ ι : Type*} {O : Set (ℂ × P)} {d : κ → ι → ℂ × P → ℂ}
    (hd : ∀ i j, DifferentiableOn ℂ (d i j) O) (i : κ) (j : ι) :
    DifferentiableOn ℂ (swapMat d i j) (Prod.swap ⁻¹' O) :=
  (hd i j).comp (differentiableOn_snd.prodMk differentiableOn_fst) fun _ hq => hq

omit [FiniteDimensional ℂ P] [CompactSpace K'] in
/-- The slices of the restriction of a holomorphic matrix are the restrictions of its slices. -/
theorem sliceMat_restrictMatrix (hρ : 0 < ρ) {κ ι : Type*} {O : Set (ℂ × P)}
    {d : κ → ι → ℂ × P → ℂ} (hd : ∀ i j, DifferentiableOn ℂ (d i j) O)
    (hKO : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' O) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ)
    (hwO : ∀ z ∈ K', (w, z) ∈ O) :
    sliceMat hρ (restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKO (swapMat d)
      (differentiableOn_swapMat hd)) w = fun i j => restrictParam K' (hd i j) w := by
  funext i j
  apply Subtype.ext; apply ContinuousMap.ext; intro z
  rw [restrictParam_apply K' (hd i j) hwO z]
  exact sliceB_apply hρ _ hw z

variable (K') in
/-- The `B(K')`-operator `D(w)` of the slice `d(w, ·)` of a holomorphic matrix. -/
def fibreOp {κ ι : Type*} [Fintype ι] {O : Set (ℂ × P)} {d : κ → ι → ℂ × P → ℂ}
    (hd : ∀ i j, DifferentiableOn ℂ (d i j) O) (w : ℂ) :
    (ι → holSubalgebra K') →L[ℂ] (κ → holSubalgebra K') :=
  matrixOperator (fun i j => restrictParam K' (hd i j) w)

omit [CompactSpace K'] [FiniteDimensional ℂ P] in
theorem restrictParam_comp {κ ι μ : Type*} [Fintype ι] {O : Set (ℂ × P)}
    {d₂ : ι → μ → ℂ × P → ℂ} {d₁ : κ → ι → ℂ × P → ℂ} (hd₂ : ∀ j k, DifferentiableOn ℂ (d₂ j k) O)
    (hd₁ : ∀ i j, DifferentiableOn ℂ (d₁ i j) O) (hcomp : ∀ i k, ∀ q ∈ O, ∑ j, d₁ i j q * d₂ j k q = 0)
    {w : ℂ} (hwO : ∀ z ∈ K', (w, z) ∈ O) (i : κ) (k : μ) :
    ∑ j, restrictParam K' (hd₁ i j) w * restrictParam K' (hd₂ j k) w = 0 := by
  apply Subtype.ext; apply ContinuousMap.ext; intro z
  have h := hcomp i k (w, z) (hwO z z.2)
  simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.mul_apply, ZeroMemClass.coe_zero, ContinuousMap.zero_apply]
  simp only [restrictParam_apply K' _ hwO]
  exact h

/-- **Douady 1966, §7 Prop. 6 (a), for a start of a resolution.** Let `d₂`, `d₁` be holomorphic
matrices on an open `O ⊆ ℂ × P` containing `{w} × K'` for `w` near `0`, with `d₁ d₂ = 0`, and let
`D_i(w)` be the `B(K')`-operators of the slices `d_i(w, ·)`. If `D₂(w)` has generalized inverses
`R₂(w)` holomorphic near `0`, and at `w = 0` the `B(K')`-complex is exact at `L₁` with `D₁(0)`
direct, then there is `ρ₀ > 0` such that for every `0 < ρ < ρ₀` the restrictions of `d₂`, `d₁` to
`K' × D̄(0,ρ)` form a `DirectExact` start over `B(K' × D̄(0,ρ))`. -/
theorem eventually_directExact_polydisc (hK' : K' ⊆ closure (interior K')) {O : Set (ℂ × P)}
    (hOo : IsOpen O) (hO : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ z ∈ K', (w, z) ∈ O)
    {d₂ : ι₁ → ι₂ → ℂ × P → ℂ} {d₁ : ι₀ → ι₁ → ℂ × P → ℂ}
    (hd₂ : ∀ j k, DifferentiableOn ℂ (d₂ j k) O) (hd₁ : ∀ i j, DifferentiableOn ℂ (d₁ i j) O)
    (hcomp : ∀ i k, ∀ q ∈ O, ∑ j, d₁ i j q * d₂ j k q = 0)
    {R₂ : ℂ → (ι₁ → holSubalgebra K') →L[ℂ] (ι₂ → holSubalgebra K')}
    (hR₂d : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ R₂ w)
    (hR₂ : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ x, fibreOp K' hd₂ w (R₂ w (fibreOp K' hd₂ w x)) = fibreOp K' hd₂ w x)
    (hex₀ : ∀ x, fibreOp K' hd₁ 0 x = 0 → ∃ u, fibreOp K' hd₂ 0 u = x)
    (hker₀ : (LinearMap.ker (fibreOp K' hd₁ 0 :
      (ι₁ → holSubalgebra K') →ₗ[ℂ] (ι₀ → holSubalgebra K'))).ClosedComplemented)
    (hran₀ : (LinearMap.range (fibreOp K' hd₁ 0 :
      (ι₁ → holSubalgebra K') →ₗ[ℂ] (ι₀ → holSubalgebra K'))).ClosedComplemented) :
    ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∃ hKO : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' O,
      ∀ [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)],
        DirectExact (restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKO (swapMat d₂)
            (differentiableOn_swapMat hd₂))
          (restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKO (swapMat d₁)
            (differentiableOn_swapMat hd₁)) := by
  obtain ⟨S₀, hS₀⟩ := exists_generalizedInverse (fibreOp K' hd₁ 0) hker₀ hran₀
  have hD₂d : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fibreOp K' hd₂) w := by
    filter_upwards [eventually_eventually_nhds.2 hO] with w hw
    exact differentiableAt_matrixOperator_restrictParam K' hOo hd₂ hw.self_of_nhds
  have hD₁d : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fibreOp K' hd₁) w := by
    filter_upwards [eventually_eventually_nhds.2 hO] with w hw
    exact differentiableAt_matrixOperator_restrictParam K' hOo hd₁ hw.self_of_nhds
  have hcompD : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ u, fibreOp K' hd₁ w (fibreOp K' hd₂ w u) = 0 := by
    filter_upwards [hO] with w hw u
    exact matrixOperator_comp_apply (fun j k => restrictParam K' (hd₂ j k) w)
      (fun i j => restrictParam K' (hd₁ i j) w) (restrictParam_comp hd₂ hd₁ hcomp hw) u
  have hstep := eventually_step_holomorphic (d₂ := fibreOp K' hd₂) (d₁ := fibreOp K' hd₁) hD₁d hD₂d
    hR₂d hR₂ hcompD hex₀ hS₀
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hstep.and (hO.and (hR₂d.and hR₂)))
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ => ?_⟩
  have hwO : ∀ w ∈ closedBall (0 : ℂ) ρ, ∀ z ∈ K', (w, z) ∈ O := fun w hw =>
    (hball w (closedBall_subset_ball hρρ₀ hw)).2.1
  have hKO : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' O := fun q hq =>
    hwO q.2 (Set.mem_prod.mp hq).2 q.1 (Set.mem_prod.mp hq).1
  refine ⟨hKO, fun {_} => ?_⟩
  have hR₂' : DifferentiableOn ℂ R₂ (ball 0 ρ₀) := fun w hw =>
    (hball w hw).2.2.1.differentiableWithinAt
  have hR₁' : DifferentiableOn ℂ (stepInvFam (fibreOp K' hd₂) R₂ (fibreOp K' hd₁) 0 S₀)
      (ball 0 ρ₀) := fun w hw => (hball w hw).1.1.differentiableWithinAt
  refine directExact_of_slices hK' hρ hρρ₀ (restrictMatrix_comp _ _ _ _ fun i k q hq =>
      hcomp i k (q.2, q.1) hq) hR₂' hR₁' (fun w hw x => ?_) (fun w hw x => ?_) (fun w hw x hx => ?_)
  · rw [sliceMat_restrictMatrix hρ hd₂ hKO hw (hwO w hw)]
    exact (hball w (closedBall_subset_ball hρρ₀ hw)).2.2.2 x
  · rw [sliceMat_restrictMatrix hρ hd₁ hKO hw (hwO w hw)]
    exact (hball w (closedBall_subset_ball hρρ₀ hw)).1.2.2 x
  · rw [sliceMat_restrictMatrix hρ hd₁ hKO hw (hwO w hw)] at hx
    rw [sliceMat_restrictMatrix hρ hd₂ hKO hw (hwO w hw)]
    exact (hball w (closedBall_subset_ball hρρ₀ hw)).1.2.1 x hx

end Assembly

end
end Hironaka.HironakaG10FlatFlatFamilyPrivilege
