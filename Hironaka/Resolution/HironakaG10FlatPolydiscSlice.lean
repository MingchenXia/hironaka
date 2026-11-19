import Hironaka.Resolution.HironakaG10FlatPolydiscFibre

/-! # `B(K' × D̄(0,ρ)) = B(D̄(0,ρ); B(K'))`: slices and gluing

Douady 1966, §7 n° 3 (proof of Prop. 6) and §8 use `B(K' × K'') = B(K''; B(K'))` for Banach-valued
`B`. For `K = K' × D̄(0,ρ)` (`ρ > 0`, `K'` compact) this module proves both directions in the form
needed to transfer fibrewise statements over the disc to `B(K)`:

* `evalB`: evaluation at a point of `K'`, a continuous linear functional on `B(K')`;
  `evalB_circleIntegral`: it commutes with circle integrals.
* **Slices** `sliceB hρ f w ∈ B(K')`, `z ↦ f(z,w)` (`differentiableOn_sliceFun`: holomorphic on
  `interior K'` for EVERY `w` of the closed disc — on the boundary circle as a uniform limit);
  `sliceL hρ w : B(K) →L B(K')` (norm `≤ 1`), `sliceB_mul`;
  `continuousOn_sliceB` (on the closed disc, uniform continuity) and **`differentiableOn_sliceB`**:
  if `K' ⊆ closure (interior K')`, `w ↦ f(·,w)` is a HOLOMORPHIC `B(K')`-valued map on `D(0,ρ)`
  (Banach-valued Cauchy integral, evaluated pointwise with `differentiableOn_fibre`).
* **Gluing** `glueB`: a `B(K')`-valued map `G`, continuous on `D̄(0,ρ)` and holomorphic on `D(0,ρ)`,
  defines `(z,w) ↦ G(w)(z)` in `B(K)` (`differentiableOn_glueFun`: joint holomorphy from the power
  series of `G` with coefficients in `B(K')`, uniform limits of partial sums); `glueB_apply`,
  `sliceB_glueB`, `norm_glueB_le`.
BP: hironaka-g10-flat-polydisc-slice.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real NNReal ENNReal
namespace Hironaka.HironakaG10FlatPolydiscSlice
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscFibre

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-! ## Evaluation functionals -/

/-- Evaluation at a point of `K'`, as a continuous linear functional on `B(K')`. -/
def evalB (K' : Set P) [CompactSpace K'] (z : K') : holSubalgebra K' →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => (f : C(K', ℂ)) z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    1 fun f => by
      rw [one_mul, norm_holSubalgebra]
      exact (f : C(K', ℂ)).norm_coe_le_norm z

theorem evalB_apply (K' : Set P) [CompactSpace K'] (z : K') (f : holSubalgebra K') :
    evalB K' z f = (f : C(K', ℂ)) z := rfl

/-- Evaluation commutes with circle integrals. -/
theorem evalB_circleIntegral (K' : Set P) [CompactSpace K'] (z : K') {g : ℂ → holSubalgebra K'}
    {c : ℂ} {R : ℝ} (hg : CircleIntegrable g c R) :
    evalB K' z (∮ ζ in C(c, R), g ζ) = ∮ ζ in C(c, R), evalB K' z (g ζ) := by
  unfold circleIntegral
  rw [← (evalB K' z).intervalIntegral_comp_comm hg.out]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  exact (evalB K' z).map_smul _ _

/-! ## Slices -/

variable {K' : Set P} [CompactSpace K'] {ρ : ℝ} [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]

omit [NormedSpace ℂ P] [CompactSpace K'] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
theorem continuous_sliceFun (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (w : ℂ) :
    Continuous fun z : K' => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) f (z.1, w) := by
  by_cases hw : w ∈ closedBall (0 : ℂ) ρ
  · have h : (fun z : K' => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) f (z.1, w)) =
        fun z => f ⟨(z.1, w), z.2, hw⟩ := funext fun z => extendZero_of_mem _ _ _
    rw [h]
    exact f.continuous.comp ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
  · have h : (fun z : K' => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) f (z.1, w)) = fun _ => 0 :=
      funext fun z => dif_neg fun h => hw h.2
    rw [h]
    exact continuous_const

omit [CompactSpace K'] in
/-- **Every slice is holomorphic on `interior K'`** (also on the boundary circle). -/
theorem differentiableOn_sliceFun (hρ : 0 < ρ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (w : ℂ) : DifferentiableOn ℂ (fun z => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
      (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (z, w)) (interior K') := by
  by_cases hw : w ∈ closedBall (0 : ℂ) ρ
  · have hf : DifferentiableOn ℂ (extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
        (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))) (interior K' ×ˢ ball (0 : ℂ) ρ) := by
      have h0 := mem_holSubalgebra.mp f.2
      rwa [interior_prod_closedBall K' hρ] at h0
    have hcl : w ∈ closure (ball (0 : ℂ) ρ) := by rwa [closure_ball _ hρ.ne']
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
    have hunif : UniformContinuous (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) :=
      CompactSpace.uniformContinuous_of_continuous (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)).continuous
    intro z₀ hz₀
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z₀ hz₀
    refine DifferentiableAt.differentiableWithinAt ?_
    refine Hironaka.differentiableAt_of_tendstoUniformlyOn_ball
      (g := fun n z => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
        (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (z, u n)) hr
      (Eventually.of_forall fun n => hf.comp (differentiableOn_id.prodMk
        (differentiableOn_const (u n))) fun z hz => ⟨hball hz, hu n⟩) ?_
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hunif ε hε
    filter_upwards [Metric.tendsto_nhds.mp hlim δ hδ] with n hn
    intro z hz
    have hzK : z ∈ K' := interior_subset (hball hz)
    have h₁ : (z, w) ∈ K' ×ˢ closedBall (0 : ℂ) ρ := ⟨hzK, hw⟩
    have h₂ : (z, u n) ∈ K' ×ˢ closedBall (0 : ℂ) ρ := ⟨hzK, ball_subset_closedBall (hu n)⟩
    rw [extendZero_of_mem _ _ h₁, extendZero_of_mem _ _ h₂]
    refine hδf ?_
    change dist (z, w) (z, u n) < δ
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_comm]
    exact hn
  · refine (differentiableOn_const (0 : ℂ)).congr fun z _ => ?_
    exact dif_neg fun h => hw h.2

/-- **The slice `z ↦ f(z,w)` as an element of `B(K')`** (`0` off the closed disc). -/
def sliceB (hρ : 0 < ρ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (w : ℂ) :
    holSubalgebra K' :=
  ⟨⟨fun z => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))
      (z.1, w), continuous_sliceFun _ w⟩,
    (differentiableOn_sliceFun hρ f w).congr fun z hz => by
      rw [extendZero_of_mem K' _ (interior_subset hz)]
      rfl⟩

omit [NormedSpace ℂ P] [CompactSpace K'] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
theorem extendZero_slice (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (z : K') {w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) ρ) :
    extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) f (z.1, w) = f ⟨(z.1, w), z.2, hw⟩ :=
  extendZero_of_mem _ _ _

omit [NormedSpace ℂ P] [CompactSpace K'] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
theorem extendZero_slice_of_not_mem (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (z : P) {w : ℂ}
    (hw : w ∉ closedBall (0 : ℂ) ρ) : extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) f (z, w) = 0 :=
  dif_neg fun h => hw h.2

omit [CompactSpace K'] in
theorem sliceB_apply (hρ : 0 < ρ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) ρ) (z : K') :
    ((sliceB hρ f w : holSubalgebra K') : C(K', ℂ)) z =
      (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) ⟨(z.1, w), z.2, hw⟩ :=
  extendZero_of_mem _ _ _

omit [CompactSpace K'] in
theorem sliceB_add (hρ : 0 < ρ) (f g : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (w : ℂ) :
    sliceB hρ (f + g) w = sliceB hρ f w + sliceB hρ g w := by
  apply Subtype.ext; apply ContinuousMap.ext; intro z
  by_cases hw : w ∈ closedBall (0 : ℂ) ρ
  · show extendZero _ _ _ = extendZero _ _ _ + extendZero _ _ _
    rw [extendZero_slice _ z hw, extendZero_slice _ z hw, extendZero_slice _ z hw]
    rfl
  · show extendZero _ _ _ = extendZero _ _ _ + extendZero _ _ _
    rw [extendZero_slice_of_not_mem _ _ hw, extendZero_slice_of_not_mem _ _ hw,
      extendZero_slice_of_not_mem _ _ hw, add_zero]

omit [CompactSpace K'] in
theorem sliceB_smul (hρ : 0 < ρ) (c : ℂ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (w : ℂ) :
    sliceB hρ (c • f) w = c • sliceB hρ f w := by
  apply Subtype.ext; apply ContinuousMap.ext; intro z
  by_cases hw : w ∈ closedBall (0 : ℂ) ρ
  · show extendZero _ _ _ = c • extendZero _ _ _
    rw [extendZero_slice _ z hw, extendZero_slice _ z hw]
    rfl
  · show extendZero _ _ _ = c • extendZero _ _ _
    rw [extendZero_slice_of_not_mem _ _ hw, extendZero_slice_of_not_mem _ _ hw, smul_zero]

omit [CompactSpace K'] in
theorem sliceB_mul (hρ : 0 < ρ) (f g : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) ρ) : sliceB hρ (f * g) w = sliceB hρ f w * sliceB hρ g w := by
  apply Subtype.ext; apply ContinuousMap.ext; intro z
  show extendZero _ ((f * g : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) _ = extendZero _ _ _ * extendZero _ _ _
  rw [extendZero_slice _ z hw, extendZero_slice _ z hw, extendZero_slice _ z hw]
  rfl

theorem norm_sliceB_le (hρ : 0 < ρ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (w : ℂ) :
    ‖sliceB hρ f w‖ ≤ ‖f‖ := by
  rw [norm_holSubalgebra, norm_holSubalgebra, ContinuousMap.norm_le _ (norm_nonneg _)]
  intro z
  by_cases hw : w ∈ closedBall (0 : ℂ) ρ
  · rw [sliceB_apply hρ f hw]
    exact (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)).norm_coe_le_norm _
  · show ‖extendZero _ _ _‖ ≤ _
    rw [extendZero_slice_of_not_mem _ _ hw, norm_zero]
    exact norm_nonneg _

/-- The slice at `w`, as a continuous linear map `B(K) → B(K')` of norm `≤ 1`. -/
def sliceL (hρ : 0 < ρ) (w : ℂ) : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) →L[ℂ] holSubalgebra K' :=
  LinearMap.mkContinuous
    { toFun := fun f => sliceB hρ f w, map_add' := fun f g => sliceB_add hρ f g w,
      map_smul' := fun c f => sliceB_smul hρ c f w } 1
    fun f => by rw [one_mul]; exact norm_sliceB_le hρ f w

theorem sliceL_apply (hρ : 0 < ρ) (w : ℂ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    sliceL hρ w f = sliceB hρ f w := rfl

/-- **The slices depend continuously on `w ∈ D̄(0,ρ)`** in the sup norm. -/
theorem continuousOn_sliceB (hρ : 0 < ρ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    ContinuousOn (sliceB hρ f) (closedBall (0 : ℂ) ρ) := by
  have hunif : UniformContinuous (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) :=
    CompactSpace.uniformContinuous_of_continuous (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)).continuous
  intro w₀ hw₀
  refine (Metric.continuousWithinAt_iff (f := sliceB hρ f)).2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hunif (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun w hw hdist => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [norm_holSubalgebra, ContinuousMap.norm_le _ (half_pos hε).le]
  intro z
  show ‖extendZero _ _ (z.1, w) - extendZero _ _ (z.1, w₀)‖ ≤ ε / 2
  rw [extendZero_slice _ z hw, extendZero_slice _ z hw₀, ← dist_eq_norm]
  refine (hδf ?_).le
  change dist (z.1, w) (z.1, w₀) < δ
  rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  exact hdist

/-- **`w ↦ f(·,w)` is a holomorphic `B(K')`-valued map on `D(0,ρ)`** (needs
`K' ⊆ closure (interior K')`, e.g. a polydisc). -/
theorem differentiableOn_sliceB (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    DifferentiableOn ℂ (sliceB hρ f) (ball (0 : ℂ) ρ) := by
  intro w₀ hw₀
  rw [mem_ball_zero_iff] at hw₀
  obtain ⟨r, hr₀, hrρ⟩ := exists_between hw₀
  have hr : 0 < r := (norm_nonneg w₀).trans_lt hr₀
  lift r to ℝ≥0 using hr.le
  set H : ℂ → holSubalgebra K' := fun w =>
    (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, (r : ℝ)), (ζ - w)⁻¹ • sliceB hρ f ζ with hH
  have hint : CircleIntegrable (sliceB hρ f) 0 r :=
    ((continuousOn_sliceB hρ f).mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall hrρ.le))).circleIntegrable hr.le
  have hps := hasFPowerSeriesOn_cauchy_integral hint (by exact_mod_cast hr)
  -- `H` agrees with the slices on `D(0,r)`
  have heq : ∀ w ∈ ball (0 : ℂ) r, H w = sliceB hρ f w := by
    intro w hw
    apply Subtype.ext; apply ContinuousMap.ext; intro z
    have hwρ : w ∈ closedBall (0 : ℂ) ρ :=
      ball_subset_closedBall (ball_subset_ball hrρ.le hw)
    change evalB K' z (H w) = evalB K' z (sliceB hρ f w)
    rw [evalB_apply K' z (sliceB hρ f w), sliceB_apply hρ f hwρ, hH, map_smul,
      evalB_circleIntegral]
    swap
    · refine ContinuousOn.circleIntegrable hr.le ?_
      refine ContinuousOn.smul (f := fun ζ : ℂ => (ζ - w)⁻¹) (g := sliceB hρ f) ?_
        ((continuousOn_sliceB hρ f).mono (sphere_subset_closedBall.trans
        (closedBall_subset_closedBall hrρ.le)))
      refine (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => sub_ne_zero.mpr ?_
      rintro rfl
      rw [mem_sphere_zero_iff_norm] at hζ
      have h' : ‖ζ‖ < (r : ℝ) := mem_ball_zero_iff.mp hw
      rw [hζ] at h'
      exact lt_irrefl _ h'
    -- the scalar Cauchy formula for the fibre `ζ ↦ f(z,ζ)`
    have hfib := differentiableOn_fibre hK' hρ f z.2
    have hd : DifferentiableOn ℂ (fun ζ : ℂ => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
        (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (z.1, ζ)) (closedBall (0 : ℂ) r) :=
      hfib.mono (closedBall_subset_ball hrρ)
    have hC := hd.circleIntegral_sub_inv_smul hw
    have hfun : (fun ζ => evalB K' z ((ζ - w)⁻¹ • sliceB hρ f ζ)) =
        fun ζ => (ζ - w)⁻¹ • extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
          (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (z.1, ζ) := by
      funext ζ
      rw [map_smul]
      rfl
    rw [hfun, hC, smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_smul,
      extendZero_slice _ z hwρ]
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) r) := by
    intro w hw
    refine (hps.analyticAt_of_mem ?_).differentiableAt.differentiableWithinAt
    rw [Metric.eball_coe]
    exact hw
  have hw₀r : w₀ ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hr₀
  refine ((hHd.differentiableAt (isOpen_ball.mem_nhds hw₀r)).congr_of_eventuallyEq ?_)
    |>.differentiableWithinAt
  filter_upwards [isOpen_ball.mem_nhds hw₀r] with w hw
  exact (heq w hw).symm

/-! ## Gluing a holomorphic `B(K')`-valued map -/

omit [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
theorem norm_evalB_le (z : K') (f : holSubalgebra K') : ‖evalB K' z f‖ ≤ ‖f‖ := by
  rw [evalB_apply, norm_holSubalgebra]
  exact (f : C(K', ℂ)).norm_coe_le_norm z

/-- The glued function `(z, w) ↦ G(w)(z)` on `K' × D̄(0,ρ)`. -/
def glueFun (G : ℂ → holSubalgebra K') (q : K' ×ˢ closedBall (0 : ℂ) ρ) : ℂ :=
  (G q.1.2 : C(K', ℂ)) ⟨q.1.1, q.2.1⟩

omit [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
theorem continuous_glueFun {G : ℂ → holSubalgebra K'} (hG : ContinuousOn G (closedBall (0 : ℂ) ρ)) :
    Continuous (glueFun (ρ := ρ) G) := by
  have h1 : Continuous fun q : K' ×ˢ closedBall (0 : ℂ) ρ => (G q.1.2 : C(K', ℂ)) :=
    continuous_subtype_val.comp (hG.comp_continuous (continuous_snd.comp continuous_subtype_val)
      fun q => q.2.2)
  have h2 : Continuous fun q : K' ×ˢ closedBall (0 : ℂ) ρ => (⟨q.1.1, q.2.1⟩ : K') :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  exact continuous_eval.comp (h1.prodMk h2)

omit [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
/-- **Joint holomorphy of a glued map** on `interior K' × D(0,ρ)`: the partial sums of the power
series of `G` (coefficients in `B(K')`) converge uniformly. -/
theorem differentiableOn_glueFun {G : ℂ → holSubalgebra K'} (hG' : DifferentiableOn ℂ G (ball 0 ρ)) :
    DifferentiableOn ℂ (fun q : P × ℂ => extendZero K' (G q.2 : C(K', ℂ)) q.1)
      (interior K' ×ˢ ball (0 : ℂ) ρ) := by
  rintro ⟨z₀, w₀⟩ ⟨hz₀, hw₀⟩
  obtain ⟨p, R, hp⟩ := hG'.analyticAt (isOpen_ball.mem_nhds hw₀)
  obtain ⟨r', hr'0, hr'R⟩ : ∃ r' : ℝ≥0, 0 < r' ∧ (r' : ℝ≥0∞) < R := by
    obtain ⟨r', hr'0, hr'R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
    exact ⟨r', by exact_mod_cast hr'0, hr'R⟩
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.mp isOpen_interior z₀ hz₀
  set ε : ℝ := min δ r' with hε
  have hε0 : 0 < ε := lt_min hδ (by exact_mod_cast hr'0)
  have hball : ∀ q ∈ ball (z₀, w₀) ε, q.1 ∈ interior K' ∧ q.2 - w₀ ∈ ball (0 : ℂ) r' := by
    intro q hq
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq
    refine ⟨hδK (lt_of_lt_of_le hq.1 (min_le_left _ _)), ?_⟩
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    exact lt_of_lt_of_le hq.2 (min_le_right _ _)
  refine DifferentiableAt.differentiableWithinAt ?_
  refine Hironaka.differentiableAt_of_tendstoUniformlyOn_ball
    (g := fun n q => ∑ k ∈ Finset.range n, (q.2 - w₀) ^ k *
      extendZero K' (p.coeff k : C(K', ℂ)) q.1) hε0 (Eventually.of_forall fun n => ?_) ?_
  · -- the partial sums are holomorphic
    refine DifferentiableOn.fun_sum fun k _ => ?_
    refine ((differentiableOn_snd.sub (differentiableOn_const w₀)).pow k).mul ?_
    refine ((p.coeff k).2.comp differentiableOn_fst fun q hq => (hball q hq).1)
  · -- uniform convergence
    have hu := hp.tendstoUniformlyOn hr'R
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro η hη
    filter_upwards [hu η hη] with n hn
    intro q hq
    obtain ⟨hq1, hq2⟩ := hball q hq
    have hzK : q.1 ∈ K' := interior_subset hq1
    have key := hn _ hq2
    rw [add_sub_cancel] at key
    rw [extendZero_of_mem K' _ hzK]
    have hsum : ∑ k ∈ Finset.range n, (q.2 - w₀) ^ k * extendZero K' (p.coeff k : C(K', ℂ)) q.1 =
        evalB K' ⟨q.1, hzK⟩ (p.partialSum n (q.2 - w₀)) := by
      rw [FormalMultilinearSeries.partialSum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, map_smul, extendZero_of_mem K' _ hzK,
        smul_eq_mul]
      rfl
    rw [hsum, dist_eq_norm]
    show ‖evalB K' ⟨q.1, hzK⟩ (G q.2) - evalB K' ⟨q.1, hzK⟩ (p.partialSum n (q.2 - w₀))‖ < η
    rw [← map_sub]
    exact lt_of_le_of_lt (norm_evalB_le _ _) (by rw [← dist_eq_norm]; exact key)

/-- **The glued element of `B(K' × D̄(0,ρ))`.** -/
def glueB (hρ : 0 < ρ) {G : ℂ → holSubalgebra K'} (hG : ContinuousOn G (closedBall (0 : ℂ) ρ))
    (hG' : DifferentiableOn ℂ G (ball 0 ρ)) : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  ⟨⟨glueFun G, continuous_glueFun hG⟩, by
    rw [mem_holSubalgebra, interior_prod_closedBall K' hρ]
    refine (differentiableOn_glueFun hG').congr fun q hq => ?_
    have hqK : q ∈ K' ×ˢ closedBall (0 : ℂ) ρ := ⟨interior_subset hq.1, ball_subset_closedBall hq.2⟩
    rw [extendZero_of_mem _ _ hqK, extendZero_of_mem K' _ (interior_subset hq.1)]
    rfl⟩

omit [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
theorem glueB_apply (hρ : 0 < ρ) {G : ℂ → holSubalgebra K'}
    (hG : ContinuousOn G (closedBall (0 : ℂ) ρ)) (hG' : DifferentiableOn ℂ G (ball 0 ρ))
    (q : K' ×ˢ closedBall (0 : ℂ) ρ) :
    ((glueB hρ hG hG' : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
      C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) q = (G q.1.2 : C(K', ℂ)) ⟨q.1.1, q.2.1⟩ := rfl

/-- Slices of a glued element. -/
theorem sliceB_glueB (hρ : 0 < ρ) {G : ℂ → holSubalgebra K'}
    (hG : ContinuousOn G (closedBall (0 : ℂ) ρ)) (hG' : DifferentiableOn ℂ G (ball 0 ρ)) {w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) ρ) : sliceB hρ (glueB hρ hG hG') w = G w := by
  apply Subtype.ext; apply ContinuousMap.ext; intro z
  rw [sliceB_apply hρ _ hw, glueB_apply]

/-- Gluing the slices gives back the element. -/
theorem glueB_sliceB (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) :
    glueB hρ (continuousOn_sliceB hρ f) (differentiableOn_sliceB hK' hρ f) = f := by
  apply Subtype.ext; apply ContinuousMap.ext; intro q
  rw [glueB_apply, sliceB_apply hρ f q.2.2]

/-- The sup norm of a glued element. -/
theorem norm_glueB_le (hρ : 0 < ρ) {G : ℂ → holSubalgebra K'}
    (hG : ContinuousOn G (closedBall (0 : ℂ) ρ)) (hG' : DifferentiableOn ℂ G (ball 0 ρ)) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ w ∈ closedBall (0 : ℂ) ρ, ‖G w‖ ≤ C) : ‖glueB hρ hG hG'‖ ≤ C := by
  rw [norm_holSubalgebra, ContinuousMap.norm_le _ hC0]
  intro q
  rw [glueB_apply]
  exact ((G q.1.2 : C(K', ℂ)).norm_coe_le_norm _).trans
    ((norm_holSubalgebra K' (G q.1.2)).symm ▸ hC _ q.2.2)

end
end Hironaka.HironakaG10FlatPolydiscSlice
