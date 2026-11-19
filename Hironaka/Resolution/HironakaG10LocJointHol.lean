import Hironaka.Resolution.HironakaG10LocSheafExact
import Hironaka.Resolution.HironakaG10FlatPolydiscSlice

/-! # Holomorphic families in `B(K)`: restrictions of holomorphic functions, joint holomorphy

Douady 1966, §5 n° 2 and §8 (a holomorphic section over `S` of the trivial bundle with fibre `B(K)`
defines a holomorphic function on `S × K̊`, and conversely) and Frisch 1968 Lemme 3 (i) ("celle-ci
donne naissance ([1], §5, n° 2) à un complexe de faisceaux sur `V × K̊`"), in the two directions used:

* `norm_bk_sub_le` (Cauchy–Lipschitz estimate): for `g ∈ B(K)` and `B(x₀, 2r) ⊆ K̊`,
  `|g(x) − g(x₀)| ≤ 2‖g‖/r · ‖x − x₀‖` on `B(x₀, r)`.
* **`differentiableAt_bkEval`**: evaluation `(b, x) ↦ b(x)` is complex differentiable on
  `B(K) × K̊` (jointly); `differentiableAt_bkEval_comp`: for `c : S → B(K)` holomorphic at `t₀`,
  `(t, x) ↦ c(t)(x)` is holomorphic at `(t₀, x₀)`, `x₀ ∈ K̊`.
* **`differentiableAt_fibRestrict`**: for `f` holomorphic on `V × U` (`S`, `X` finite dimensional,
  `K ⊆ U` compact), `s ↦ f(s,·)|_K` is a holomorphic `B(K)`-valued map on `V` (second-order Cauchy
  estimates, uniform on the compact `{s₀} × K`).
BP: hironaka-g10-loc-joint-hol.tex. -/
set_option autoImplicit false
open Set Filter Metric Asymptotics
open scoped Topology
namespace Hironaka.HironakaG10LocJointHol
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10LocSheafExact Hironaka

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Elements of `B(K)` are bounded by their norm on `K`. -/
theorem norm_extendZero_le {K : Set X} [CompactSpace K] (g : holSubalgebra K) (v : X) :
    ‖extendZero K ((g : holSubalgebra K) : C(K, ℂ)) v‖ ≤ ‖g‖ := by
  by_cases hv : v ∈ K
  · rw [extendZero_of_mem K _ hv, norm_holSubalgebra]
    exact (g : C(K, ℂ)).norm_coe_le_norm ⟨v, hv⟩
  · rw [show extendZero K ((g : holSubalgebra K) : C(K, ℂ)) v = 0 from dif_neg hv, norm_zero]
    exact norm_nonneg _

/-- **Cauchy–Lipschitz estimate in `B(K)`** at an interior point. -/
theorem norm_bk_sub_le {K : Set X} [CompactSpace K] (g : holSubalgebra K) {x₀ : X} {r : ℝ}
    (hr : 0 < r) (hball : ball x₀ (2 * r) ⊆ interior K) {x : X} (hx : x ∈ ball x₀ r) :
    ‖extendZero K ((g : holSubalgebra K) : C(K, ℂ)) x -
      extendZero K ((g : holSubalgebra K) : C(K, ℂ)) x₀‖ ≤ 2 * ‖g‖ / r * ‖x - x₀‖ := by
  set φ : X → ℂ := extendZero K ((g : holSubalgebra K) : C(K, ℂ)) with hφ
  have hφd : DifferentiableOn ℂ φ (interior K) := g.2
  have hsub : ∀ w ∈ ball x₀ r, ball w r ⊆ interior K := by
    intro w hw y hy
    apply hball
    rw [mem_ball] at hw hy ⊢
    linarith [dist_triangle y w x₀]
  have hdiff : ∀ y ∈ ball x₀ r, DifferentiableAt ℂ φ y := fun y hy =>
    hφd.differentiableAt (isOpen_interior.mem_nhds (hsub y hy (mem_ball_self hr)))
  have hbound : ∀ y ∈ ball x₀ r, ‖fderiv ℂ φ y‖ ≤ 2 * ‖g‖ / r := by
    intro y hy
    have h := _root_.Hironaka.norm_fderiv_le_of_forall_norm_le (hφd.mono (hsub y hy))
      (fun w _ => norm_extendZero_le g w) (half_pos hr) (half_lt_self hr)
    calc ‖fderiv ℂ φ y‖ ≤ ‖g‖ / (r / 2) := h
      _ = 2 * ‖g‖ / r := by rw [div_div_eq_mul_div, mul_comm]
  exact (convex_ball x₀ r).norm_image_sub_le_of_norm_fderiv_le hdiff hbound (mem_ball_self hr) hx

/-- **Joint differentiability of evaluation** `(b, x) ↦ b(x)` on `B(K) × K̊`. -/
theorem differentiableAt_bkEval {K : Set X} [CompactSpace K] (b₀ : holSubalgebra K) {x₀ : X}
    (hx₀ : x₀ ∈ interior K) :
    DifferentiableAt ℂ (fun q : holSubalgebra K × X =>
      extendZero K ((q.1 : holSubalgebra K) : C(K, ℂ)) q.2) (b₀, x₀) := by
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  set r := r₂ / 2 with hr
  have hr0 : 0 < r := half_pos hr₂
  have hball : ball x₀ (2 * r) ⊆ interior K := by
    rw [hr, mul_div_cancel₀ _ two_ne_zero]; exact hball₂
  have hx₀K : x₀ ∈ K := interior_subset hx₀
  -- the three pieces
  set Θ : holSubalgebra K × X → ℂ := fun q =>
    extendZero K (((q.1 - b₀ : holSubalgebra K)) : C(K, ℂ)) q.2 -
      extendZero K (((q.1 - b₀ : holSubalgebra K)) : C(K, ℂ)) x₀ with hΘ
  have hsplit : (fun q : holSubalgebra K × X =>
      extendZero K ((q.1 : holSubalgebra K) : C(K, ℂ)) q.2) = fun q =>
      Θ q + (HironakaG10FlatPolydiscSlice.evalB K ⟨x₀, hx₀K⟩) (q.1 - b₀) +
        extendZero K ((b₀ : holSubalgebra K) : C(K, ℂ)) q.2 := by
    funext q
    rw [hΘ, HironakaG10FlatPolydiscSlice.evalB_apply]
    simp only [extendZero_of_mem K _ hx₀K]
    by_cases hq : q.2 ∈ K
    · simp only [extendZero_of_mem K _ hq, AddSubgroupClass.coe_sub, ContinuousMap.sub_apply]
      ring
    · simp only [extendZero, hq, dite_false]
      ring
  rw [hsplit]
  refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) ?_
  · -- `Θ` has derivative `0`
    refine (HasFDerivAt.differentiableAt (f' := 0) ?_)
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine isLittleO_iff.2 fun c hc => ?_
    filter_upwards [Metric.ball_mem_nhds (0 : holSubalgebra K × X)
      (lt_min hr0 (show 0 < c * r / 2 by positivity))] with h hh
    rw [mem_ball, dist_zero_right, lt_min_iff] at hh
    have h1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
    have h2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
    have hx : x₀ + h.2 ∈ ball x₀ r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith
    have hb := norm_bk_sub_le h.1 hr0 hball hx
    rw [add_sub_cancel_left] at hb
    simp only [hΘ, Prod.fst_add, Prod.snd_add, add_sub_cancel_left, sub_self,
      zero_apply, sub_zero]
    calc _ ≤ 2 * ‖h.1‖ / r * ‖h.2‖ := hb
      _ ≤ 2 * ‖h‖ / r * ‖h‖ := by gcongr
      _ ≤ c * ‖h‖ := by
          have : 2 * ‖h‖ / r ≤ c := by
            rw [div_le_iff₀ hr0]; linarith
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  · exact ((HironakaG10FlatPolydiscSlice.evalB K ⟨x₀, hx₀K⟩).differentiableAt).comp _
      (differentiableAt_fst.sub_const b₀)
  · have hb₀ : DifferentiableAt ℂ (extendZero K ((b₀ : holSubalgebra K) : C(K, ℂ))) x₀ :=
      (show DifferentiableOn ℂ (extendZero K ((b₀ : holSubalgebra K) : C(K, ℂ))) (interior K)
        from b₀.2).differentiableAt (isOpen_interior.mem_nhds hx₀)
    exact hb₀.comp (b₀, x₀) (differentiableAt_snd (𝕜 := ℂ) (E := holSubalgebra K) (F := X)
      (p := (b₀, x₀)))

/-- **Joint holomorphy of a holomorphic `B(K)`-valued family**: `(t, x) ↦ c(t)(x)` is holomorphic at
`(t₀, x₀)`, `x₀ ∈ K̊`, when `c` is holomorphic at `t₀`. -/
theorem differentiableAt_bkEval_comp {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
    {K : Set X} [CompactSpace K] {c : S → holSubalgebra K} {t₀ : S} (hc : DifferentiableAt ℂ c t₀)
    {x₀ : X} (hx₀ : x₀ ∈ interior K) :
    DifferentiableAt ℂ (fun p : S × X => extendZero K ((c p.1 : holSubalgebra K) : C(K, ℂ)) p.2)
      (t₀, x₀) := by
  have hpair : DifferentiableAt ℂ (fun p : S × X => (c p.1, p.2)) (t₀, x₀) :=
    (hc.comp (t₀, x₀) (differentiableAt_fst (𝕜 := ℂ) (E := S) (F := X) (p := (t₀, x₀)))).prodMk
      (differentiableAt_snd (𝕜 := ℂ) (E := S) (F := X) (p := (t₀, x₀)))
  exact (differentiableAt_bkEval (c t₀) hx₀).comp (t₀, x₀) hpair

/-! ## Restrictions of holomorphic functions are holomorphic `B(K)`-valued maps -/

section Restrict
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]

/-- The derivative candidate `h ↦ (∂f/∂s)(s₀,·)(h)|_K` as an element of `B(K)`. -/
def fibDeriv (K : Set X) {U : Set X} (hKU : K ⊆ U) (hU : IsOpen U) {V : Set S} (hV : IsOpen V)
    (f : S × X → ℂ) (hf : DifferentiableOn ℂ f (V ×ˢ U)) {s₀ : S} (hs₀ : s₀ ∈ V) (h : S) :
    holSubalgebra K :=
  restrict K hKU (fun x => fderiv ℂ f (s₀, x) (h, 0))
    (differentiableOn_fib (differentiableOn_fderiv_apply_of_isOpen hf (hV.prod hU) (h, 0)) hs₀)

/-- **`s ↦ f(s,·)|_K` is holomorphic** (`S`, `X` finite dimensional). -/
theorem differentiableAt_fibRestrict [FiniteDimensional ℂ S] [FiniteDimensional ℂ X] (K : Set X)
    [CompactSpace K] {U : Set X} (hU : IsOpen U) (hKU : K ⊆ U) {V : Set S} (hV : IsOpen V)
    (f : S × X → ℂ) (hf : DifferentiableOn ℂ f (V ×ˢ U)) {s₀ : S} (hs₀ : s₀ ∈ V) :
    DifferentiableAt ℂ (fibRestrict K hKU f hf) s₀ := by
  -- uniform bounds near the compact `{s₀} × K`
  have hKc : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  have hC : IsCompact ({s₀} ×ˢ K : Set (S × X)) := isCompact_singleton.prod hKc
  have hCW : ({s₀} ×ˢ K : Set (S × X)) ⊆ V ×ˢ U := fun q hq => ⟨by rw [hq.1]; exact hs₀, hKU hq.2⟩
  obtain ⟨δ, hδ, hδW⟩ := hC.exists_cthickening_subset_open (hV.prod hU) hCW
  obtain ⟨M₀, hM₀⟩ := (hC.cthickening (r := δ)).exists_bound_of_continuousOn
    (hf.continuousOn.mono hδW)
  set M := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hmem : ∀ x ∈ K, ((s₀, x) : S × X) ∈ ({s₀} ×ˢ K : Set (S × X)) := fun x hx => ⟨rfl, hx⟩
  have hball : ∀ x ∈ K, ball ((s₀, x) : S × X) δ ⊆ V ×ˢ U := fun x hx =>
    ball_subset_closedBall.trans ((closedBall_subset_cthickening (hmem x hx) δ).trans hδW)
  have hbd : ∀ x ∈ K, ∀ w ∈ ball ((s₀, x) : S × X) δ, ‖f w‖ ≤ M := fun x hx w hw =>
    (hM₀ w (ball_subset_closedBall.trans (closedBall_subset_cthickening (hmem x hx) δ) hw)).trans
      (le_max_left _ _)
  -- the Cauchy bound on the derivative
  set L := M / (δ / 4) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hfd : ∀ x ∈ K, DifferentiableOn ℂ f (ball ((s₀, x) : S × X) δ) := fun x hx =>
    hf.mono (hball x hx)
  have hLb : ∀ x ∈ K, ∀ w ∈ ball ((s₀, x) : S × X) (δ / 2), ‖fderiv ℂ f w‖ ≤ L := by
    intro x hx w hw
    have hsub : ball w (δ / 2) ⊆ ball ((s₀, x) : S × X) δ := by
      refine ball_subset_ball' ?_
      rw [mem_ball] at hw
      linarith
    exact _root_.Hironaka.norm_fderiv_le_of_forall_norm_le ((hfd x hx).mono hsub)
      (fun v hv => hbd x hx v (hsub hv)) (by positivity) (by linarith)
  have hn : ∀ h : S, ‖((h, (0 : X)) : S × X)‖ = ‖h‖ := fun h => by
    rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg h)]
  -- the derivative
  let Dl : S →ₗ[ℂ] holSubalgebra K :=
    { toFun := fibDeriv K hKU hU hV f hf hs₀
      map_add' := fun h h' => by
        apply Subtype.ext
        apply ContinuousMap.ext
        intro z
        simp only [fibDeriv, HironakaG10FlatPolydiscAlgebra.restrict_apply, Subalgebra.coe_add,
          ContinuousMap.add_apply]
        rw [show ((h + h', (0 : X)) : S × X) = (h, 0) + (h', 0) by simp, map_add]
      map_smul' := fun a h => by
        apply Subtype.ext
        apply ContinuousMap.ext
        intro z
        simp only [fibDeriv, HironakaG10FlatPolydiscAlgebra.restrict_apply, RingHom.id_apply,
          Subalgebra.coe_smul, ContinuousMap.smul_apply]
        rw [show ((a • h, (0 : X)) : S × X) = a • (h, 0) by simp, map_smul] }
  have hDl : ∀ h, ‖Dl h‖ ≤ L * ‖h‖ := by
    intro h
    rw [norm_holSubalgebra, ContinuousMap.norm_le _ (by positivity)]
    intro z
    show ‖fderiv ℂ f (s₀, z) (h, 0)‖ ≤ L * ‖h‖
    calc ‖fderiv ℂ f (s₀, z) (h, 0)‖ ≤ ‖fderiv ℂ f (s₀, z)‖ * ‖((h, (0 : X)) : S × X)‖ :=
          (fderiv ℂ f (s₀, z)).le_opNorm _
      _ ≤ L * ‖h‖ := by
          rw [hn]
          exact mul_le_mul_of_nonneg_right (hLb z z.2 _ (mem_ball_self (by positivity)))
            (norm_nonneg _)
  set D : S →L[ℂ] holSubalgebra K := Dl.mkContinuous L hDl with hD
  refine (HasFDerivAt.differentiableAt (f' := D) ?_)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine isLittleO_iff.2 fun c hc => ?_
  set Q := L / (δ / 2 / 4) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hVt : Tendsto (fun h : S => s₀ + h) (𝓝 0) (𝓝 s₀) := by
    simpa using (continuous_const_add s₀).tendsto (0 : S)
  filter_upwards [Metric.ball_mem_nhds (0 : S) (lt_min (show 0 < δ / 2 / 8 by positivity)
    (show 0 < c / (Q + 1) by positivity)), hVt.eventually (hV.mem_nhds hs₀)] with h hh hhV
  rw [mem_ball, dist_zero_right, lt_min_iff] at hh
  rw [fibRestrict_of_mem K hKU f hf hhV, fibRestrict_of_mem K hKU f hf hs₀, norm_holSubalgebra,
    ContinuousMap.norm_le _ (by positivity)]
  intro z
  have ht := norm_sub_sub_fderiv_le (f := f) (z₀ := ((s₀, (z : X)) : S × X)) (by positivity)
    ((hfd z z.2).mono (ball_subset_ball (by linarith))) (hLb z z.2)
    (z := ((s₀, (z : X)) : S × X)) (u := (h, 0)) (mem_ball_self (by positivity))
    (by rw [hn]; exact hh.1)
  rw [← hQ, hn, Prod.mk_add_mk, add_zero] at ht
  have hval : ((restrict K hKU (fun x => f (s₀ + h, x)) (differentiableOn_fib hf hhV) -
      restrict K hKU (fun x => f (s₀, x)) (differentiableOn_fib hf hs₀) - D h :
        holSubalgebra K) : C(K, ℂ)) z =
      f (s₀ + h, (z : X)) - f (s₀, (z : X)) - fderiv ℂ f (s₀, (z : X)) (h, 0) := rfl
  rw [hval]
  calc _ ≤ Q * ‖h‖ * ‖h‖ := ht
    _ ≤ c * ‖h‖ := by
        have h1 : Q * ‖h‖ ≤ c := by
          calc Q * ‖h‖ ≤ (Q + 1) * (c / (Q + 1)) :=
                mul_le_mul (by linarith) hh.2.le (norm_nonneg _) (by positivity)
            _ = c := by field_simp
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end Restrict

end
end Hironaka.HironakaG10LocJointHol
